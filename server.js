// server.js – COMPLETE (STITCH + SCAN + FORCE DISTINCT L/R + QUOTA SAFE CACHE)
//
// QUOTA-FIXES:
// 1) Cache RMV location.nearbystops & departureBoard (TTL)
// 2) Scan nur wenn nötig (Positionsänderung oder Cache leer)
// 3) Refresh: wenn Stations-Cache existiert -> kein Scan, nur departures
// 4) Weniger Scan-Punkte (step hoch) + Force distinct ebenfalls moderat
//
// Voraussetzungen:
// - package.json: { "type": "module" }
// - .env: RMV_API_KEY=...
// Start: node server.js

import express from "express";
import fetch from "node-fetch";
import dotenv from "dotenv";
import path from "path";
import https from "https";
import { fileURLToPath } from "url";

dotenv.config();

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const app = express();
const PORT = process.env.PORT ? Number(process.env.PORT) : 3000;

app.use(express.json({ limit: "256kb" }));
app.use(express.static(__dirname));
app.get("/", (req, res) => res.sendFile(path.join(__dirname, "index.html")));
app.get("/api/ping", (req, res) =>
  res.json({ ok: true, t: Date.now(), quotaSafe: true })
);

// -------------------- CONFIG --------------------
const RMV_KEY = process.env.RMV_API_KEY;
const RMV_BASE = "https://www.rmv.de/hapi";

const OVERPASS_ENDPOINTS = [
  "https://overpass-api.de/api/interpreter",
  "https://overpass.kumi.systems/api/interpreter",
  "https://overpass.openstreetmap.ru/api/interpreter",
];

const LOOKAHEAD_MS = 60 * 60 * 1000;
const PASS_TIME_MS = 10_000;

// Sperr-Logik
const BASE_BUFFER_MS = 115_000;
const MIN_BUFFER_MS = 60_000;
const MAX_BUFFER_MS = 170_000;
const DELAY_BOOST_AT_MIN = 2;
const DELAY_BOOST_MS = 30_000;
const HEADWAY_TIGHT_MS = 120_000;
const HEADWAY_REDUCE_MS = 30_000;

// Travel Clamp (für sehr nahe Stops)
const MIN_TRAVEL_MS = 8_000;
const MAX_TRAVEL_MS = 25 * 60 * 1000;

// Event-Dedupe
const DEDUP_WINDOW_MS = 35_000;

// Track/stitch
const RAIL_NET_RADIUS_M = 9000;
const STITCH_TARGET_M = 16000;
const MIN_SIDE_COVERAGE_M = 2200;

// Scan entlang Track (reduziert -> weniger RMV calls)
const SCAN_MIN_M = 200;
const SCAN_MAX_M = 4200;
const SCAN_STEP_M = 500; // ✅ war 250

// Force distinct wenn L/R gleich
const FORCE_MIN_M = 900;
const FORCE_MAX_M = 9000;
const FORCE_STEP_M = 600; // ✅ war 350

// Departures Filter
const ONLY_SBAHN = true;

// ✅ Cache TTLs (Quota Safe)
const RMV_NEARBY_TTL_MS = 30 * 60 * 1000; // 30 min
const RMV_DEPS_TTL_MS = 25 * 1000;        // 25s (passt zu deinem refresh)
const STATIONS_TTL_MS = 60 * 60 * 1000;   // 1h (Stations ändern sich nicht)

// ✅ Wenn Schranke sich < X Meter bewegt -> nutze cached stations
const SAME_CROSSING_DIST_M = 60;

// -------------------- HTTP Agent --------------------
const httpsAgent = new https.Agent({ keepAlive: true });

// -------------------- generic helpers --------------------
async function fetchWithRetry(url, tries = 3) {
  let lastErr;
  for (let i = 0; i < tries; i++) {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 12_000);
    try {
      const r = await fetch(url, {
        headers: { Accept: "application/json", "User-Agent": "barbain/1.0" },
        agent: httpsAgent,
        signal: controller.signal,
      });
      clearTimeout(timeout);
      return r;
    } catch (e) {
      clearTimeout(timeout);
      lastErr = e;
      await new Promise((res) => setTimeout(res, 500 * (i + 1)));
    }
  }
  throw lastErr;
}

const toRad = (d) => (d * Math.PI) / 180;
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));

function haversineMeters(lat1, lon1, lat2, lon2) {
  const R = 6371000;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const a =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(a));
}

function polylineCumulativeMeters(points) {
  const cum = [0];
  for (let i = 1; i < points.length; i++) {
    const a = points[i - 1];
    const b = points[i];
    cum[i] = cum[i - 1] + haversineMeters(a.lat, a.lon, b.lat, b.lon);
  }
  return cum;
}

function projectToPolylineMeters(lat, lon, pts, cum) {
  let best = { sMeters: 0, distMeters: Infinity };

  const lat0 = toRad(lat);
  const cosLat = Math.cos(lat0);
  const R = 6371000;

  function toXY(p) {
    const x = toRad(p.lon - lon) * cosLat * R;
    const y = toRad(p.lat - lat) * R;
    return { x, y };
  }

  for (let i = 0; i < pts.length - 1; i++) {
    const p1 = pts[i];
    const p2 = pts[i + 1];

    const a = toXY(p1);
    const b = toXY(p2);

    const vx = b.x - a.x;
    const vy = b.y - a.y;
    const wx = -a.x;
    const wy = -a.y;

    const vv = vx * vx + vy * vy;
    let t = vv > 0 ? (wx * vx + wy * vy) / vv : 0;
    t = clamp(t, 0, 1);

    const px = a.x + t * vx;
    const py = a.y + t * vy;
    const dist = Math.sqrt(px * px + py * py);

    const segLen = haversineMeters(p1.lat, p1.lon, p2.lat, p2.lon);
    const s = cum[i] + t * segLen;

    if (dist < best.distMeters) best = { sMeters: s, distMeters: dist };
  }
  return best;
}

function pointAtS(pts, cum, sMeters) {
  if (!pts.length) return null;
  const total = cum[cum.length - 1];
  if (!Number.isFinite(sMeters) || sMeters <= 0 || sMeters >= total) return null;

  let i = 1;
  while (i < cum.length && cum[i] < sMeters) i++;
  const i0 = Math.max(0, i - 1);
  const i1 = Math.min(pts.length - 1, i);

  const s0 = cum[i0];
  const s1 = cum[i1];
  const t = (sMeters - s0) / Math.max(1e-6, s1 - s0);

  const a = pts[i0];
  const b = pts[i1];

  return { lat: a.lat + (b.lat - a.lat) * t, lon: a.lon + (b.lon - a.lon) * t };
}

function mergeIntervals(intervals) {
  if (!intervals.length) return [];
  intervals.sort((a, b) => a[0] - b[0]);
  const merged = [intervals[0].slice()];
  for (let i = 1; i < intervals.length; i++) {
    const last = merged[merged.length - 1];
    const cur = intervals[i];
    if (cur[0] <= last[1]) last[1] = Math.max(last[1], cur[1]);
    else merged.push(cur.slice());
  }
  return merged;
}

function normalizeName(s) {
  return String(s || "")
    .toLowerCase()
    .replace(/\(.*?\)/g, " ")
    .replace(/[^\p{L}\p{N}\s]/gu, " ")
    .replace(/\s+/g, " ")
    .trim();
}
function looksLikeRailStopName(name) {
  const n = normalizeName(name);
  return /\bbahnhof\b/.test(n) || /\bbf\b/.test(n) || /\bhbf\b/.test(n) || /\bstation\b/.test(n);
}

// -------------------- Small TTL cache --------------------
function makeTTLCache() {
  const m = new Map(); // key -> { t, v, ttl }
  return {
    get(key) {
      const it = m.get(key);
      if (!it) return null;
      if (Date.now() - it.t > it.ttl) {
        m.delete(key);
        return null;
      }
      return it.v;
    },
    set(key, value, ttl) {
      m.set(key, { t: Date.now(), v: value, ttl });
    },
    has(key) {
      return this.get(key) != null;
    }
  };
}

const rmvNearbyCache = makeTTLCache(); // key: lat,lon,maxNo
const rmvDepsCache = makeTTLCache();   // key: stopId
const stationsCache = makeTTLCache();  // key: crossingKey -> {mode, railWayOut, stations, stitchedMeta, crossingUsed}

// -------------------- Overpass soft + cache --------------------
const overpassCache = new Map();
const OVERPASS_CACHE_MS = 10 * 60 * 1000;

function opCacheGet(key) {
  const v = overpassCache.get(key);
  if (!v) return null;
  if (Date.now() - v.t > OVERPASS_CACHE_MS) return null;
  return v.json;
}
function opCacheSet(key, json) {
  overpassCache.set(key, { t: Date.now(), json });
}

async function overpassSoft(query, cacheKey) {
  const cached = cacheKey ? opCacheGet(cacheKey) : null;
  if (cached) return { ok: true, json: cached, cached: true, endpoint: null };

  let lastErr = null;
  for (const endpoint of OVERPASS_ENDPOINTS) {
    for (let attempt = 0; attempt < 2; attempt++) {
      const controller = new AbortController();
      const t = setTimeout(() => controller.abort(), 22_000);
      try {
        const r = await fetch(endpoint, {
          method: "POST",
          headers: { "content-type": "application/x-www-form-urlencoded;charset=UTF-8" },
          body: "data=" + encodeURIComponent(query),
          signal: controller.signal,
        });
        const txt = await r.text();
        clearTimeout(t);

        if (!r.ok) {
          lastErr = new Error(`Overpass HTTP ${r.status}: ${txt.slice(0, 160)}`);
          await new Promise((res) => setTimeout(res, 800 + attempt * 600));
          continue;
        }
        if (!txt.trim().startsWith("{")) {
          lastErr = new Error(`Overpass non-JSON: ${txt.slice(0, 160)}`);
          await new Promise((res) => setTimeout(res, 800 + attempt * 600));
          continue;
        }

        const json = JSON.parse(txt);
        if (cacheKey) opCacheSet(cacheKey, json);
        return { ok: true, json, cached: false, endpoint };
      } catch (e) {
        clearTimeout(t);
        lastErr = e;
        await new Promise((res) => setTimeout(res, 800 + attempt * 600));
      }
    }
  }
  return { ok: false, error: String(lastErr?.message || lastErr || "Overpass failed") };
}

async function findNearestCrossingSoft(lat, lon, radiusM = 2500) {
  const key = `crossing:${radiusM}:${lat.toFixed(5)}:${lon.toFixed(5)}`;
  const q = `
[out:json][timeout:25];
(
  node(around:${radiusM},${lat},${lon})["railway"="level_crossing"];
  node(around:${radiusM},${lat},${lon})["railway"="tram_level_crossing"];
);
out body;`;

  const r = await overpassSoft(q, key);
  if (!r.ok) return { ok: false, error: r.error };

  const els = r.json.elements || [];
  if (!els.length) return { ok: true, crossing: null, overpass: { cached: r.cached, endpoint: r.endpoint } };

  let best = null;
  for (const el of els) {
    if (typeof el.lat !== "number" || typeof el.lon !== "number") continue;
    const d = haversineMeters(lat, lon, el.lat, el.lon);
    if (!best || d < best.distM) best = { id: el.id, lat: el.lat, lon: el.lon, tags: el.tags || {}, distM: d };
  }
  best.distM = Math.round(best.distM);
  return { ok: true, crossing: best, overpass: { cached: r.cached, endpoint: r.endpoint } };
}

// rail network
async function fetchRailNetworkAround(lat, lon, radiusM = RAIL_NET_RADIUS_M) {
  const key = `railNet:${radiusM}:${lat.toFixed(5)}:${lon.toFixed(5)}`;
  const q = `
[out:json][timeout:25];
(
  way(around:${radiusM},${lat},${lon})["railway"~"^(rail|light_rail|subway|tram)$"];
);
(._;>;);
out body;`;

  const r = await overpassSoft(q, key);
  if (!r.ok) return { ok: false, error: r.error };

  const nodes = new Map();
  for (const e of (r.json.elements || [])) {
    if (e.type === "node" && typeof e.lat === "number" && typeof e.lon === "number") {
      nodes.set(e.id, { lat: e.lat, lon: e.lon });
    }
  }

  const ways = [];
  for (const e of (r.json.elements || [])) {
    if (e.type !== "way") continue;
    if (!Array.isArray(e.nodes) || e.nodes.length < 2) continue;

    const pts = [];
    for (const nid of e.nodes) {
      const p = nodes.get(nid);
      if (p) pts.push({ lat: p.lat, lon: p.lon, nid });
    }
    if (pts.length < 2) continue;

    const cum = polylineCumulativeMeters(pts);
    ways.push({
      wayId: e.id,
      tags: e.tags || {},
      pts,
      cum,
      lengthM: cum[cum.length - 1],
      a: e.nodes[0],
      b: e.nodes[e.nodes.length - 1],
    });
  }

  return { ok: true, ways, nodesCount: nodes.size, cached: r.cached, endpoint: r.endpoint };
}

function buildWaysById(ways) {
  const m = new Map();
  for (const w of ways) m.set(w.wayId, w);
  return m;
}
function buildEndpointIndex(ways) {
  const index = new Map();
  for (const w of ways) {
    for (const end of [w.a, w.b]) {
      if (!index.has(end)) index.set(end, []);
      index.get(end).push(w.wayId);
    }
  }
  return index;
}

function findBestStartWay(cLat, cLon, ways) {
  let best = null;
  for (const w of ways) {
    const proj = projectToPolylineMeters(cLat, cLon, w.pts, w.cum);
    if (!best || proj.distMeters < best.proj.distMeters) best = { w, proj };
  }
  return best;
}

// naive stitch
function stitchFromWay(startWay, waysById, endpointIndex, targetMeters = STITCH_TARGET_M) {
  const used = new Set([startWay.wayId]);

  function chooseNextWay(node) {
    const candidates = (endpointIndex.get(node) || [])
      .map((id) => waysById.get(id))
      .filter((w) => w && !used.has(w.wayId));
    if (!candidates.length) return null;
    candidates.sort((a, b) => b.lengthM - a.lengthM);
    return candidates[0];
  }

  function extendFrom(nodeStart, ptsOut) {
    let total = 0;
    let node = nodeStart;
    while (total < targetMeters) {
      const w = chooseNextWay(node);
      if (!w) break;
      used.add(w.wayId);

      const forward = w.a === node;
      const seq = forward ? w.pts : [...w.pts].reverse();
      for (let i = 1; i < seq.length; i++) ptsOut.push(seq[i]);

      total += w.lengthM;
      node = forward ? w.b : w.a;
    }
  }

  const base = startWay.pts.map((p) => ({ lat: p.lat, lon: p.lon, nid: p.nid }));
  const leftPts = [...base];
  const rightPts = [...base];

  extendFrom(startWay.a, leftPts);
  extendFrom(startWay.b, rightPts);

  const merged = [...leftPts].reverse().concat(rightPts.slice(1));
  const cum = polylineCumulativeMeters(merged);

  return { pts: merged, cum, lengthM: cum[cum.length - 1], usedWays: Array.from(used) };
}

// -------------------- RMV with QUOTA SAFE CACHE --------------------
function isQuotaError(jsonOrText) {
  const s = typeof jsonOrText === "string" ? jsonOrText : JSON.stringify(jsonOrText || {});
  return s.includes("API_QUOTA") || s.toLowerCase().includes("quota exceeded");
}

async function rmvNearbyStops(lat, lon, maxNo = 12) {
  if (!RMV_KEY) throw new Error("RMV_API_KEY fehlt (.env)");

  // ✅ cache key – rounding to reduce unique keys
  const key = `nearby:${lat.toFixed(5)}:${lon.toFixed(5)}:${maxNo}`;
  const cached = rmvNearbyCache.get(key);
  if (cached) return cached;

  const url =
    `${RMV_BASE}/location.nearbystops` +
    `?originCoordLat=${encodeURIComponent(lat)}` +
    `&originCoordLong=${encodeURIComponent(lon)}` +
    `&accessId=${encodeURIComponent(RMV_KEY)}` +
    `&format=json&maxNo=${encodeURIComponent(maxNo)}`;

  const r = await fetchWithRetry(url, 3);
  const txt = await r.text();

  // RMV kann bei quota 401 + JSON liefern
  if (!r.ok) {
    // wenn quota: cached fallback
    if (isQuotaError(txt)) {
      const any = rmvNearbyCache.get(key);
      if (any) return any;
      const err = new Error(`RMV nearbyStops quota exceeded`);
      err.code = "API_QUOTA";
      throw err;
    }
    throw new Error(`RMV nearbyStops HTTP ${r.status}: ${txt.slice(0, 200)}`);
  }

  const json = JSON.parse(txt);
  if (json.errorCode || json.errorText) {
    if (isQuotaError(json)) {
      const any = rmvNearbyCache.get(key);
      if (any) return any;
      const err = new Error(`RMV nearbyStops quota exceeded`);
      err.code = "API_QUOTA";
      throw err;
    }
    throw new Error(`RMV nearbyStops error: ${json.errorCode || ""} ${json.errorText || ""}`.trim());
  }

  let items = json.stopLocationList?.stopLocation;
  if (!Array.isArray(items)) {
    items = (json.stopLocationOrCoordLocation || []).map((x) => x.StopLocation).filter(Boolean);
  }
  if (!Array.isArray(items)) items = [];

  const out = items
    .map((s) => ({
      id: s.id,
      name: s.name,
      lat: Number(s.lat),
      lon: Number(s.lon),
      dist: Number(s.dist ?? 1e9),
      products: String(s.products || "").toLowerCase(),
    }))
    .filter((s) => s.id && s.name && Number.isFinite(s.lat) && Number.isFinite(s.lon))
    .sort((a, b) => a.dist - b.dist)
    .slice(0, maxNo);

  rmvNearbyCache.set(key, out, RMV_NEARBY_TTL_MS);
  return out;
}

async function rmvDepartures(stopId) {
  if (!RMV_KEY) throw new Error("RMV_API_KEY fehlt (.env)");

  const key = `deps:${stopId}`;
  const cached = rmvDepsCache.get(key);
  if (cached) return cached;

  const now = Date.now();
  const maxT = now + LOOKAHEAD_MS;

  const url =
    `${RMV_BASE}/departureBoard` +
    `?id=${encodeURIComponent(stopId)}` +
    `&accessId=${encodeURIComponent(RMV_KEY)}` +
    `&format=json&maxJourneys=90`;

  const r = await fetchWithRetry(url, 3);
  const txt = await r.text();

  if (!r.ok) {
    if (isQuotaError(txt)) {
      const any = rmvDepsCache.get(key);
      if (any) return any;
      const err = new Error(`RMV departureBoard quota exceeded`);
      err.code = "API_QUOTA";
      throw err;
    }
    throw new Error(`RMV departureBoard HTTP ${r.status}: ${txt.slice(0, 200)}`);
  }

  const json = JSON.parse(txt);
  if (json.errorCode || json.errorText) {
    if (isQuotaError(json)) {
      const any = rmvDepsCache.get(key);
      if (any) return any;
      const err = new Error(`RMV departureBoard quota exceeded`);
      err.code = "API_QUOTA";
      throw err;
    }
    throw new Error(`RMV departureBoard error: ${json.errorCode || ""} ${json.errorText || ""}`.trim());
  }

  const deps = json.Departure || [];
  const out = [];
  for (const d of deps) {
    const date = d.rtDate || d.date;
    const time = d.rtTime || d.time;
    if (!date || !time) continue;

    const ts = new Date(`${date}T${time}`).getTime();
    if (!Number.isFinite(ts)) continue;
    if (ts < now - 60_000 || ts > maxT) continue;

    const lineRaw =
      d?.ProductAtStop?.line ||
      d?.ProductAtStop?.displayNumber ||
      d?.Product?.[0]?.line ||
      d?.line ||
      "";
    const line = String(lineRaw).trim().toUpperCase();

    const cat =
      String(d?.ProductAtStop?.catOut || d?.ProductAtStop?.catIn || d?.ProductAtStop?.cat || d?.cat || "")
        .trim()
        .toUpperCase();

    const direction = String(d.direction || d.dir || d?.ProductAtStop?.direction || "").trim();
    const delay = parseInt(d.delay || "0", 10) || 0;

    out.push({ ts, line, cat, direction, delay });
  }

  rmvDepsCache.set(key, out, RMV_DEPS_TTL_MS);
  return out;
}

function isSBahn(dep) {
  if (!ONLY_SBAHN) return true;
  const line = String(dep?.line || "").toUpperCase();
  const cat = String(dep?.cat || "").toUpperCase();
  if (cat === "S" || cat.includes("SBAHN")) return true;
  if (/^S\d+/.test(line)) return true;
  return false;
}

function inferSpeedKmh(dep) {
  const line = String(dep?.line || "").toUpperCase();
  if (/^S\d+/.test(line)) return 60;
  return 60;
}

function computeAdaptiveBufferMs(delayMin, prevPass, pass) {
  let b = BASE_BUFFER_MS;
  if ((delayMin || 0) >= DELAY_BOOST_AT_MIN) b += DELAY_BOOST_MS;

  if (Number.isFinite(prevPass) && Number.isFinite(pass)) {
    const headway = pass - prevPass;
    if (headway > 0 && headway <= HEADWAY_TIGHT_MS) b -= HEADWAY_REDUCE_MS;
  }
  return clamp(b, MIN_BUFFER_MS, MAX_BUFFER_MS);
}

function dedupEvents(events) {
  events.sort((a, b) => a.pass - b.pass);
  const out = [];
  const lastByKey = new Map();

  for (const e of events) {
    const key = `${e.line}|${e.fromStationId}|${e.side || ""}`;
    const prev = lastByKey.get(key);
    if (prev && Math.abs(e.pass - prev.pass) <= DEDUP_WINDOW_MS) {
      if (e.pass < prev.pass) prev.pass = e.pass;
      prev.delay = Math.max(prev.delay || 0, e.delay || 0);
      continue;
    }
    out.push(e);
    lastByKey.set(key, e);
  }
  return out;
}

function pickBestRmvStop(stops) {
  let best = null;
  let bestScore = -1e9;

  for (const s of stops || []) {
    const p = s.products || "";
    const railish =
      p.includes("sbahn") ||
      p.includes("train") ||
      p.includes("rail") ||
      p.includes("regional") ||
      p.includes("subway") ||
      p.includes("tram") ||
      p.includes("s");

    let score = 0;
    if (railish) score += 50;
    if (looksLikeRailStopName(s.name)) score += 25;
    score += clamp(20 - (s.dist || 9999) / 100, -50, 20);

    if (score > bestScore) {
      bestScore = score;
      best = s;
    }
  }
  return best;
}

async function bestStopNear(lat, lon, maxNo = 18) {
  const stops = await rmvNearbyStops(lat, lon, maxNo);
  return pickBestRmvStop(stops);
}

// Scan + force distinct
async function findBestStationsByScan(track, crossingS, notes) {
  const total = track.cum[track.cum.length - 1];

  if (crossingS < MIN_SIDE_COVERAGE_M || (total - crossingS) < MIN_SIDE_COVERAGE_M) {
    notes.push(`scan reject: sideCoverage too small total=${Math.round(total)} crossingS=${Math.round(crossingS)}`);
    return null;
  }

  function scoreStop(cand, off) {
    const name = cand.name || "";
    const n = normalizeName(name);
    const isBf = /\bbahnhof\b/.test(n) || /\bbf\b/.test(n) || /\bhbf\b/.test(n);

    const p = cand.products || "";
    const isS = p.includes("sbahn") || /^S\d+/.test(String(cand.name || "").toUpperCase());

    let score = 0;
    score += isBf ? 160 : 0;
    score += looksLikeRailStopName(name) ? 50 : 0;
    score += isS ? 30 : 0;
    score += clamp(60 - off / 35, -60, 60);
    score += clamp(20 - (cand.dist || 9999) / 70, -60, 20);
    return score;
  }

  async function bestOnSide(side, { minOff, maxOff, step, banIds = new Set() }) {
    let best = null;
    let bestScore = -1e9;

    for (let off = minOff; off <= maxOff; off += step) {
      const s = side === "minus" ? (crossingS - off) : (crossingS + off);
      if (s <= 0 || s >= total) continue;

      const pt = pointAtS(track.pts, track.cum, s);
      if (!pt) continue;

      const cand = await bestStopNear(pt.lat, pt.lon, 18);
      if (!cand?.id) continue;
      if (banIds.has(cand.id)) continue;

      const sc = scoreStop(cand, off);

      if (sc > bestScore) {
        bestScore = sc;
        best = {
          side,
          off,
          name: cand.name,
          rmvId: cand.id,
          lat: cand.lat,
          lon: cand.lon,
          travelMeters: Math.round(off),
          alongTrackM: Math.round(off),
          score: Math.round(sc),
        };
      }
    }

    if (best) notes.push(`scan:${side} best="${best.name}" off=${best.off} score=${best.score}`);
    else notes.push(`scan:${side} no candidate in ${minOff}-${maxOff}m`);

    return best;
  }

  const base = { minOff: SCAN_MIN_M, maxOff: SCAN_MAX_M, step: SCAN_STEP_M };
  const L1 = await bestOnSide("minus", base);
  const R1 = await bestOnSide("plus", base);
  if (!L1 || !R1) return null;

  if (L1.rmvId === R1.rmvId) {
    notes.push(`scan: L/R identical (${L1.name}) -> force distinct on plus`);
    const ban = new Set([L1.rmvId]);

    const R2 = await bestOnSide("plus", { minOff: FORCE_MIN_M, maxOff: FORCE_MAX_M, step: FORCE_STEP_M, banIds: ban });
    if (R2) return { left: L1, right: R2 };

    const L2 = await bestOnSide("minus", { minOff: FORCE_MIN_M, maxOff: FORCE_MAX_M, step: FORCE_STEP_M, banIds: ban });
    if (L2) return { left: L2, right: R1 };

    notes.push(`scan: could not force distinct L/R`);
    return null;
  }

  return { left: L1, right: R1 };
}

// -------------------- /api/connect --------------------
app.post("/api/connect", async (req, res) => {
  try {
    if (!RMV_KEY) return res.status(500).json({ error: "RMV_API_KEY fehlt (.env)." });

    const { lat, lon } = req.body || {};
    if (!Number.isFinite(lat) || !Number.isFinite(lon)) {
      return res.status(400).json({ error: "lat/lon fehlt oder ungültig." });
    }

    const notes = [];

    const crossR = await findNearestCrossingSoft(lat, lon, 2500);
    let crossing;
    if (crossR.ok && crossR.crossing) {
      crossing = crossR.crossing;
      notes.push(`crossing: ok${crossR.overpass?.cached ? " (cached)" : ""}`);
    } else {
      crossing = { id: null, lat, lon, tags: { name: null }, distM: 0 };
      notes.push("crossing: fallback(marker)");
      if (!crossR.ok) notes.push(`overpass: ${crossR.error}`);
    }

    // ✅ stations cache key by crossing ID if exists, else by rounded coords
    const crossingKey =
      crossing.id ? `xid:${crossing.id}` : `xll:${crossing.lat.toFixed(5)}:${crossing.lon.toFixed(5)}`;

    // ✅ If we have cached stations and crossing is basically the same: reuse -> no RMV nearbyStops scan!
    const cachedStationsPack = stationsCache.get(crossingKey);
    const canReuseStations =
      cachedStationsPack &&
      haversineMeters(crossing.lat, crossing.lon, cachedStationsPack.crossingUsed.lat, cachedStationsPack.crossingUsed.lon) <=
        SAME_CROSSING_DIST_M;

    let mode = "fallback";
    let railWayOut = null;
    let stations = [];
    let stitchedMeta = null;

    if (canReuseStations) {
      mode = cachedStationsPack.mode;
      railWayOut = cachedStationsPack.railWay;
      stations = cachedStationsPack.stations;
      stitchedMeta = cachedStationsPack.stitchedMeta;
      notes.push(`stationsCache: hit (${crossingKey}) reuseStations=true`);
    } else {
      notes.push(`stationsCache: miss (${crossingKey}) -> compute stations`);

      // Track attempt
      const net = await fetchRailNetworkAround(crossing.lat, crossing.lon, RAIL_NET_RADIUS_M);
      if (net.ok && net.ways.length) {
        notes.push(`railNet: ways=${net.ways.length} nodes=${net.nodesCount} radius=${RAIL_NET_RADIUS_M}m`);
        const waysById = buildWaysById(net.ways);
        const endpointIndex = buildEndpointIndex(net.ways);

        const start = findBestStartWay(crossing.lat, crossing.lon, net.ways);
        if (start) {
          notes.push(`startWay=${start.w.wayId} startProjDist=${Math.round(start.proj.distMeters)}m startLen=${Math.round(start.w.lengthM)}m`);

          const stitchedTrack = stitchFromWay(start.w, waysById, endpointIndex, STITCH_TARGET_M);
          stitchedMeta = { lenM: Math.round(stitchedTrack.lengthM), usedWays: stitchedTrack.usedWays.length };
          notes.push(`stitchedLen=${stitchedMeta.lenM}m usedWays=${stitchedMeta.usedWays}`);

          const proj = projectToPolylineMeters(crossing.lat, crossing.lon, stitchedTrack.pts, stitchedTrack.cum);
          notes.push(`stitchedProjDist=${Math.round(proj.distMeters)}m crossingS=${Math.round(proj.sMeters)}m`);

          const pair = await findBestStationsByScan(stitchedTrack, proj.sMeters, notes);
          if (pair) {
            mode = "track";
            stations = [
              {
                name: pair.left.name,
                rmvId: pair.left.rmvId,
                lat: pair.left.lat,
                lon: pair.left.lon,
                side: "minus",
                resolveHow: `track:scan(minus@${pair.left.off})`,
                alongTrackM: pair.left.alongTrackM,
                travelMeters: pair.left.travelMeters,
                travelMs: 0,
              },
              {
                name: pair.right.name,
                rmvId: pair.right.rmvId,
                lat: pair.right.lat,
                lon: pair.right.lon,
                side: "plus",
                resolveHow: `track:scan(plus@${pair.right.off})`,
                alongTrackM: pair.right.alongTrackM,
                travelMeters: pair.right.travelMeters,
                travelMs: 0,
              },
            ];

            notes.push(`track: ok | L="${stations[0].name}" R="${stations[1].name}"`);
            railWayOut = { wayId: start.w.wayId, tags: start.w.tags, crossingDistToWayM: Math.round(start.proj.distMeters) };
          } else {
            notes.push("track: stitched but scan found no valid L/R -> fallback");
          }
        } else {
          notes.push("track: no start way -> fallback");
        }
      } else {
        notes.push("track: railNet empty -> fallback");
        if (!net.ok) notes.push(`railNet err: ${net.error}`);
      }

      // Fallback
      if (mode === "fallback") {
        const nb = await rmvNearbyStops(crossing.lat, crossing.lon, 20);
        const pick = nb.slice(0, 4);
        stations = pick.map((s) => {
          const distM = haversineMeters(crossing.lat, crossing.lon, s.lat, s.lon);
          return {
            name: s.name,
            rmvId: s.id,
            lat: s.lat,
            lon: s.lon,
            resolveHow: "fallback:nearbyStops",
            side: null,
            alongTrackM: Math.round(distM),
            travelMeters: Math.round(distM),
            travelMs: clamp(Math.round((distM / 1000 / 60) * 3600 * 1000), MIN_TRAVEL_MS, MAX_TRAVEL_MS),
          };
        });
      }

      // ✅ store stations pack
      stationsCache.set(
        crossingKey,
        {
          mode,
          railWay: railWayOut,
          stations,
          stitchedMeta,
          crossingUsed: { lat: crossing.lat, lon: crossing.lon },
        },
        STATIONS_TTL_MS
      );
    }

    // Departures -> events -> intervals (cheap, cached for 25s)
    const perStation = [];
    const events = [];

    const haveLR = mode === "track" && stations.length === 2;
    const leftStation = haveLR ? stations.find((s) => s.side === "minus") : null;
    const rightStation = haveLR ? stations.find((s) => s.side === "plus") : null;

    for (const st of stations) {
      const deps = await rmvDepartures(st.rmvId);
      perStation.push({ name: st.name, rmvId: st.rmvId, deps: deps.length });
      notes.push(`depsRaw(${st.name})=${deps.length}`);

      let kept = 0;

      for (const d of deps) {
        if (!isSBahn(d)) continue;

        // optional: Richtung (soft)
        if (haveLR && d.direction) {
          const other = st.side === "minus" ? rightStation : leftStation;
          const otherLast = normalizeName(other.name).split(" ").slice(-1)[0];
          const dirN = normalizeName(d.direction);
          if (otherLast && !dirN.includes(otherLast)) continue;
        }

        const speedKmh = inferSpeedKmh(d);
        const travelMsRaw = Math.round((st.travelMeters / 1000 / speedKmh) * 3600 * 1000);
        const travelMs = clamp(travelMsRaw, MIN_TRAVEL_MS, MAX_TRAVEL_MS);
        st.travelMs = travelMs;

        const pass = d.ts + travelMs;
        events.push({
          pass,
          line: d.line,
          delay: d.delay || 0,
          fromStationId: st.rmvId,
          side: st.side || null,
        });
        kept++;
      }

      notes.push(`depsKept(${st.name})=${kept}`);
    }

    const deduped = dedupEvents(events);
    const intervals = [];
    let prevPass = NaN;

    for (const e of deduped.sort((a, b) => a.pass - b.pass)) {
      const buf = computeAdaptiveBufferMs(e.delay, prevPass, e.pass);
      intervals.push([e.pass - buf, e.pass + PASS_TIME_MS]);
      prevPass = e.pass;
    }

    const closedIntervals = mergeIntervals(intervals).filter((iv) => iv[1] > Date.now() - 60_000);

    res.json({
      mode,
      crossing,
      railWay: railWayOut,
      stations,
      closedIntervals,
      debug: {
        note: notes.join(" | "),
        stations: stations.length,
        perStation,
        events: events.length,
        usedEvents: deduped.length,
        mergedIntervals: closedIntervals.length,
        stitched: stitchedMeta || null,
        cache: {
          stationsCacheKey: crossingKey,
          nearbyTTLmin: RMV_NEARBY_TTL_MS / 60000,
          depsTTLsec: RMV_DEPS_TTL_MS / 1000,
        },
      },
    });
  } catch (e) {
    const msg = String(e?.message || e);
    const code = e?.code || "";

    // ✅ Quota -> 429 (Too Many Requests) with friendly info
    if (code === "API_QUOTA" || msg.toLowerCase().includes("quota")) {
      return res.status(429).json({
        error: "RMV API_QUOTA: Kontingent aufgebraucht. Warte oder nutze weniger Requests (Caching aktiv).",
        hint: "Tipp: Scan passiert jetzt nur selten. Wenn du gerade viel getestet hast, warte bis das RMV-Kontingent zurückgesetzt ist.",
      });
    }

    console.error("api/connect error:", e);
    res.status(500).json({
      error: msg,
      stack: e?.stack ? String(e.stack).split("\n").slice(0, 12).join("\n") : null,
    });
  }
});

app.listen(PORT, () => {
  console.log(`✅ Server läuft: http://localhost:${PORT}`);
  console.log(`✅ Ping:        http://localhost:${PORT}/api/ping`);
});
