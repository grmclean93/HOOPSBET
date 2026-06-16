// ═══════════════════════════════════════════════════════════════════════════
// HOOPSBET v1.3.2 (GOVERNOR) — NCAA Basketball sides & totals analytics
// S1: chassis + market layer (The Odds API, sole odds source)
// S2: Torvik-fed efficiency model (AdjOE/AdjDE/AdjT) + Models surface
// S3: picks engine · fractional Kelly · Redis tracker · CLV grading
// S4: Pinnacle-anchored +EV screen (line-match gated) · record polish
// S5: lookahead-free replay — Odds API historical snapshots + Torvik Time
//     Machine ratings-as-of-date; picks sim at open, CLV vs close;
//     calibration report (residual SDs, HCA, totals bias) — recommend only
// v1.3.2: replay ingest hardened — per-run credit ceiling enforced against the
//     REAL quota delta, 429/5xx backoff-retry, Redis-required guard, accurate
//     per-call cost (Pinnacle kept ⇒ ~60/call across US+EU regions).
// Odds: one slate call — bookmakers list (7 books incl Pinnacle = 1 group) ×
//       3 markets = 3 credits per refresh, slate-size-blind.
// Model: multiplicative efficiency (KenPom/Torvik convention):
//       pace = adjtA·adjtH/avgT ; eff = adjoe·oppAdjde/avgEff ; pts = eff·pace/100
//       HCA split ±HCA/2 (zeroed on neutral) ; P(home ML) = Φ(margin/SD)
// Sign conventions (phantom-edge guard, see tests):
//       sprH = home handicap (−7.5 ⇒ home favored). P(home covers)=Φ((margin+sprH)/SD)
//       P(over)=Φ((modelTotal−line)/TOT_SD)
// ═══════════════════════════════════════════════════════════════════════════
const express = require("express");
const cors = require("cors");
const fetch = require("node-fetch");
const zlib = require("zlib");

const app = express();
app.use(cors());
app.use(express.json({ limit: "32mb" }));

const PORT = process.env.PORT || 3000;
const ODDS_KEY = process.env.ODDS_API_KEY || "";
const REDIS_URL = process.env.UPSTASH_REDIS_URL || "";
const REDIS_TOKEN = process.env.UPSTASH_REDIS_TOKEN || "";

const VERSION = "1.3.18";
const SPORT = "basketball_ncaab";
const ODDS_HOST = "https://api.the-odds-api.com";
// 7 bookmakers = one group of 10 ⇒ 1 region-equivalent; Pinnacle rides along free.
const BOOKS = ["draftkings", "fanduel", "betmgm", "caesars", "betrivers", "espnbet", "pinnacle"];
const SHARP = "pinnacle";
const RETAIL = BOOKS.filter(b => b !== SHARP);
const MARKETS = "h2h,spreads,totals";

// ── tunable model/threshold config (runtime-adjustable via /api/admin/model) ──
let CFG = {
  HCA: 3.0,        // home-court points (CBB ≈ 3.0–3.5; observe → tune)
  SD: 10.5,        // margin SD (CBB ≈ 10.5–11)
  TOT_SD: 16,      // total SD
  RATINGS_MAX_AGE_H: 72,
  thresholds: { ML: 4.0, SPR: 5.0, TOT: 5.5, BOOKS: 3 }, // percent floors + min books gate
  kelly: { fraction: 0.25, maxU: 2.0, minU: 0.25 },       // quarter-Kelly; 1u = 1% of bankroll
  ev: { min: 2.0, strongGap: 2.0 },                        // EV% floor; outlier gap (implied pts)
  replay: { snapTimes: ["16:00", "04:55+1"],               // UTC; "+1" = next calendar day (≈11am / 11:55pm ET)
    lagDays: 0, safetyCredits: 500, fetchDelayMs: 400, costPerCall: 60, maxRetries: 3 },
  GRADE_LAG_MIN: 120                                       // grade picks >=2h after tip
};

// ═══ helpers ═════════════════════════════════════════════════════════════════
function normCdf(x) {
  const t = 1 / (1 + 0.2316419 * Math.abs(x));
  const d = 0.3989423 * Math.exp(-x * x / 2);
  const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274))));
  return x > 0 ? 1 - p : p;
}
function impProb(ml) { if (ml == null || ml === 0) return null; return ml < 0 ? Math.abs(ml) / (Math.abs(ml) + 100) : 100 / (ml + 100); }
function noVigPair(a, h) { const pa = impProb(a), ph = impProb(h); if (pa == null || ph == null) return null; const s = pa + ph; return { pA: pa / s, pH: ph / s, hold: s - 1 }; }
function median(arr) { const a = arr.filter(x => x != null).sort((x, y) => x - y); if (!a.length) return null; const m = Math.floor(a.length / 2); return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2; }
function mean(arr) { const a = arr.filter(x => x != null); return a.length ? a.reduce((s, x) => s + x, 0) / a.length : null; }
function todayKey() { return new Date().toISOString().slice(0, 10).replace(/-/g, ""); }
function seasonYear() { const d = new Date(); return d.getMonth() + 1 >= 10 ? d.getFullYear() + 1 : d.getFullYear(); }

// ═══ Redis (Upstash REST; graceful no-op when unset) ═════════════════════════
async function rCmd(cmd) {
  if (!REDIS_URL || !REDIS_TOKEN) return null;
  try {
    // Upstash REST: POST the command array in the request body. The old GET-path form put the value
    // in the URL and silently failed on large writes (e.g. a month of line snapshots), which broke
    // ingest persistence. Body form has no size limit and works for every command.
    const r = await fetch(REDIS_URL, { method: "POST", headers: { Authorization: "Bearer " + REDIS_TOKEN, "Content-Type": "application/json" }, body: JSON.stringify(cmd) });
    if (!r.ok) return null;
    return (await r.json()).result;
  } catch (e) { return null; }
}
const rGet = k => rCmd(["GET", k]);
const rSet = (k, v) => rCmd(["SET", k, typeof v === "string" ? v : JSON.stringify(v)]);

// Live Redis round-trip probe — distinguishes "configured" from "actually works".
// Used by /api/health, /api/debug/redis, and the ingest pre-flight so a present-but-broken
// Upstash credential is caught loudly instead of silently no-oping writes.
async function redisProbe() {
  if (!REDIS_URL || !REDIS_TOKEN) return { ok: false, configured: false, error: "env vars not set (UPSTASH_REDIS_URL / UPSTASH_REDIS_TOKEN)" };
  const scheme = (REDIS_URL.split("://")[0] || "").toLowerCase();
  if (scheme !== "https" && scheme !== "http") return { ok: false, configured: true, scheme: scheme, error: "UPSTASH_REDIS_URL is a '" + scheme + "://' value but this app uses the Upstash REST API \u2014 set it to the https://<db>.upstash.io REST URL, not the redis:// connection string" };
  const key = "hb:__probe", val = "x".repeat(20000) + Date.now(); // ~20KB, to exercise the large-value write path (not just a tiny value)
  const ctrl = new AbortController(), timer = setTimeout(function () { ctrl.abort(); }, 6000);
  const post = c => fetch(REDIS_URL, { method: "POST", headers: { Authorization: "Bearer " + REDIS_TOKEN, "Content-Type": "application/json" }, body: JSON.stringify(c), signal: ctrl.signal });
  try {
    const w = await post(["SET", key, val]);
    if (!w.ok) return { ok: false, configured: true, scheme: scheme, status: w.status, error: "SET returned HTTP " + w.status + (w.status === 401 ? " (token rejected / WRONGPASS)" : "") };
    const rd = await post(["GET", key]);
    if (!rd.ok) return { ok: false, configured: true, scheme: scheme, status: rd.status, error: "GET returned HTTP " + rd.status };
    const readBack = (await rd.json()).result;
    return { ok: readBack === val, configured: true, scheme: scheme, bytesTested: val.length, error: readBack === val ? null : "round-trip mismatch on a " + val.length + "-byte value" };
  } catch (e) {
    return { ok: false, configured: true, scheme: scheme, error: "request failed: " + (e.name === "AbortError" ? "timeout (6s)" : e.message) };
  } finally { clearTimeout(timer); }
}

// ═══ ODDS LAYER (S1) ═════════════════════════════════════════════════════════
let QUOTA = { remaining: null, used: null, last: null, ts: 0 };
let LAST_ODDS_ERR = null;
function captureQuota(resp) {
  const rem = resp.headers.get("x-requests-remaining"), used = resp.headers.get("x-requests-used"), last = resp.headers.get("x-requests-last");
  if (rem != null) QUOTA = { remaining: +rem, used: used != null ? +used : null, last: last != null ? +last : null, ts: Date.now() };
}

async function fetchOddsRaw() {
  const url = ODDS_HOST + "/v4/sports/" + SPORT + "/odds?apiKey=" + ODDS_KEY +
    "&bookmakers=" + BOOKS.join(",") + "&markets=" + MARKETS + "&oddsFormat=american&dateFormat=iso";
  const r = await fetch(url);
  captureQuota(r);
  if (!r.ok) {
    let msg = "odds HTTP " + r.status;
    try { const j = await r.json(); if (j.message) msg += " — " + j.message; } catch (e) {}
    LAST_ODDS_ERR = { ts: Date.now(), msg };
    throw new Error(msg);
  }
  LAST_ODDS_ERR = null;
  return r.json();
}

// normalize one Odds API event → internal game (pure; unit-tested)
function normalizeGame(ev) {
  const g = {
    id: ev.id, away: ev.away_team, home: ev.home_team, commence: ev.commence_time,
    books: {}, nML: 0, nSPR: 0, nTOT: 0
  };
  (ev.bookmakers || []).forEach(bk => {
    const b = { mlA: null, mlH: null, sprA: null, sprH: null, sprAJ: null, sprHJ: null, tot: null, overJ: null, underJ: null };
    (bk.markets || []).forEach(m => {
      (m.outcomes || []).forEach(o => {
        if (m.key === "h2h") {
          if (o.name === g.away) b.mlA = o.price; else if (o.name === g.home) b.mlH = o.price;
        } else if (m.key === "spreads") {
          if (o.name === g.away) { b.sprA = o.point; b.sprAJ = o.price; }
          else if (o.name === g.home) { b.sprH = o.point; b.sprHJ = o.price; }
        } else if (m.key === "totals") {
          if (/over/i.test(o.name)) { b.tot = o.point; b.overJ = o.price; }
          else if (/under/i.test(o.name)) { if (b.tot == null) b.tot = o.point; b.underJ = o.price; }
        }
      });
    });
    if (b.mlA != null || b.sprH != null || b.tot != null) g.books[bk.key] = b;
  });
  Object.assign(g, summarizeBooks(g.books));
  return g;
}

// shared by live normalizeGame and the replay unpacker — single source of truth
function summarizeBooks(books) {
  const retail = RETAIL.filter(k => books[k]);
  const out = {};
  out.nML = retail.filter(k => books[k].mlA != null && books[k].mlH != null).length;
  out.nSPR = retail.filter(k => books[k].sprH != null && books[k].sprHJ != null && books[k].sprAJ != null).length;
  out.nTOT = retail.filter(k => books[k].tot != null && books[k].overJ != null && books[k].underJ != null).length;
  out.nBooks = retail.length;
  const nvs = retail.map(k => noVigPair(books[k].mlA, books[k].mlH)).filter(Boolean);
  out.book = {
    pHome: nvs.length ? mean(nvs.map(x => x.pH)) : null,
    sprH: median(retail.map(k => books[k].sprH)),
    tot: median(retail.map(k => books[k].tot))
  };
  const s = books[SHARP];
  out.sharp = s ? {
    pHome: (s.mlA != null && s.mlH != null) ? noVigPair(s.mlA, s.mlH).pH : null,
    sprH: s.sprH != null ? s.sprH : null, tot: s.tot != null ? s.tot : null
  } : { pHome: null, sprH: null, tot: null };
  return out;
}

let slateCache = { d: null, t: 0 };
let LAST_SLATE_GAMES = null;
// NCAAB season is ~early Nov – early/mid April. Outside it, books post no D1 lines, so the
// dash's 3-min slate poll would spend Odds API credits fetching empty slates all summer. Gate
// non-forced live fetches on the offseason (a forced/manual pull still goes through).
function isOffseason(now) {
  const d = now || new Date(), m = d.getMonth() + 1, day = d.getDate();
  if (m >= 11 || m <= 3) return false;        // Nov–Mar: in-season
  if (m === 4 && day <= 14) return false;      // first half of April: tournament / postseason
  return true;                                 // mid-April – October: offseason
}
let OPENS = {}; let opensDirty = false;
function slateTtlMs() { const h = new Date().getUTCHours(); return (h >= 14 || h <= 5) ? 10 * 60e3 : 30 * 60e3; } // ~10am–1am ET active

async function getSlate(force) {
  if (!force && isOffseason()) { LAST_SLATE_GAMES = 0; return []; }
  if (!force && slateCache.d && Date.now() - slateCache.t < slateTtlMs()) return slateCache.d;
  const raw = await fetchOddsRaw();
  const games = raw.map(normalizeGame);
  // opening-line capture (S3 CLV groundwork — costs nothing extra)
  games.forEach(g => {
    if (!OPENS[g.id] && (g.book.pHome != null || g.book.sprH != null || g.book.tot != null)) {
      OPENS[g.id] = { ts: Date.now(), pHome: g.book.pHome, sprH: g.book.sprH, tot: g.book.tot, sharp: g.sharp };
      opensDirty = true;
    }
  });
  if (opensDirty) { rSet("hb:opens:" + todayKey(), OPENS); opensDirty = false; }
  updateLastSeen(games);
  slateCache = { d: games, t: Date.now() };
  LAST_SLATE_GAMES = games.length;
  return games;
}

let scoresCache = { d: null, t: 0 };
async function getScores() {
  if (scoresCache.d && Date.now() - scoresCache.t < 5 * 60e3) return scoresCache.d;
  const r = await fetch(ODDS_HOST + "/v4/sports/" + SPORT + "/scores?daysFrom=1&apiKey=" + ODDS_KEY);
  captureQuota(r);
  if (!r.ok) throw new Error("scores HTTP " + r.status);
  const d = await r.json();
  scoresCache = { d, t: Date.now() };
  return d;
}

// ═══ TORVIK LAYER (S2) — self-detecting adapter ═════════════════════════════
// barttorvik.com exposes ratings via ?csv=1 / ?json=1. Column order is
// undocumented and may drift, so instead of hard-coding positions we DETECT:
//   barthag → the only numeric column bounded in (0,1]
//   adjt    → the only numeric column with mean ≈ 55–80 (possessions)
//   adjoe/adjde → the two ~85–135 columns, split by correlation with barthag
//   team    → string column with the most distinct, mostly-alphabetic values
//   conf    → string column with 8–60 distinct short values
// The winning strategy + column map is locked (ODDSFIX pattern) and inspectable
// at /api/debug/torvik; an admin override exists if detection ever misfires.
let TORVIK = null; // { byTeam:{normName:{team,conf,adjoe,adjde,adjt,barthag,rank}}, avg:{eff,tempo}, year, mode, fetchedAt }
let TORVIK_LOCK = null; // { mode, colmap }
let TORVIK_ERR = null;
let TORVIK_RAW_SAMPLE = null;

function corr(xs, ys) {
  const n = Math.min(xs.length, ys.length); if (n < 3) return 0;
  const mx = mean(xs), my = mean(ys); let num = 0, dx = 0, dy = 0;
  for (let i = 0; i < n; i++) { const a = xs[i] - mx, b = ys[i] - my; num += a * b; dx += a * a; dy += b * b; }
  return (dx && dy) ? num / Math.sqrt(dx * dy) : 0;
}

function detectColumns(rows) {
  if (!rows || rows.length < 50) return null;
  const ncol = rows[0].length;
  const cols = [];
  for (let c = 0; c < ncol; c++) {
    const vals = rows.map(r => r[c]);
    const nums = vals.map(v => parseFloat(v)).filter(v => !isNaN(v));
    const numFrac = nums.length / vals.length;
    const strs = vals.filter(v => typeof v === "string" && /[a-zA-Z]/.test(v) && isNaN(parseFloat(v)));
    cols.push({ c, numFrac, mean: nums.length ? mean(nums) : null, min: nums.length ? Math.min(...nums) : null, max: nums.length ? Math.max(...nums) : null, nums, distinct: new Set(vals.map(String)).size, strFrac: strs.length / vals.length });
  }
  const numeric = cols.filter(x => x.numFrac > 0.95);
  const barthag = numeric.find(x => x.min > 0 && x.max <= 1.0001 && x.mean > 0.05 && x.mean < 0.95);
  const adjt = numeric.find(x => x.mean >= 55 && x.mean <= 80);
  const effCands = numeric.filter(x => x.mean >= 85 && x.mean <= 135 && x !== adjt);
  if (!barthag || !adjt || effCands.length < 2) return null;
  const scored = effCands.map(x => ({ x, r: corr(x.nums, barthag.nums) })).sort((a, b) => b.r - a.r);
  const adjoe = scored[0].x, adjde = scored[scored.length - 1].x;
  if (!(scored[0].r > 0.15 && scored[scored.length - 1].r < -0.15)) return null;
  const strings = cols.filter(x => x.strFrac > 0.9);
  const team = strings.sort((a, b) => b.distinct - a.distinct)[0];
  if (!team || team.distinct < 200) return null;
  const conf = strings.find(x => x !== team && x.distinct >= 8 && x.distinct <= 60) || null;
  return { team: team.c, conf: conf ? conf.c : null, adjoe: adjoe.c, adjde: adjde.c, adjt: adjt.c, barthag: barthag.c };
}

function parseCsv(text) {
  return text.trim().split(/\r?\n/).map(line => {
    const out = []; let cur = "", q = false;
    for (let i = 0; i < line.length; i++) {
      const ch = line[i];
      if (ch === '"') q = !q;
      else if (ch === "," && !q) { out.push(cur); cur = ""; }
      else cur += ch;
    }
    out.push(cur);
    return out;
  });
}

function headerColmap(header) {
  const find = (re) => { const i = header.findIndex(h => re.test(String(h).toLowerCase().replace(/[^a-z]/g, ""))); return i >= 0 ? i : null; };
  const m = {
    team: find(/^team$|^teamname$/), conf: find(/^conf$|^conference$/),
    adjoe: find(/^adjoe$|^adjo$/), adjde: find(/^adjde$|^adjd$/),
    adjt: find(/^adjt$|^adjtempo$|^tempo$/), barthag: find(/^barthag$/)
  };
  return (m.team != null && m.adjoe != null && m.adjde != null && m.adjt != null && m.barthag != null) ? m : null;
}

// shared by fetchTorvik(json) and Time Machine archives
function ratingsFromArray(arr, lockColmap) {
  if (!Array.isArray(arr[0])) {
    const keys = Object.keys(arr[0]);
    const hm = headerColmap(keys);
    if (hm) return { rows: arr.map(o => keys.map(k => o[k])), colmap: hm };
    const rows = arr.map(o => Object.values(o));
    return { rows, colmap: detectColumns(rows) };
  }
  return { rows: arr, colmap: lockColmap || detectColumns(arr) };
}

function buildTorvik(rows, colmap, year, mode) {
  const byTeam = {}; const list = [];
  rows.forEach(r => {
    const team = String(r[colmap.team] || "").trim();
    const adjoe = parseFloat(r[colmap.adjoe]), adjde = parseFloat(r[colmap.adjde]), adjt = parseFloat(r[colmap.adjt]), barthag = parseFloat(r[colmap.barthag]);
    if (!team || isNaN(adjoe) || isNaN(adjde) || isNaN(adjt) || isNaN(barthag)) return;
    const rec = { team, conf: colmap.conf != null ? String(r[colmap.conf] || "").trim() : "", adjoe, adjde, adjt, barthag };
    list.push(rec);
  });
  if (list.length < 200) return null;
  list.sort((a, b) => b.barthag - a.barthag).forEach((t, i) => { t.rank = i + 1; });
  list.forEach(t => { byTeam[normName(t.team)] = t; });
  return {
    byTeam, list,
    avg: { eff: mean(list.map(t => (t.adjoe + t.adjde) / 2)), tempo: mean(list.map(t => t.adjt)) },
    year, mode, fetchedAt: Date.now(), teams: list.length
  };
}

async function fetchTorvik(year, force) {
  year = year || seasonYear();
  if (!force && TORVIK && TORVIK.year === year && Date.now() - TORVIK.fetchedAt < 24 * 3600e3) return TORVIK;
  const strategies = [];
  if (TORVIK_LOCK) strategies.push(TORVIK_LOCK.mode);
  ["jsonfile", "csv", "json"].forEach(m => { if (!strategies.includes(m)) strategies.push(m); });
  for (const mode of strategies) {
    try {
      const url = mode === "jsonfile" ? ("https://barttorvik.com/" + year + "_team_results.json") : ("https://barttorvik.com/trank.php?year=" + year + (mode === "csv" ? "&csv=1" : "&json=1"));
      const r = await fetch(url, { headers: { "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", "Accept": mode === "csv" ? "text/csv,text/plain,*/*" : "application/json,text/plain,*/*" } });
      if (!r.ok) { TORVIK_ERR = mode + " HTTP " + r.status; continue; }
      let rows, colmap = null;
      if (mode === "csv") {
        const all = parseCsv(await r.text());
        if (all.length < 50) { TORVIK_ERR = "csv too short"; continue; }
        TORVIK_RAW_SAMPLE = all.slice(0, 2);
        colmap = headerColmap(all[0]);
        rows = colmap ? all.slice(1) : all;
        if (!colmap) colmap = (TORVIK_LOCK && TORVIK_LOCK.mode === mode && TORVIK_LOCK.colmap) || detectColumns(rows);
      } else {
        const j = await r.json();
        const arr = Array.isArray(j) ? j : (j.data || []);
        if (!arr.length) { TORVIK_ERR = "json empty"; continue; }
        TORVIK_RAW_SAMPLE = arr.slice(0, 2);
        const parsedA = ratingsFromArray(arr, (TORVIK_LOCK && TORVIK_LOCK.mode === mode) ? TORVIK_LOCK.colmap : null);
        rows = parsedA.rows; colmap = parsedA.colmap;
      }
      if (!colmap) { TORVIK_ERR = mode + ": column detection failed"; continue; }
      const built = buildTorvik(rows, colmap, year, mode);
      if (!built) { TORVIK_ERR = mode + ": build failed (<200 teams parsed)"; continue; }
      TORVIK = built; TORVIK_ERR = null;
      TORVIK_LOCK = { mode, colmap };
      rSet("hb:torvik:lock", TORVIK_LOCK);
      rSet("hb:torvik:last", { list: built.list, year: built.year, fetchedAt: built.fetchedAt, mode: built.mode });
      console.log("Torvik locked: mode=" + mode + " teams=" + built.teams + " avgEff=" + built.avg.eff.toFixed(1) + " avgT=" + built.avg.tempo.toFixed(1));
      return TORVIK;
    } catch (e) { TORVIK_ERR = mode + ": " + e.message; }
  }
  // graceful stale: fall back to last-good from Redis
  if (!TORVIK) {
    const last = await rGet("hb:torvik:last");
    if (last) {
      try {
        const p = typeof last === "string" ? JSON.parse(last) : last;
        const rebuilt = { byTeam: {}, list: p.list, avg: { eff: mean(p.list.map(t => (t.adjoe + t.adjde) / 2)), tempo: mean(p.list.map(t => t.adjt)) }, year: p.year, mode: p.mode + " (stale)", fetchedAt: p.fetchedAt, teams: p.list.length };
        p.list.forEach(t => { rebuilt.byTeam[normName(t.team)] = t; });
        TORVIK = rebuilt;
      } catch (e) {}
    }
  }
  return TORVIK;
}

// ═══ TEAM NAME MAP ═══════════════════════════════════════════════════════════
function normName(s) {
  return String(s || "").toLowerCase()
    .replace(/[().'’&-]/g, m => (m === "&" ? " and " : " "))
    .replace(/\b(state)\b/g, "st").replace(/\b(saint)\b/g, "st")
    .replace(/\s+/g, " ").trim();
}
// seeded aliases: normalized Odds-API full name → normalized Torvik name
const ALIAS_SEED = {
  "nc st wolfpack": "north carolina st", "north carolina st wolfpack": "north carolina st",
  "ole miss rebels": "mississippi", "uconn huskies": "connecticut",
  "miami hurricanes": "miami fl", "miami fl hurricanes": "miami fl",
  "miami redhawks": "miami oh", "miami oh redhawks": "miami oh",
  "southern california trojans": "usc", "texas san antonio roadrunners": "utsa", "utsa roadrunners": "utsa",
  "louisiana ragin cajuns": "louisiana", "hawai i rainbow warriors": "hawaii", "hawaii rainbow warriors": "hawaii",
  "uic flames": "illinois chicago", "illinois chicago flames": "illinois chicago",
  "omaha mavericks": "nebraska omaha", "kansas city roos": "kansas city",
  "sam houston bearkats": "sam houston st", "mcneese cowboys": "mcneese st", "nicholls colonels": "nicholls st",
  "grambling tigers": "grambling st", "alcorn braves": "alcorn st", "prairie view a and m panthers": "prairie view a and m",
  "charleston cougars": "college of charleston", "app st mountaineers": "appalachian st",
  "fiu panthers": "fiu", "florida international panthers": "fiu",
  "ut martin skyhawks": "tennessee martin", "tennessee martin skyhawks": "tennessee martin",
  "southern miss golden eagles": "southern miss", "umass minutemen": "massachusetts",
  "uncw seahawks": "unc wilmington", "nc wilmington seahawks": "unc wilmington", "north carolina wilmington seahawks": "unc wilmington",
  "unc greensboro spartans": "unc greensboro", "north carolina greensboro spartans": "unc greensboro",
  "unc asheville bulldogs": "unc asheville", "north carolina asheville bulldogs": "unc asheville",
  "st francis pa red flash": "st francis pa", "st francis brooklyn terriers": "st francis ny",
  "loyola chicago ramblers": "loyola chicago", "loyola marymount lions": "loyola marymount", "loyola md greyhounds": "loyola md",
  "california baptist lancers": "cal baptist", "long island university sharks": "liu", "liu sharks": "liu",
  "purdue fort wayne mastodons": "purdue fort wayne", "detroit mercy titans": "detroit mercy",
  "queens royals": "queens", "texas a and m corpus christi islanders": "texas a and m corpus christi",
  "se louisiana lions": "southeastern louisiana", "southeastern louisiana lions": "southeastern louisiana"
};
let ALIASES = Object.assign({}, ALIAS_SEED);
const MAP_STATS = { matched: {}, unmatched: {} };

function resolveTeam(oddsName, byTeamOpt) {
  const byTeam = byTeamOpt || (TORVIK && TORVIK.byTeam);
  if (!byTeam) return null;
  const n = normName(oddsName);
  if (ALIASES[n] && byTeam[ALIASES[n]]) { MAP_STATS.matched[oddsName] = ALIASES[n]; return byTeam[ALIASES[n]]; }
  if (byTeam[n]) { MAP_STATS.matched[oddsName] = n; return byTeam[n]; }
  // strip trailing mascot words (1–3 tokens)
  const toks = n.split(" ");
  for (let take = toks.length - 1; take >= Math.max(1, toks.length - 3); take--) {
    const cand = toks.slice(0, take).join(" ");
    if (byTeam[cand]) { MAP_STATS.matched[oddsName] = cand; return byTeam[cand]; }
  }
  // fuzzy: token-set Jaccard
  let best = null, bestScore = 0;
  const set = new Set(toks);
  for (const key of Object.keys(byTeam)) {
    const kt = key.split(" "); let inter = 0;
    kt.forEach(t => { if (set.has(t)) inter++; });
    const score = inter / (set.size + kt.length - inter);
    if (score > bestScore) { bestScore = score; best = key; }
  }
  if (bestScore >= 0.6) { MAP_STATS.matched[oddsName] = best + " (fuzzy)"; return byTeam[best]; }
  MAP_STATS.unmatched[oddsName] = 1;
  return null;
}

// ═══ MODEL (S2) ═══════════════════════════════════════════════════════════════
let NEUTRAL = {}; // gameId → 1 (admin-flagged; zeroes HCA)

function predict(homeR, awayR, neutral, avg) {
  const pace = homeR.adjt * awayR.adjt / avg.tempo;
  const effH = homeR.adjoe * awayR.adjde / avg.eff;
  const effA = awayR.adjoe * homeR.adjde / avg.eff;
  const hca = neutral ? 0 : CFG.HCA;
  const hPts = effH * pace / 100 + hca / 2;
  const aPts = effA * pace / 100 - hca / 2;
  return { hPts, aPts, margin: hPts - aPts, total: hPts + aPts, pace, pHomeML: normCdf((hPts - aPts) / CFG.SD) };
}

// per-market edges with line shopping across retail books; gates applied
function computeEdges(g, proj) {
  const TH = CFG.thresholds;
  const out = { ML: null, SPR: null, TOT: null };
  const gate = (n, min) => n >= min ? null : n + " bk";

  // ML — best retail price each side vs model prob
  {
    const reason = gate(g.nML, TH.BOOKS);
    if (reason) out.ML = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.mlA == null || b.mlH == null) return;
        [["home", b.mlH, proj.pHomeML], ["away", b.mlA, 1 - proj.pHomeML]].forEach(([side, ml, pm]) => {
          const e = pm - impProb(ml);
          if (!best || e > best.edge) best = { side, edge: e, odds: ml, book: k, pModel: pm };
        });
      });
      out.ML = best ? { ok: true, side: best.side, edge: best.edge, odds: best.odds, book: best.book, pModel: best.pModel,
        label: (best.side === "home" ? lastWord(g.home) : lastWord(g.away)).slice(0, 3).toUpperCase() + " " + (best.odds > 0 ? "+" + best.odds : best.odds),
        hot: best.edge * 100 >= TH.ML } : { ok: false, reason: "no prices" };
    }
  }
  // SPR — per-book line; P(home covers)=Φ((margin+sprH)/SD)
  {
    const reason = gate(g.nSPR, TH.BOOKS);
    if (reason) out.SPR = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.sprH == null || b.sprHJ == null || b.sprAJ == null) return;
        const pH = normCdf((proj.margin + b.sprH) / CFG.SD);
        [["home", b.sprH, b.sprHJ, pH], ["away", -b.sprH, b.sprAJ, 1 - pH]].forEach(([side, line, juice, pm]) => {
          const e = pm - impProb(juice);
          if (!best || e > best.edge) best = { side, line, juice, edge: e, book: k, pModel: pm };
        });
      });
      out.SPR = best ? { ok: true, side: best.side, edge: best.edge, line: best.line, juice: best.juice, book: best.book, pModel: best.pModel,
        label: (best.side === "home" ? lastWord(g.home) : lastWord(g.away)).slice(0, 3).toUpperCase() + " " + (best.line > 0 ? "+" + best.line : best.line),
        hot: best.edge * 100 >= TH.SPR } : { ok: false, reason: "no prices" };
    }
  }
  // TOT — per-book line; P(over)=Φ((total−line)/TOT_SD)
  {
    const reason = gate(g.nTOT, TH.BOOKS);
    if (reason) out.TOT = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.tot == null || b.overJ == null || b.underJ == null) return;
        const pO = normCdf((proj.total - b.tot) / CFG.TOT_SD);
        [["over", b.tot, b.overJ, pO], ["under", b.tot, b.underJ, 1 - pO]].forEach(([side, line, juice, pm]) => {
          const e = pm - impProb(juice);
          if (!best || e > best.edge) best = { side, line, juice, edge: e, book: k, pModel: pm };
        });
      });
      out.TOT = best ? { ok: true, side: best.side, edge: best.edge, line: best.line, juice: best.juice, book: best.book, pModel: best.pModel,
        label: (best.side === "over" ? "O" : "U") + " " + best.line,
        hot: best.edge * 100 >= TH.TOT } : { ok: false, reason: "no prices" };
    }
  }
  return out;
}
function lastWord(s) { return s ? s.split(" ").pop() : "?"; }

function assembleSlate(games) {
  const fresh = TORVIK && (Date.now() - TORVIK.fetchedAt) < CFG.RATINGS_MAX_AGE_H * 3600e3;
  let modeled = 0, lined = 0;
  const out = games.map(g => {
    const o = { id: g.id, away: g.away, home: g.home, commence: g.commence, nBooks: g.nBooks, nML: g.nML, nSPR: g.nSPR, nTOT: g.nTOT, book: g.book, sharp: g.sharp, neutral: !!NEUTRAL[g.id] };
    if (g.nBooks > 0) lined++;
    const hR = resolveTeam(g.home), aR = resolveTeam(g.away);
    if (hR) { o.hRank = hR.rank; o.hConf = hR.conf; }
    if (aR) { o.aRank = aR.rank; o.aConf = aR.conf; }
    if (!TORVIK) { o.modeled = false; o.modelReason = "ratings not loaded"; return o; }
    if (!fresh) { o.modeled = false; o.modelReason = "stale ratings"; return o; }
    if (!hR || !aR) { o.modeled = false; o.modelReason = "unrated: " + (!hR ? lastWord(g.home) : lastWord(g.away)); return o; }
    const proj = predict(hR, aR, o.neutral, TORVIK.avg);
    o.modeled = true; modeled++;
    o.proj = { hPts: proj.hPts, aPts: proj.aPts, margin: +proj.margin.toFixed(2), total: +proj.total.toFixed(2), pace: +proj.pace.toFixed(1), pHomeML: +proj.pHomeML.toFixed(4) };
    o.edges = computeEdges(g, proj);
    return o;
  });
  return { games: out, coverage: { games: games.length, lined, modeled } };
}

// ═══ S3 (v1.1 TICKET): PICKS · KELLY · TRACKER · CLV ════════════════════════
// One pick per game+market, locked at FIRST qualification (open-capture
// discipline). Stakes: fractional Kelly, 1u = 1% bankroll, clamped to
// [minU, maxU]. Tracker = single Redis key hb:tracker (capped 400 picks).
// CLV sign conventions (positive = pick beat the close):
//   SPR pts = pickLine − closeLineForSide   (home line = sprH; away = −sprH)
//   TOT pts = over: closeTot − pickLine ; under: pickLine − closeTot
//   ML  pp  = (pClose(side) − pSnap(side)) × 100, no-vig, sharp preferred
let TRACKER = { picks: [] };
let LASTSEEN = {}; // gameId → latest pre-tip snapshot (memory; refresh-driven)
let trackerDirty = false;
function saveTracker() {
  if (TRACKER.picks.length > 400) TRACKER.picks = TRACKER.picks.slice(-400);
  rSet("hb:tracker", TRACKER); trackerDirty = false;
}
function decOdds(am) { return am > 0 ? 1 + am / 100 : 1 + 100 / (-am); }
function kellyStake(p, am) {
  const b = decOdds(am) - 1, q = 1 - p;
  const f = (p * b - q) / b;
  if (f <= 0) return 0;
  const u = CFG.kelly.fraction * f * 100;
  return Math.min(CFG.kelly.maxU, Math.max(CFG.kelly.minU, Math.round(u * 100) / 100));
}
function snapOf(g) {
  return { sprH: g.book.sprH, tot: g.book.tot, pHome: g.book.pHome,
    sharp: { sprH: g.sharp.sprH, tot: g.sharp.tot, pHome: g.sharp.pHome } };
}
function ensurePick(g, o, mkt) {
  const pid = g.id + "|" + mkt;
  if (TRACKER.picks.some(p => p.pid === pid)) return null;
  const e = o.edges[mkt];
  if (e.pModel == null) return null;
  const odds = e.odds != null ? e.odds : e.juice;
  const stakeU = kellyStake(e.pModel, odds);
  if (!stakeU) return null;
  const pick = { pid, gameId: g.id, mkt, side: e.side, line: e.line != null ? e.line : null,
    odds, book: e.book, edge: +e.edge.toFixed(4), pModel: +e.pModel.toFixed(4), label: e.label,
    stakeU, away: g.away, home: g.home, commence: g.commence, date: todayKey(), at: Date.now(),
    snap: snapOf(g), close: null, status: "open", result: null, clv: null };
  TRACKER.picks.push(pick); trackerDirty = true;
  return pick;
}
function harvestPicks(asm, games) {
  const now = Date.now(); let made = 0;
  const byId = {}; games.forEach(g => { byId[g.id] = g; });
  asm.games.forEach(o => {
    if (!o.modeled) return;
    if (new Date(o.commence).getTime() <= now) return;
    ["ML", "SPR", "TOT"].forEach(mkt => {
      const e = o.edges[mkt];
      if (e && e.ok && e.hot && ensurePick(byId[o.id], o, mkt)) made++;
    });
  });
  if (trackerDirty) saveTracker();
  return made;
}
function updateLastSeen(games) {
  const now = Date.now();
  games.forEach(g => { if (new Date(g.commence).getTime() > now) LASTSEEN[g.id] = Object.assign({ ts: now }, snapOf(g)); });
}
function freezeDueCloses() {
  const now = Date.now(); let touched = false;
  TRACKER.picks.forEach(p => {
    if (!p.close && new Date(p.commence).getTime() <= now && LASTSEEN[p.gameId]) {
      p.close = Object.assign({}, LASTSEEN[p.gameId]);
      computeClv(p); touched = true;
    }
  });
  if (touched) { trackerDirty = true; saveTracker(); }
}
function computeClv(p) {
  if (!p.close) { p.clv = null; return; }
  const sC = p.close.sharp || {}, sS = (p.snap && p.snap.sharp) || {};
  if (p.mkt === "SPR") {
    const useSharp = sC.sprH != null && sS.sprH != null;
    const closeLine = useSharp ? sC.sprH : p.close.sprH;
    if (closeLine == null) { p.clv = null; return; }
    const closeForSide = p.side === "home" ? closeLine : -closeLine;
    const pts = +(p.line - closeForSide).toFixed(2);
    p.clv = { pts, src: useSharp ? "sharp" : "consensus", beat: pts > 0 };
  } else if (p.mkt === "TOT") {
    const useSharp = sC.tot != null && sS.tot != null;
    const closeTot = useSharp ? sC.tot : p.close.tot;
    if (closeTot == null) { p.clv = null; return; }
    const pts = +((p.side === "over" ? closeTot - p.line : p.line - closeTot)).toFixed(2);
    p.clv = { pts, src: useSharp ? "sharp" : "consensus", beat: pts > 0 };
  } else {
    const useSharp = sC.pHome != null && sS.pHome != null;
    const pc = useSharp ? sC.pHome : p.close.pHome;
    const ps = useSharp ? sS.pHome : p.snap.pHome;
    if (pc == null || ps == null) { p.clv = null; return; }
    const forSide = x => p.side === "home" ? x : 1 - x;
    const pp = +(((forSide(pc) - forSide(ps)) * 100)).toFixed(2);
    p.clv = { pp, src: useSharp ? "sharp" : "consensus", beat: pp > 0 };
  }
}
function gradePick(p, hScore, aScore) {
  const margin = hScore - aScore, total = hScore + aScore;
  let outcome;
  if (p.mkt === "ML") outcome = margin === 0 ? "push" : ((margin > 0) === (p.side === "home") ? "won" : "lost");
  else if (p.mkt === "SPR") { const d = (p.side === "home" ? margin : -margin) + p.line; outcome = d > 0 ? "won" : d < 0 ? "lost" : "push"; }
  else { const d = p.side === "over" ? total - p.line : p.line - total; outcome = d > 0 ? "won" : d < 0 ? "lost" : "push"; }
  const units = outcome === "won" ? +(p.stakeU * (decOdds(p.odds) - 1)).toFixed(3) : outcome === "lost" ? -p.stakeU : 0;
  p.status = outcome;
  p.result = { units, finalH: hScore, finalA: aScore, gradedAt: Date.now() };
}
function duePicks() {
  const lag = (CFG.GRADE_LAG_MIN || 120) * 60e3, now = Date.now();
  return TRACKER.picks.filter(p => p.status === "open" && new Date(p.commence).getTime() < now - lag);
}
function applyScoresToPicks(rows) {
  const byId = {}; (rows || []).forEach(r => { byId[r.id] = r; });
  let graded = 0;
  duePicks().forEach(p => {
    const r = byId[p.gameId];
    if (!r || !r.completed || !r.scores) return;
    let h = null, a = null;
    r.scores.forEach(s => { if (s.name === r.home_team) h = parseInt(s.score); if (s.name === r.away_team) a = parseInt(s.score); });
    if (h == null || a == null || isNaN(h) || isNaN(a)) return;
    if (!p.close && LASTSEEN[p.gameId]) p.close = Object.assign({}, LASTSEEN[p.gameId]);
    if (p.close && !p.clv) computeClv(p);
    gradePick(p, h, a); graded++;
  });
  if (graded) { trackerDirty = true; saveTracker(); }
  return { graded, pending: TRACKER.picks.filter(p => p.status === "open").length };
}
async function gradeOpenPicks() {
  if (!duePicks().length) return { graded: 0, pending: TRACKER.picks.filter(p => p.status === "open").length };
  let rows; try { rows = await getScores(); } catch (e) { return { graded: 0, error: e.message }; }
  return applyScoresToPicks(rows);
}
function computeRecord() {
  const mk = () => ({ n: 0, w: 0, l: 0, p: 0, open: 0, voided: 0, staked: 0, net: 0, clvN: 0, clvSum: 0, beatN: 0 });
  const rec = { ML: mk(), SPR: mk(), TOT: mk(), ALL: mk() };
  TRACKER.picks.forEach(pk => {
    [rec[pk.mkt], rec.ALL].forEach(r => {
      if (!r) return;
      if (pk.status === "void") { r.voided++; return; }
      r.n++;
      if (pk.status === "open") { r.open++; return; }
      r.staked += pk.stakeU; r.net += pk.result ? pk.result.units : 0;
      if (pk.status === "won") r.w++; else if (pk.status === "lost") r.l++; else r.p++;
      if (pk.clv) { r.clvN++; r.clvSum += (pk.clv.pts != null ? pk.clv.pts : pk.clv.pp); if (pk.clv.beat) r.beatN++; }
    });
  });
  Object.keys(rec).forEach(k => {
    const r = rec[k];
    r.roi = r.staked ? +(r.net / r.staked).toFixed(4) : null;
    r.net = +r.net.toFixed(2); r.staked = +r.staked.toFixed(2);
    r.avgClv = r.clvN ? +(r.clvSum / r.clvN).toFixed(2) : null;
    r.beat = r.clvN ? +(r.beatN / r.clvN).toFixed(3) : null;
    delete r.clvSum;
  });
  return rec;
}

// ═══ S4 (v1.2 ANCHOR): PINNACLE-ANCHORED +EV SCREEN ═════════════════════════
// Fair prob = Pinnacle no-vig. EV% = pFair × dec(retail odds) − 1.
// SPR/TOT are compared ONLY where the retail line exactly matches Pinnacle's
// line — mismatched lines are skipped, never approximated.
// STRONG = the best-priced book is an outlier vs the OTHER retail books by
// >= CFG.ev.strongGap implied points (stale-line signal); otherwise WEAK
// (whole retail market disagrees with Pinnacle — could be anchor lag).
// EV rows are a screen, not picks: nothing here enters the tracker.
function evPush(rows, g, mkt, side, line, fair, entries, modelP) {
  if (!entries.length) return;
  let best = null;
  entries.forEach(e => { if (!best || e.dec > best.dec) best = e; });
  const ev = fair * best.dec - 1;
  if (ev * 100 < CFG.ev.min) return;
  let gap = null, strong = false;
  const others = entries.filter(e => e !== best);
  if (others.length) {
    gap = +((mean(others.map(e => 1 / e.dec)) - 1 / best.dec) * 100).toFixed(2);
    strong = gap >= CFG.ev.strongGap;
  }
  rows.push({ gameId: g.id, away: g.away, home: g.home, commence: g.commence,
    mkt, side, line, book: best.book, odds: best.odds, evPct: +(ev * 100).toFixed(2),
    pFair: +fair.toFixed(4), gap, strong, nBooks: entries.length,
    model: modelP != null ? { p: +modelP.toFixed(4), agree: modelP > fair } : null });
}
function evScanGame(g, proj) {
  const rows = []; const anchored = { ML: false, SPR: false, TOT: false };
  const s = g.books[SHARP];
  if (!s) return { rows, anchored };
  if (s.mlA != null && s.mlH != null) {
    anchored.ML = true;
    const fair = noVigPair(s.mlA, s.mlH);
    const eA = [], eH = [];
    RETAIL.forEach(k => { const b = g.books[k]; if (!b) return;
      if (b.mlA != null) eA.push({ book: k, odds: b.mlA, dec: decOdds(b.mlA) });
      if (b.mlH != null) eH.push({ book: k, odds: b.mlH, dec: decOdds(b.mlH) }); });
    evPush(rows, g, "ML", "away", null, fair.pA, eA, proj ? 1 - proj.pHomeML : null);
    evPush(rows, g, "ML", "home", null, fair.pH, eH, proj ? proj.pHomeML : null);
  }
  if (s.sprH != null && s.sprHJ != null && s.sprAJ != null) {
    anchored.SPR = true;
    const fair = noVigPair(s.sprAJ, s.sprHJ); // pA = away cover, pH = home cover @ Pinnacle line
    const eA = [], eH = [];
    RETAIL.forEach(k => { const b = g.books[k]; if (!b || b.sprH !== s.sprH) return;
      if (b.sprAJ != null) eA.push({ book: k, odds: b.sprAJ, dec: decOdds(b.sprAJ) });
      if (b.sprHJ != null) eH.push({ book: k, odds: b.sprHJ, dec: decOdds(b.sprHJ) }); });
    const mH = proj ? normCdf((proj.margin + s.sprH) / CFG.SD) : null;
    evPush(rows, g, "SPR", "away", -s.sprH, fair.pA, eA, mH != null ? 1 - mH : null);
    evPush(rows, g, "SPR", "home", s.sprH, fair.pH, eH, mH);
  }
  if (s.tot != null && s.overJ != null && s.underJ != null) {
    anchored.TOT = true;
    const fair = noVigPair(s.overJ, s.underJ); // pA = over, pH = under
    const eO = [], eU = [];
    RETAIL.forEach(k => { const b = g.books[k]; if (!b || b.tot !== s.tot) return;
      if (b.overJ != null) eO.push({ book: k, odds: b.overJ, dec: decOdds(b.overJ) });
      if (b.underJ != null) eU.push({ book: k, odds: b.underJ, dec: decOdds(b.underJ) }); });
    const mO = proj ? normCdf((proj.total - s.tot) / CFG.TOT_SD) : null;
    evPush(rows, g, "TOT", "over", s.tot, fair.pA, eO, mO);
    evPush(rows, g, "TOT", "under", s.tot, fair.pH, eU, mO != null ? 1 - mO : null);
  }
  return { rows, anchored };
}
function evArbScan(g) {
  let bA = null, bH = null;
  BOOKS.forEach(k => { const b = g.books[k]; if (!b) return;
    if (b.mlA != null && (!bA || decOdds(b.mlA) > bA.dec)) bA = { book: k, odds: b.mlA, dec: decOdds(b.mlA) };
    if (b.mlH != null && (!bH || decOdds(b.mlH) > bH.dec)) bH = { book: k, odds: b.mlH, dec: decOdds(b.mlH) }; });
  if (!bA || !bH) return null;
  const sum = 1 / bA.dec + 1 / bH.dec;
  if (sum >= 1) return null;
  return { gameId: g.id, away: g.away, home: g.home, commence: g.commence,
    arbPct: +((1 - sum) * 100).toFixed(2), legA: { book: bA.book, odds: bA.odds }, legH: { book: bH.book, odds: bH.odds } };
}
function computeEv(games, asm) {
  const projById = {};
  ((asm && asm.games) || []).forEach(o => { if (o.modeled) projById[o.id] = o.proj; });
  const rows = [], arbs = [];
  let lined = 0, withSharp = 0;
  const anch = { ML: 0, SPR: 0, TOT: 0 };
  games.forEach(g => {
    if (!g.nBooks) return;
    lined++;
    if (g.books[SHARP]) withSharp++;
    const r = evScanGame(g, projById[g.id]);
    ["ML", "SPR", "TOT"].forEach(m => { if (r.anchored[m]) anch[m]++; });
    r.rows.forEach(x => rows.push(x));
    const a = evArbScan(g);
    if (a) arbs.push(a);
  });
  rows.sort((x, y) => y.evPct - x.evPct);
  return { rows, arbs, coverage: { lined, withSharp, anchored: anch, candidates: rows.length, strong: rows.filter(x => x.strong).length } };
}
function dailyPnl(picks) {
  const graded = picks.filter(p => ["won", "lost", "push"].includes(p.status));
  const byDate = {};
  graded.forEach(p => {
    const d = (p.commence || "").slice(0, 10) || "?";
    const r = (byDate[d] = byDate[d] || { d, net: 0, w: 0, l: 0, p: 0, n: 0 });
    r.n++; r.net += p.result.units;
    if (p.status === "won") r.w++; else if (p.status === "lost") r.l++; else r.p++;
  });
  let cum = 0;
  return Object.keys(byDate).sort().map(k => {
    const x = byDate[k]; cum += x.net;
    return { d: x.d, net: +x.net.toFixed(2), cum: +cum.toFixed(2), w: x.w, l: x.l, p: x.p, n: x.n };
  });
}

// ═══ S5 (v1.3 REWIND): LOOKAHEAD-FREE REPLAY CALIBRATION ════════════════════
// Pipeline: (1) ingest Odds API historical snapshots (30 credits each:
// 10 × 3 markets × 1 bookmaker-group) — budgeted, cursor-resumable, quota-
// guarded; (2) results via Torvik games adapter or manual CSV; (3) simulate:
// for each date, ratings come from Torvik's Time Machine archive AS OF that
// date (no lookahead), picks are made at the EARLY snapshot with the live
// computeEdges/kellyStake code, graded on finals, CLV'd against the LATE
// snapshot via the live computeClv. Report recommends SD/TOT_SD/HCA from
// residuals but NEVER applies them — observe before tuning.
function pad2(n) { return (n < 10 ? "0" : "") + n; }
function addDaysStr(d, n) { const t = new Date(d + "T12:00:00Z"); t.setUTCDate(t.getUTCDate() + n); return t.toISOString().slice(0, 10); }
function etDateOf(iso) { return new Date(new Date(iso).getTime() - 5 * 3600e3).toISOString().slice(0, 10); }
function snapIsosFor(dateStr, times) {
  return times.map(t => {
    const plus = /\+1$/.test(t); const hm = t.replace(/\+1$/, "");
    return (plus ? addDaysStr(dateStr, 1) : dateStr) + "T" + hm + ":00Z";
  });
}
const BOOK_IDX = {}; BOOKS.forEach((b, i) => { BOOK_IDX[b] = i; });
function packBooks(books) {
  const out = [];
  Object.keys(books).forEach(k => {
    if (BOOK_IDX[k] == null) return;
    const b = books[k];
    out.push([BOOK_IDX[k], b.mlA, b.mlH, b.sprA, b.sprAJ, b.sprH, b.sprHJ, b.tot, b.overJ, b.underJ]);
  });
  return out;
}
function unpackToGame(rec, packed) {
  const g = { id: rec.id || (rec.a + "@" + rec.h), away: rec.a, home: rec.h, commence: rec.c, books: {} };
  (packed || []).forEach(row => {
    g.books[BOOKS[row[0]]] = { mlA: row[1], mlH: row[2], sprA: row[3], sprAJ: row[4], sprH: row[5], sprHJ: row[6], tot: row[7], overJ: row[8], underJ: row[9] };
  });
  Object.assign(g, summarizeBooks(g.books));
  return g;
}
function gunzipJson(buf) { return JSON.parse(zlib.gunzipSync(buf).toString("utf8")); }
async function rGetJ(k) { const v = await rGet(k); if (v == null) return null; try { return typeof v === "string" ? JSON.parse(v) : v; } catch (e) { return null; } }
const rDel = k => rCmd(["DEL", k]);
const sleep = ms => new Promise(res => setTimeout(res, ms));
function replayCostFor(days, snaps) { return days * snaps * CFG.replay.costPerCall; }
function quotaAllows(cost) { return QUOTA.remaining == null || QUOTA.remaining >= cost + (CFG.replay.safetyCredits || 0); }

async function fetchHistoricalSnap(iso) {
  if (!quotaAllows(CFG.replay.costPerCall)) throw new Error("quota guard: " + QUOTA.remaining + " remaining < " + CFG.replay.costPerCall + " + safety " + CFG.replay.safetyCredits);
  const url = ODDS_HOST + "/v4/historical/sports/" + SPORT + "/odds?apiKey=" + ODDS_KEY +
    "&bookmakers=" + BOOKS.join(",") + "&markets=" + MARKETS + "&oddsFormat=american&dateFormat=iso&date=" + encodeURIComponent(iso);
  const maxRetries = CFG.replay.maxRetries != null ? CFG.replay.maxRetries : 3;
  for (let attempt = 0; ; attempt++) {
    const r = await fetch(url);
    // rate-limit / transient: back off and retry without aborting the run (429s do not consume quota)
    if (r.status === 429 || r.status >= 500) {
      if (attempt >= maxRetries) throw new Error((r.status === 429 ? "rate-limited (429)" : "server " + r.status) + " after " + maxRetries + " retries");
      await sleep(1000 * Math.pow(2, attempt));
      continue;
    }
    captureQuota(r);
    if (!r.ok) { let m = "historical HTTP " + r.status; try { const j = await r.json(); if (j.message) m += " — " + j.message; } catch (e) {} throw new Error(m); }
    const j = await r.json();
    return { ts: j.timestamp || iso, events: j.data || [] };
  }
}

const monthKey = (y, d) => "hb:replay:lines:" + y + ":" + d.slice(5, 7);
async function ingestDays(body) {
  const __rp = await redisProbe();
  if (!__rp.ok) return { ok: false, error: __rp.configured ? ("Redis credentials are present but commands are failing \u2014 refusing to spend credits (" + (__rp.error || "unknown") + "). See /api/debug/redis.") : "Redis not configured \u2014 replay ingest requires persistence (set UPSTASH_REDIS_URL / UPSTASH_REDIS_TOKEN). Refusing to spend credits.", redis: __rp, quota: QUOTA };
  const year = +body.year;
  let cur = await rGetJ("hb:replay:cursor:" + year) || {};
  const from = body.from || cur.from || (year - 1) + "-11-04";
  const to = body.to || cur.to || year + "-04-08";
  const times = (body.snapTimes && Array.isArray(body.snapTimes)) ? body.snapTimes : (cur.snapTimes || CFG.replay.snapTimes);
  let d = cur.ingestNext || from;
  const maxDays = Math.min(15, Math.max(1, body.days || 5));
  // hard per-run credit ceiling, enforced against the REAL quota delta (fail-safe)
  const cap = (typeof body.maxCredits === "number" && body.maxCredits > 0) ? body.maxCredits : Infinity;
  const startRem = QUOTA.remaining;
  const months = {}; let processed = 0, credits = 0, halted = null;
  const realSpent = () => (startRem != null && QUOTA.remaining != null) ? (startRem - QUOTA.remaining) : credits;
  while (d <= to && processed < maxDays) {
    for (const iso of snapIsosFor(d, times)) {
      const estNext = QUOTA.last != null ? QUOTA.last : CFG.replay.costPerCall;
      if (realSpent() + estNext > cap) { halted = "credit ceiling " + cap + " (spent ~" + realSpent() + ")"; break; }
      if (!quotaAllows(CFG.replay.costPerCall)) { halted = "quota guard at " + QUOTA.remaining; break; }
      let snap;
      try { snap = await fetchHistoricalSnap(iso); } catch (e) { halted = e.message; break; }
      credits += (QUOTA.last != null ? QUOTA.last : CFG.replay.costPerCall);
      const mk = monthKey(year, d);
      if (!months[mk]) months[mk] = await rGetJ(mk) || {};
      const day = months[mk][d] = months[mk][d] || {};
      snap.events.forEach(ev => {
        if (etDateOf(ev.commence_time) !== d) return;
        const g = normalizeGame(ev);
        if (!g.nBooks && !g.books[SHARP]) return;
        const rec = day[g.id] = day[g.id] || { a: g.away, h: g.home, c: g.commence, snaps: [] };
        rec.snaps.push({ t: snap.ts, b: packBooks(g.books) });
      });
      await sleep(CFG.replay.fetchDelayMs || 400);
    }
    if (halted) break;
    processed++; d = addDaysStr(d, 1);
  }
  for (const mk of Object.keys(months)) await rSet(mk, months[mk]);
  const runSpent = realSpent();
  cur = Object.assign(cur, { year, from, to, snapTimes: times, ingestNext: d, ingestedDays: (cur.ingestedDays || 0) + processed, credits: (cur.credits || 0) + credits });
  await rSet("hb:replay:cursor:" + year, cur);
  return { ok: !halted || processed > 0, processedDays: processed, nextDate: d, done: d > to, halted, creditsUsed: credits, realSpent: (startRem != null ? runSpent : null), totalCredits: cur.credits, quota: QUOTA };
}

// ── POINT-IN-TIME (TIME MACHINE) RATINGS STORE ──────────────────────────────
// Dated Torvik snapshots in Redis so the replay sim can use ratings as they stood on each
// game date, without the server reaching barttorvik (its bot challenge blocks server fetches).
// Populate via POST /api/admin/torvik/tm. timeMachineRatings() reads the nearest-prior stored
// snapshot per day; the live barttorvik fetch is only a fallback.
const TM_STORE = new Map();   // "year:ymd" -> built ratings (byTeam/avg/list)
const TM_INDEX = new Map();   // year -> { dates:[sorted ymd], at }
function tmPickNearest(dates, ymd) { let best = null; for (const dd of dates) { if (dd <= ymd && (best === null || dd > best)) best = dd; } return best; }
async function tmIndex(year, force) {
  const c = TM_INDEX.get(year);
  if (c && !force && Date.now() - c.at < 60000) return c.dates;
  const dates = (await rGetJ("hb:torvik:tmidx:" + year)) || [];
  TM_INDEX.set(year, { dates: dates, at: Date.now() });
  return dates;
}
async function tmNearest(year, ymd) { return tmPickNearest(await tmIndex(year), ymd); }
function tmBuildList(list, year, mode) {
  const byTeam = {};
  list.forEach(t => { byTeam[normName(t.team)] = t; });
  return { byTeam: byTeam, list: list, avg: { eff: mean(list.map(t => (t.adjoe + t.adjde) / 2)), tempo: mean(list.map(t => t.adjt)) }, year: year, mode: mode, fetchedAt: Date.now(), teams: list.length };
}
async function tmStoreBuild(year, ymd) {
  const k = year + ":" + ymd;
  if (TM_STORE.has(k)) return TM_STORE.get(k);
  const rec = await rGetJ("hb:torvik:tm:" + year + ":" + ymd);
  if (!rec || !rec.list || !rec.list.length) return null;
  const built = tmBuildList(rec.list, year, "tm-store:" + ymd);
  TM_STORE.set(k, built);
  if (TM_STORE.size > 12) TM_STORE.delete(TM_STORE.keys().next().value);
  return built;
}
async function tmStorePut(year, ymd, list) {
  await rSet("hb:torvik:tm:" + year + ":" + ymd, { list: list, teams: list.length, at: Date.now() });
  const dates = (await rGetJ("hb:torvik:tmidx:" + year)) || [];
  if (!dates.includes(ymd)) { dates.push(ymd); dates.sort(); await rSet("hb:torvik:tmidx:" + year, dates); }
  TM_INDEX.delete(year); TM_STORE.delete(year + ":" + ymd);
}
const TM_CACHE = new Map();
async function timeMachineRatings(dateStr, year) {
  const eff = addDaysStr(dateStr, -(CFG.replay.lagDays || 0));
  if (TM_CACHE.has(eff)) return TM_CACHE.get(eff);
  const ymd = eff.replace(/-/g, "");
  let out = null;
  // 1) point-in-time store: nearest-prior dated snapshot <= eff (no barttorvik dependency)
  try { const snapYmd = await tmNearest(year, ymd); if (snapYmd) out = await tmStoreBuild(year, snapYmd); } catch (e) {}
  // 2) fallback: live barttorvik time-machine fetch (may be blocked by their browser challenge)
  if (!out) for (const url of ["https://barttorvik.com/timemachine/team_results/" + ymd + "_team_results.json.gz",
                     "https://barttorvik.com/timemachine/team_results/" + ymd + "_team_results.json"]) {
    try {
      const r = await fetch(url, { headers: { "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", "Accept": "application/json,application/octet-stream,*/*" } });
      if (!r.ok) continue;
      const buf = await r.buffer();
      const payload = /\.gz$/.test(url) ? gunzipJson(buf) : JSON.parse(buf.toString("utf8"));
      const arr = Array.isArray(payload) ? payload : (payload.data || []);
      if (!arr.length) continue;
      const pa = ratingsFromArray(arr, null);
      if (!pa.colmap) continue;
      const built = buildTorvik(pa.rows, pa.colmap, year, "tm:" + eff);
      if (built) { out = built; tmStorePut(year, ymd, built.list).catch(function () {}); break; }
    } catch (e) {}
  }
  if (TM_CACHE.size > 4) TM_CACHE.delete(TM_CACHE.keys().next().value);
  TM_CACHE.set(eff, out);
  if (!out) await sleep(CFG.replay.fetchDelayMs || 250);
  return out;
}

// ── results adapters ──
function parseResultsCsvManual(text) {
  const tt = String(text == null ? "" : text).trim();
  let rows;
  if (tt[0] === "[" || tt[0] === "{") {
    try { const j = JSON.parse(tt); const arr = Array.isArray(j) ? j : (j.data || []); rows = (arr.length && !Array.isArray(arr[0])) ? arr.map(o => Object.values(o)) : arr; }
    catch (e) { rows = parseCsv(text); }
  } else rows = parseCsv(text);
  if (!rows || !rows.length) return null;
  const hd = rows[0].map(x => String(x).toLowerCase().replace(/[^a-z_]/g, ""));
  const ix = n => hd.indexOf(n);
  const m = { d: ix("date"), away: ix("away"), home: ix("home"), aPts: ix("away_pts") >= 0 ? ix("away_pts") : ix("awaypts"), hPts: ix("home_pts") >= 0 ? ix("home_pts") : ix("homepts"), neutral: ix("neutral") };
  if (m.d < 0 || m.away < 0 || m.home < 0 || m.aPts < 0 || m.hPts < 0) return parseTorvikGameStats(rows);
  return rows.slice(1).map(r => ({
    d: String(r[m.d]).slice(0, 10), away: String(r[m.away]).trim(), home: String(r[m.home]).trim(),
    aPts: parseInt(r[m.aPts]), hPts: parseInt(r[m.hPts]),
    neutral: m.neutral >= 0 ? /^(1|true|n|neutral)$/i.test(String(r[m.neutral]).trim()) : false
  })).filter(x => x.away && x.home && !isNaN(x.aPts) && !isNaN(x.hPts));
}
function detectGamesColumns(rows) {
  if (!rows || rows.length < 50) return null;
  const ncol = rows[0].length, cols = [];
  for (let c = 0; c < ncol; c++) {
    const vals = rows.map(r => String(r[c] == null ? "" : r[c]).trim());
    const nums = vals.map(v => parseFloat(v)).filter(v => !isNaN(v));
    cols.push({ c,
      dateFrac: vals.filter(v => /^\d{4}-\d{2}-\d{2}|^\d{8}$|^\d{1,2}\/\d{1,2}(\/\d{2,4})?$/.test(v)).length / vals.length,
      resFrac: vals.filter(v => /^[WL][, ]?\s*\d{2,3}-\d{2,3}/.test(v)).length / vals.length,
      venue: (() => { const ds = new Set(vals.map(v => v.toUpperCase())); if (ds.size > 4) return false; for (const v of ds) if (!["H", "A", "N", "HOME", "AWAY", "NEUTRAL", "0", "1", ""].includes(v)) return false; return ds.size >= 2; })(),
      scoreLike: nums.length / vals.length > 0.95 && mean(nums) >= 40 && mean(nums) <= 130,
      strDistinct: (vals.filter(v => /[a-zA-Z]/.test(v) && isNaN(parseFloat(v))).length / vals.length > 0.9) ? new Set(vals).size : 0
    });
  }
  const date = cols.filter(x => x.dateFrac > 0.9).sort((a, b) => b.dateFrac - a.dateFrac)[0];
  if (!date) return null;
  const teams = cols.filter(x => x.strDistinct >= 150).sort((a, b) => b.strDistinct - a.strDistinct);
  const result = cols.filter(x => x.resFrac > 0.8).sort((a, b) => b.resFrac - a.resFrac)[0];
  const venue = cols.find(x => x.venue);
  if (result && teams.length >= 2) {
    return { mode: "B", date: date.c, team: Math.min(teams[0].c, teams[1].c), opp: Math.max(teams[0].c, teams[1].c), result: result.c, venue: venue ? venue.c : null };
  }
  const scores = cols.filter(x => x.scoreLike);
  if (teams.length >= 2 && scores.length >= 2) {
    return { mode: "A", date: date.c, away: Math.min(teams[0].c, teams[1].c), home: Math.max(teams[0].c, teams[1].c), aPts: Math.min(scores[0].c, scores[1].c), hPts: Math.max(scores[0].c, scores[1].c), venue: venue ? venue.c : null };
  }
  return null;
}
function normalizeDateStr(v) {
  v = String(v).trim();
  if (/^\d{4}-\d{2}-\d{2}/.test(v)) return v.slice(0, 10);
  if (/^\d{8}$/.test(v)) return v.slice(0, 4) + "-" + v.slice(4, 6) + "-" + v.slice(6, 8);
  const m = v.match(/^(\d{1,2})\/(\d{1,2})\/(\d{2,4})/);
  if (m) { const yy = m[3].length === 2 ? "20" + m[3] : m[3]; return yy + "-" + pad2(+m[1]) + "-" + pad2(+m[2]); }
  return v;
}
function normalizeGameRows(rows, det) {
  const out = [], seen = {};
  rows.forEach(r => {
    let row = null;
    if (det.mode === "B") {
      const res = String(r[det.result] || "").match(/^([WL])[, ]?\s*(\d{2,3})-(\d{2,3})/);
      if (!res) return;
      const team = String(r[det.team]).trim(), opp = String(r[det.opp]).trim();
      const tPts = +res[2], oPts = +res[3];
      const v = det.venue != null ? String(r[det.venue]).trim().toUpperCase() : "H";
      const neutral = v === "N" || v === "NEUTRAL";
      const home = (v === "A" || v === "AWAY") ? opp : team;
      const hPts = home === team ? tPts : oPts, aPts = home === team ? oPts : tPts;
      const away = home === team ? opp : team;
      row = { d: normalizeDateStr(r[det.date]), away, home, aPts, hPts, neutral };
    } else {
      const v = det.venue != null ? String(r[det.venue]).trim().toUpperCase() : "";
      row = { d: normalizeDateStr(r[det.date]), away: String(r[det.away]).trim(), home: String(r[det.home]).trim(),
        aPts: parseInt(r[det.aPts]), hPts: parseInt(r[det.hPts]), neutral: v === "N" || v === "NEUTRAL" || v === "1" };
    }
    if (!row || !row.away || !row.home || isNaN(row.aPts) || isNaN(row.hPts)) return;
    const key = row.d + "|" + [normName(row.away), normName(row.home)].sort().join("|");
    if (seen[key]) return;
    seen[key] = 1; out.push(row);
  });
  return out;
}
// barttorvik getgamestats.php top-level row (~31 cols): date(0), ?(1), team(2), teamConf(3),
// opp(4), venue(5: H/A/N from team's POV), result(6: "W/L, winnerPts-loserPts"), efficiency
// stats…, fused gameID(24), coaches(25,26), win-prob(28), nested box-score string(29), …
// Only 0,2,4,5,6 are needed. Each game appears twice (once per team's POV); dedup by date+pair.
function parseTorvikGameStats(rows) {
  if (!rows || rows.length < 100) return null;
  const DATE = 0, TEAM = 2, OPP = 4, VENUE = 5, RESULT = 6;
  const cl = x => String(x == null ? "" : x).replace(/^[\s\[\]"']+|[\s\[\]"']+$/g, "").trim();
  const RE = /([WL])[\s,]+(\d{2,3})\s*-\s*(\d{2,3})/;
  const parseRow = r => {
    if (!Array.isArray(r) || r.length <= RESULT) return null;
    const d = normalizeDateStr(cl(r[DATE]));
    if (!/^\d{4}-\d{2}-\d{2}$/.test(d)) return null;
    const team = cl(r[TEAM]), opp = cl(r[OPP]);
    if (!team || !opp || !isNaN(+team) || !isNaN(+opp)) return null;
    const m = cl(r[RESULT]).match(RE);
    if (!m) return null;
    const wl = m[1], hi = +m[2], lo = +m[3];
    if (!(hi >= 20 && hi <= 250 && lo >= 10 && lo <= 250)) return null;
    const teamPts = wl === "W" ? hi : lo, oppPts = wl === "W" ? lo : hi;
    const v = cl(r[VENUE]).toUpperCase(), neutral = v === "N" || v === "NEUTRAL";
    let home, away, hPts, aPts;
    if (v === "A" || v === "AWAY") { home = opp; away = team; hPts = oppPts; aPts = teamPts; }
    else { home = team; away = opp; hPts = teamPts; aPts = oppPts; }
    return { d: d, home: home, away: away, hPts: hPts, aPts: aPts, neutral: neutral };
  };
  const sample = rows.slice(0, 300).filter(r => Array.isArray(r) && r.length > RESULT);
  if (sample.length < 50 || sample.filter(r => parseRow(r)).length < sample.length * 0.7) return null;
  const out = [], seen = {};
  for (const r of rows) {
    const g = parseRow(r);
    if (!g) continue;
    const key = g.d + "|" + [normName(g.home), normName(g.away)].sort().join("|");
    if (seen[key]) continue;
    seen[key] = 1;
    out.push(g);
  }
  return out.length >= 100 ? out : null;
}
async function fetchTorvikGames(year) {
  for (const mode of ["csv", "json"]) {
    try {
      const url = "https://barttorvik.com/getgamestats.php?year=" + year + (mode === "csv" ? "&csv=1" : "&json=1");
      const r = await fetch(url, { headers: { "User-Agent": "hoopsbet/1.3 (personal analytics)" } });
      if (!r.ok) continue;
      let rows;
      const txt = await r.text(), tt = txt.trim();
      if (tt[0] === "[" || tt[0] === "{") {
        try { const j = JSON.parse(tt); const arr = Array.isArray(j) ? j : (j.data || []); rows = (arr.length && !Array.isArray(arr[0])) ? arr.map(o => Object.values(o)) : arr; }
        catch (e) { rows = parseCsv(txt); }
      } else rows = parseCsv(txt);
      if (!rows || rows.length < 100) continue;
      const tg = parseTorvikGameStats(rows);
      if (tg && tg.length >= 100) { await rSet("hb:replay:games:" + year, { games: tg, det: "torvik-getgamestats", mode, fetchedAt: Date.now(), sample: rows.slice(0, 2) }); return { ok: true, games: tg.length, mode, det: "torvik-getgamestats", sample: tg[0] }; }
      let det = detectGamesColumns(rows), data = rows;
      if (!det) { det = detectGamesColumns(rows.slice(1)); data = rows.slice(1); }
      if (!det) continue;
      const games = normalizeGameRows(data, det);
      if (games.length < 100) continue;
      await rSet("hb:replay:games:" + year, { games, det, mode, fetchedAt: Date.now(), sample: rows.slice(0, 2) });
      return { ok: true, games: games.length, mode, det, sample: games[0] };
    } catch (e) {}
  }
  return { ok: false, error: "could not fetch/parse Torvik games — POST a manual CSV (date,away,home,away_pts,home_pts,neutral) to /api/replay/results" };
}

// ── aggregates + day simulation (pure core) ──
function stAdd(s, v) { s.n++; s.sum += v; s.sum2 += v * v; }
function stView(s) { if (!s.n) return null; const m = s.sum / s.n; return { n: s.n, mean: +m.toFixed(3), sd: +Math.sqrt(Math.max(0, s.sum2 / s.n - m * m)).toFixed(3) }; }
function newAgg(year) {
  const pk = () => ({ n: 0, w: 0, l: 0, p: 0, units: 0, staked: 0, clvN: 0, clvSum: 0, beatN: 0 });
  const st = () => ({ n: 0, sum: 0, sum2: 0 });
  const swb = () => ({ n: 0, w: 0, l: 0, p: 0, units: 0 });
  return { year, startedAt: Date.now(), cfg: { HCA: CFG.HCA, SD: CFG.SD, TOT_SD: CFG.TOT_SD, thresholds: Object.assign({}, CFG.thresholds), kelly: Object.assign({}, CFG.kelly) },
    days: 0, lineGames: 0, simmed: 0, unmatchedRatings: {}, unmatchedResults: 0, ratingsMissingDays: 0, resultDateShift: 0, unmatchedSample: [], noPreTip: 0, sameSnap: 0,
    picks: { ML: pk(), SPR: pk(), TOT: pk(), ALL: pk() },
    sweep: { "2-4": swb(), "4-6": swb(), "6-8": swb(), "8+": swb() },
    cal: { buckets: Array.from({ length: 10 }, () => ({ n: 0, w: 0, pSum: 0 })), brierSum: 0, brierN: 0 },
    resid: { margin: st(), home: st(), neutral: st(), total: st() },
    vsClose: { n: 0, absSum: 0, sideN: 0, sideHit: 0 } };
}
function mkReplayPick(rec, e, mkt) {
  const odds = e.odds != null ? e.odds : e.juice;
  const stakeU = kellyStake(e.pModel, odds);
  if (!stakeU) return null;
  return { pid: "R|" + rec.a + "@" + rec.h + "|" + mkt, mkt, side: e.side, line: e.line != null ? e.line : null,
    odds, book: e.book, edge: e.edge, pModel: e.pModel, stakeU, away: rec.a, home: rec.h, commence: rec.c,
    snap: null, close: null, status: "open", result: null, clv: null };
}
function simDate(dateStr, tm, byDateMap, dayLines, agg) {
  agg.days++;
  // Odds line dates are UTC while Torvik result dates are game-local, so a game can land a day off.
  // Build the result map from the day and its neighbours, preferring the exact date (added first).
  const resMap = {};
  [dateStr, addDaysStr(dateStr, -1), addDaysStr(dateStr, 1)].forEach(dd => {
    (byDateMap[dd] || []).forEach(g => {
      const gh = resolveTeam(g.home, tm.byTeam), ga = resolveTeam(g.away, tm.byTeam);
      const k = (gh && ga) ? (normName(gh.team) + "|" + normName(ga.team)) : (normName(g.home) + "|" + normName(g.away));
      if (!(k in resMap)) resMap[k] = g;
    });
  });
  Object.keys(dayLines || {}).forEach(id => {
    const rec = dayLines[id]; rec.id = id;
    agg.lineGames++;
    const rH = resolveTeam(rec.h, tm.byTeam), rA = resolveTeam(rec.a, tm.byTeam);
    if (!rH || !rA) { agg.unmatchedRatings[!rH ? rec.h : rec.a] = 1; return; }
    let res = resMap[normName(rH.team) + "|" + normName(rA.team)], swapped = false;
    if (!res) { res = resMap[normName(rA.team) + "|" + normName(rH.team)]; swapped = !!res; }
    if (!res) { agg.unmatchedResults++; if (agg.unmatchedSample.length < 3) agg.unmatchedSample.push({ want: normName(rH.team) + "|" + normName(rA.team), have: Object.keys(resMap).slice(0, 5) }); return; }
    if (res.d && res.d !== dateStr) agg.resultDateShift++;
    const hPts = swapped ? res.aPts : res.hPts, aPts = swapped ? res.hPts : res.aPts;
    const neutral = res.neutral || swapped;
    const proj = predict(rH, rA, neutral, tm.avg);
    agg.simmed++;
    // calibration on every simmed game
    const homeWon = hPts > aPts ? 1 : 0;
    const bi = Math.min(9, Math.floor(proj.pHomeML * 10));
    const bk2 = agg.cal.buckets[bi]; bk2.n++; bk2.w += homeWon; bk2.pSum += proj.pHomeML;
    agg.cal.brierSum += Math.pow(proj.pHomeML - homeWon, 2); agg.cal.brierN++;
    const mResid = proj.margin - (hPts - aPts), tResid = proj.total - (hPts + aPts);
    stAdd(agg.resid.margin, mResid); stAdd(agg.resid.total, tResid);
    stAdd(neutral ? agg.resid.neutral : agg.resid.home, mResid);
    // snapshots
    const snaps = (rec.snaps || []).slice().sort((x, y) => x.t < y.t ? -1 : 1);
    if (!snaps.length) return;
    const usable = snaps.filter(s => s.t <= rec.c);
    const closeS = usable.length ? usable[usable.length - 1] : snaps[snaps.length - 1];
    const gC = unpackToGame(rec, closeS.b);
    if (gC.book.sprH != null) { agg.vsClose.n++; agg.vsClose.absSum += Math.abs((-proj.margin) - gC.book.sprH); }
    if (gC.book.pHome != null) { agg.vsClose.sideN++; if ((proj.pHomeML > 0.5) === (gC.book.pHome > 0.5)) agg.vsClose.sideHit++; }
    if (!usable.length) { agg.noPreTip++; return; }
    const openS = usable[0];
    const gO = unpackToGame(rec, openS.b);
    const edges = computeEdges(gO, proj);
    ["ML", "SPR", "TOT"].forEach(mkt => {
      const e = edges[mkt];
      if (!e || !e.ok) return;
      // threshold sweep: hypothetical flat 1u at every edge >= 2%
      if (e.edge * 100 >= 2) {
        const key = e.edge * 100 < 4 ? "2-4" : e.edge * 100 < 6 ? "4-6" : e.edge * 100 < 8 ? "6-8" : "8+";
        const scratch = { mkt, side: e.side, line: e.line != null ? e.line : null, odds: e.odds != null ? e.odds : e.juice, stakeU: 1, status: "open", result: null };
        gradePick(scratch, hPts, aPts);
        const sw = agg.sweep[key]; sw.n++; sw.units += scratch.result.units;
        if (scratch.status === "won") sw.w++; else if (scratch.status === "lost") sw.l++; else sw.p++;
      }
      if (!e.hot) return;
      const pick = mkReplayPick(rec, e, mkt);
      if (!pick) return;
      pick.snap = snapOf(gO);
      if (closeS.t !== openS.t) { pick.close = Object.assign({ ts: closeS.t }, snapOf(gC)); computeClv(pick); }
      else agg.sameSnap++;
      gradePick(pick, hPts, aPts);
      [agg.picks[mkt], agg.picks.ALL].forEach(r => {
        r.n++; r.staked += pick.stakeU; r.units += pick.result.units;
        if (pick.status === "won") r.w++; else if (pick.status === "lost") r.l++; else r.p++;
        if (pick.clv) { r.clvN++; r.clvSum += (pick.clv.pts != null ? pick.clv.pts : pick.clv.pp); if (pick.clv.beat) r.beatN++; }
      });
    });
  });
}
async function simulateDays(body) {
  const year = +body.year;
  const cur = await rGetJ("hb:replay:cursor:" + year);
  if (!cur || !cur.from) return { ok: false, error: "no ingest cursor — run /api/replay/ingest first" };
  const gamesBlob = await rGetJ("hb:replay:games:" + year);
  if (!gamesBlob || !gamesBlob.games) return { ok: false, error: "no results loaded — POST /api/replay/results first" };
  const byDate = {};
  gamesBlob.games.forEach(g => { (byDate[g.d] = byDate[g.d] || []).push(g); });
  let agg;
  if (body.restart) { agg = newAgg(year); cur.simNext = cur.from; }
  else { agg = await rGetJ("hb:replay:agg:" + year) || newAgg(year); }
  let d = cur.simNext || cur.from;
  const end = cur.ingestNext ? addDaysStr(cur.ingestNext, -1) : cur.to;
  const maxDays = Math.min(30, Math.max(1, body.days || 10));
  let processed = 0; const monthsCache = {};
  while (d <= end && processed < maxDays) {
    const mk = monthKey(year, d);
    if (!(mk in monthsCache)) monthsCache[mk] = await rGetJ(mk) || {};
    const dayLines = monthsCache[mk][d];
    if (dayLines && Object.keys(dayLines).length) {
      const tm = await timeMachineRatings(d, year);
      if (!tm) agg.ratingsMissingDays++;
      else simDate(d, tm, byDate, dayLines, agg);
    }
    processed++; d = addDaysStr(d, 1);
    if (processed % 5 === 0) { await rSet("hb:replay:agg:" + year, agg); cur.simNext = d; await rSet("hb:replay:cursor:" + year, cur); }
  }
  cur.simNext = d;
  await rSet("hb:replay:agg:" + year, agg);
  await rSet("hb:replay:cursor:" + year, cur);
  return { ok: true, processedDays: processed, nextDate: d, done: d > end, simmed: agg.simmed, days: agg.days, lineGames: agg.lineGames, ratingsMissingDays: agg.ratingsMissingDays, unmatchedRatings: Object.keys(agg.unmatchedRatings).length, unmatchedResults: agg.unmatchedResults, resultDateShift: agg.resultDateShift, unmatchedSample: agg.unmatchedSample };
}
function buildReport(agg) {
  if (!agg) return null;
  const pview = r => ({ n: r.n, record: r.w + "-" + r.l + (r.p ? "-" + r.p : ""), units: +r.units.toFixed(2), staked: +r.staked.toFixed(2),
    roi: r.staked ? +(r.units / r.staked).toFixed(4) : null, avgClv: r.clvN ? +(r.clvSum / r.clvN).toFixed(2) : null,
    clvBeat: r.clvN ? +(r.beatN / r.clvN).toFixed(3) : null, clvN: r.clvN });
  const m = stView(agg.resid.margin), t = stView(agg.resid.total), h = stView(agg.resid.home), nn = stView(agg.resid.neutral);
  return { year: agg.year, cfgAtSim: agg.cfg,
    coverage: { days: agg.days, lineGames: agg.lineGames, simmed: agg.simmed, ratingsMissingDays: agg.ratingsMissingDays,
      unmatchedResults: agg.unmatchedResults, unmatchedRatings: Object.keys(agg.unmatchedRatings).length, noPreTip: agg.noPreTip, sameSnap: agg.sameSnap },
    picks: { ML: pview(agg.picks.ML), SPR: pview(agg.picks.SPR), TOT: pview(agg.picks.TOT), ALL: pview(agg.picks.ALL) },
    sweep: Object.keys(agg.sweep).reduce((o, k) => { const s = agg.sweep[k]; o[k] = { n: s.n, record: s.w + "-" + s.l + (s.p ? "-" + s.p : ""), units: +s.units.toFixed(2), roi: s.n ? +(s.units / s.n).toFixed(4) : null }; return o; }, {}),
    calibration: { brier: agg.cal.brierN ? +(agg.cal.brierSum / agg.cal.brierN).toFixed(4) : null,
      buckets: agg.cal.buckets.map((b, i) => ({ range: (i * 10) + "-" + (i * 10 + 10), n: b.n, predicted: b.n ? +(b.pSum / b.n).toFixed(3) : null, actual: b.n ? +(b.w / b.n).toFixed(3) : null })).filter(b => b.n > 0) },
    residuals: { margin: m, total: t, homeGames: h, neutralGames: nn },
    vsClose: { spreadMAE: agg.vsClose.n ? +(agg.vsClose.absSum / agg.vsClose.n).toFixed(2) : null, sideAgree: agg.vsClose.sideN ? +(agg.vsClose.sideHit / agg.vsClose.sideN).toFixed(3) : null, n: agg.vsClose.n },
    recommend: { SD: m ? m.sd : null, TOT_SD: t ? t.sd : null, totalsBias: t ? t.mean : null,
      HCA_implied: h ? +(agg.cfg.HCA - h.mean).toFixed(2) : null, neutralSanity: nn ? nn.mean : null,
      note: "Display-only. Positive totalsBias = model projects high. Apply deliberately via POST /api/admin/model after review — observe before tuning." } };
}


// ═══ ROUTES ═══════════════════════════════════════════════════════════════════
const month = () => new Date().getMonth() + 1;
const OFFSEASON_NOTE = "NCAAB season runs November \u2013 April. The data layer is live; the slate populates when books post lines.";

app.get("/api/health", async (q, r) => {
  const rp = await redisProbe();
  r.json({
    ok: true, app: "hoopsbet", version: VERSION,
    quota: QUOTA, oddsKey: !!ODDS_KEY, lastOddsError: LAST_ODDS_ERR,
    slateAgeMin: slateCache.t ? Math.round((Date.now() - slateCache.t) / 60e3) : null,
    seasonActive: !isOffseason(), lastSlateGames: LAST_SLATE_GAMES,
    torvik: TORVIK ? { year: TORVIK.year, teams: TORVIK.teams, mode: TORVIK.mode, ageMin: Math.round((Date.now() - TORVIK.fetchedAt) / 60e3) } : { error: TORVIK_ERR || "not loaded" },
    tracker: { picks: TRACKER.picks.length, open: TRACKER.picks.filter(p => p.status === "open").length },
    redis: rp.ok, redisInfo: rp.ok ? undefined : rp
  });
});

app.get("/api/slate", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: true, games: [], coverage: { games: 0, lined: 0, modeled: 0 }, thresholds: CFG.thresholds, note: "ODDS_API_KEY not set \u2014 add it in the Render dashboard.", quota: QUOTA });
    await fetchTorvik();
    const games = await getSlate(q.query.force === "1");
    const asm = assembleSlate(games);
    freezeDueCloses();
    harvestPicks(asm, games);
    const pickMap = {};
    TRACKER.picks.forEach(p => { if (p.status !== "void") (pickMap[p.gameId] = pickMap[p.gameId] || []).push(p.mkt); });
    asm.games.forEach(o => { if (pickMap[o.id]) o.picks = pickMap[o.id]; });
    asm.coverage.picksToday = TRACKER.picks.filter(p => p.date === todayKey()).length;
    r.json(Object.assign({ ok: true, generatedAt: slateCache.t, thresholds: CFG.thresholds, quota: QUOTA, note: (!games.length && isOffseason()) ? OFFSEASON_NOTE : undefined }, asm));
  } catch (e) { r.status(500).json({ ok: false, error: e.message, quota: QUOTA }); }
});

app.get("/api/scores", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: true, games: [], note: "ODDS_API_KEY not set" });
    r.json({ ok: true, games: await getScores() });
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.get("/api/ratings", async (q, r) => {
  try {
    await fetchTorvik(q.query.year ? +q.query.year : null);
    if (!TORVIK) return r.json({ ok: false, error: TORVIK_ERR || "torvik unavailable" });
    let list = TORVIK.list;
    if (q.query.conf) list = list.filter(t => t.conf === q.query.conf);
    const top = q.query.top ? +q.query.top : 50;
    r.json({ ok: true, year: TORVIK.year, mode: TORVIK.mode, avg: TORVIK.avg, teams: list.slice(0, top) });
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.get("/api/debug/odds", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ error: "ODDS_API_KEY not set" });
    const raw = await fetchOddsRaw();
    const perBook = {};
    raw.forEach(ev => (ev.bookmakers || []).forEach(b => { perBook[b.key] = (perBook[b.key] || 0) + 1; }));
    r.json({ http: 200, events: raw.length, quota: QUOTA, booksRequested: BOOKS, perBookGameCounts: perBook, sample: raw[0] || null });
  } catch (e) { r.json({ error: e.message, quota: QUOTA }); }
});

app.get("/api/debug/torvik", async (q, r) => {
  await fetchTorvik(q.query.year ? +q.query.year : null, q.query.force === "1");
  r.json({
    locked: TORVIK_LOCK, error: TORVIK_ERR, rawSample: TORVIK_RAW_SAMPLE,
    parsed: TORVIK ? { year: TORVIK.year, mode: TORVIK.mode, teams: TORVIK.teams, avg: TORVIK.avg, top3: TORVIK.list.slice(0, 3) } : null,
    overrideHint: "POST /api/admin/torvikmap {mode:'csv'|'json', colmap:{team,conf,adjoe,adjde,adjt,barthag}} if detection misfires"
  });
});

app.get("/api/debug/redis", async (q, r) => { r.json(await redisProbe()); });
app.get("/api/debug/cursor", async (q, r) => { const year = +(q.query.year || seasonYear()); r.json({ year, cursor: await rGetJ("hb:replay:cursor:" + year), redis: await redisProbe() }); });
app.get("/api/replay/debug/rawresults", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const out = { year };
  for (const mode of ["csv", "json"]) {
    try {
      const url = "https://barttorvik.com/getgamestats.php?year=" + year + (mode === "csv" ? "&csv=1" : "&json=1");
      const resp = await fetch(url, { headers: { "User-Agent": "hoopsbet/1.3 (personal analytics)" } });
      const txt = await resp.text(), tt = txt.trim();
      let rows = null, via = "csv", perr = null;
      if (tt[0] === "[" || tt[0] === "{") {
        try { const j = JSON.parse(tt); const arr = Array.isArray(j) ? j : (j.data || []); rows = (arr.length && !Array.isArray(arr[0])) ? arr.map(o => Object.values(o)) : arr; via = "json"; }
        catch (e) { perr = e.message; rows = parseCsv(txt); via = "csv-fallback"; }
      } else rows = parseCsv(txt);
      const tg = parseTorvikGameStats(rows);
      const det = detectGamesColumns(rows);
      out[mode] = {
        httpStatus: resp.status,
        contentType: (resp.headers && resp.headers.get) ? resp.headers.get("content-type") : null,
        bytes: txt.length, firstChars: tt.slice(0, 4), rawHead: txt.slice(0, 600),
        parsedVia: via, jsonParseError: perr,
        rowCount: rows ? rows.length : null,
        row0Len: (rows && rows[0] != null) ? (Array.isArray(rows[0]) ? rows[0].length : ("notArray:" + typeof rows[0])) : null,
        row0_first6: (rows && Array.isArray(rows[0])) ? rows[0].slice(0, 6) : null,
        row0_col18_col33: (rows && Array.isArray(rows[0])) ? [rows[0][18], rows[0][33]] : null,
        row1_first6: (rows && Array.isArray(rows[1])) ? rows[1].slice(0, 6) : null,
        torvikParsed: tg ? tg.length : 0, torvikSample: tg ? tg[0] : null,
        detectResult: det
      };
    } catch (e) { out[mode] = { fetchError: e.message }; }
  }
  r.json(out);
});
app.get("/api/debug/teammap", (q, r) => {
  const um = Object.keys(MAP_STATS.unmatched);
  if (q.query.summary) return r.json({ matched: Object.keys(MAP_STATS.matched).length, unmatched: um.length });
  r.json({ matched: MAP_STATS.matched, unmatched: um, aliasCount: Object.keys(ALIASES).length, hint: "POST /api/admin/alias {odds:'<Odds API name>', torvik:'<Torvik name>'}" });
});

app.post("/api/admin/alias", async (q, r) => {
  const { odds, torvik } = q.body || {};
  if (!odds || !torvik) return r.status(400).json({ ok: false, error: "need odds + torvik" });
  ALIASES[normName(odds)] = normName(torvik);
  delete MAP_STATS.unmatched[odds];
  await rSet("hb:aliases", ALIASES);
  r.json({ ok: true, aliases: Object.keys(ALIASES).length });
});

app.post("/api/admin/torvikmap", async (q, r) => {
  const { mode, colmap } = q.body || {};
  if (!mode || !colmap) return r.status(400).json({ ok: false, error: "need mode + colmap" });
  TORVIK_LOCK = { mode, colmap }; TORVIK = null;
  await rSet("hb:torvik:lock", TORVIK_LOCK);
  await fetchTorvik(null, true);
  r.json({ ok: !!TORVIK, torvik: TORVIK ? { teams: TORVIK.teams, mode: TORVIK.mode } : TORVIK_ERR });
});
app.post("/api/admin/torvik", async (q, r) => {
  const b = q.body || {};
  const data = typeof b.data === "string" ? b.data.trim() : "";
  if (!data) return r.status(400).json({ ok: false, error: "need data \u2014 paste the barttorvik CSV or JSON" });
  const year = +b.year || seasonYear();
  let mode = b.mode || "auto";
  if (mode === "auto") mode = (data[0] === "[" || data[0] === "{") ? "json" : "csv";
  let rows, colmap;
  try {
    if (mode === "json") {
      const j = JSON.parse(data);
      const arr = Array.isArray(j) ? j : (j.data || []);
      if (!arr.length) return r.json({ ok: false, error: "JSON parsed but contained no rows" });
      const pa = ratingsFromArray(arr, b.colmap || null);
      rows = pa.rows; colmap = b.colmap || pa.colmap;
    } else {
      const all = parseCsv(data);
      if (all.length < 50) return r.json({ ok: false, error: "CSV too short (" + all.length + " rows) \u2014 paste the full ratings table" });
      const hc = headerColmap(all[0]);
      colmap = b.colmap || hc;
      rows = hc ? all.slice(1) : all;
      if (!colmap) colmap = detectColumns(rows);
    }
  } catch (e) { return r.json({ ok: false, error: mode + " parse failed: " + e.message }); }
  if (!colmap) return r.json({ ok: false, error: "column detection failed \u2014 re-send with colmap {team,conf,adjoe,adjde,adjt,barthag}", sample: rows ? rows.slice(0, 2) : null });
  const built = buildTorvik(rows, colmap, year, "manual:" + mode);
  if (!built) return r.json({ ok: false, error: "parsed " + (rows ? rows.length : 0) + " rows but <200 valid teams \u2014 check colmap", colmap: colmap, sample: rows ? rows.slice(0, 2) : null });
  TORVIK = built; TORVIK_ERR = null; TORVIK_LOCK = { mode: mode, colmap: colmap };
  await rSet("hb:torvik:lock", TORVIK_LOCK);
  await rSet("hb:torvik:last", { list: built.list, year: built.year, fetchedAt: built.fetchedAt, mode: built.mode });
  r.json({ ok: true, teams: built.teams, year: built.year, mode: built.mode, avg: built.avg, top3: built.list.slice(0, 3) });
});

// Point-in-time ratings import. Body: { year, date, data } for one dated snapshot, or
// { year, bulk: { "YYYYMMDD"|"YYYY-MM-DD": <rows array | csv/json text>, ... } } for many at once
// (build the bulk map from barttorvik time-machine files on a machine that can reach them).
app.post("/api/admin/torvik/tm", async (q, r) => {
  const b = q.body || {};
  const year = +b.year || seasonYear();
  const toYmd = s => String(s).replace(/-/g, "").slice(0, 8);
  function listFrom(data, colmap) {
    let rows, cm = colmap || null;
    if (typeof data === "string") {
      const t = data.trim();
      if (t[0] === "[" || t[0] === "{") { const j = JSON.parse(t); const arr = Array.isArray(j) ? j : (j.data || []); const pa = ratingsFromArray(arr, cm); rows = pa.rows; cm = cm || pa.colmap; }
      else { const all = parseCsv(t); const hc = headerColmap(all[0]); cm = cm || hc; rows = hc ? all.slice(1) : all; if (!cm) cm = detectColumns(rows); }
    } else if (Array.isArray(data)) { const pa = ratingsFromArray(data, cm); rows = pa.rows; cm = cm || pa.colmap; }
    else return null;
    if (!cm) return null;
    const built = buildTorvik(rows, cm, year, "tm-import");
    return built ? built.list : null;
  }
  try {
    const items = b.bulk && typeof b.bulk === "object" ? Object.keys(b.bulk).map(k => [toYmd(k), b.bulk[k]]) : (b.date ? [[toYmd(b.date), b.data]] : null);
    if (!items || !items.length) return r.status(400).json({ ok: false, error: "need { year, date, data } or { year, bulk: { date: rows } }" });
    const stored = [], failed = [];
    for (const it of items) {
      const ymd = it[0], data = it[1];
      if (!/^\d{8}$/.test(ymd)) { failed.push({ date: ymd, error: "bad date (use YYYY-MM-DD or YYYYMMDD)" }); continue; }
      let list = null; try { list = listFrom(data, b.colmap); } catch (e) { failed.push({ date: ymd, error: "parse: " + e.message }); continue; }
      if (!list || list.length < 200) { failed.push({ date: ymd, error: "parsed " + (list ? list.length : 0) + " teams (<200)" }); continue; }
      await tmStorePut(year, ymd, list);
      stored.push({ date: ymd, teams: list.length });
    }
    const dates = await tmIndex(year, true);
    r.json({ ok: stored.length > 0, year: year, stored: stored.length, failed: failed.length, storedDetail: stored.slice(0, 5), failedDetail: failed.slice(0, 5), coverage: { count: dates.length, from: dates[0] || null, to: dates[dates.length - 1] || null } });
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.post("/api/admin/neutral", async (q, r) => {
  const { gameId, off } = q.body || {};
  if (!gameId) return r.status(400).json({ ok: false, error: "need gameId" });
  if (off) delete NEUTRAL[gameId]; else NEUTRAL[gameId] = 1;
  await rSet("hb:neutral", NEUTRAL);
  r.json({ ok: true, neutral: Object.keys(NEUTRAL) });
});

app.post("/api/admin/model", async (q, r) => {
  const b = q.body || {};
  ["HCA", "SD", "TOT_SD", "RATINGS_MAX_AGE_H"].forEach(k => { if (typeof b[k] === "number") CFG[k] = b[k]; });
  if (b.thresholds) Object.keys(CFG.thresholds).forEach(k => { if (typeof b.thresholds[k] === "number") CFG.thresholds[k] = b.thresholds[k]; });
  if (b.kelly) Object.keys(CFG.kelly).forEach(k => { if (typeof b.kelly[k] === "number") CFG.kelly[k] = b.kelly[k]; });
  if (b.ev) Object.keys(CFG.ev).forEach(k => { if (typeof b.ev[k] === "number") CFG.ev[k] = b.ev[k]; });
  if (b.replay) {
    if (Array.isArray(b.replay.snapTimes) && b.replay.snapTimes.every(x => typeof x === "string")) CFG.replay.snapTimes = b.replay.snapTimes;
    ["lagDays", "safetyCredits", "fetchDelayMs", "costPerCall", "maxRetries"].forEach(k => { if (typeof b.replay[k] === "number") CFG.replay[k] = b.replay[k]; });
  }
  await rSet("hb:model", CFG);
  slateCache.t = 0; // force re-assembly with new constants on next pull
  r.json({ ok: true, cfg: CFG });
});

app.get("/api/ev", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: true, rows: [], arbs: [], coverage: {}, cfg: CFG.ev, note: "ODDS_API_KEY not set \u2014 add it in the Render dashboard.", quota: QUOTA });
    await fetchTorvik();
    const games = await getSlate(false);
    const asm = assembleSlate(games);
    r.json(Object.assign({ ok: true, generatedAt: slateCache.t, cfg: CFG.ev, quota: QUOTA,
      note: (!games.length && isOffseason()) ? OFFSEASON_NOTE : undefined }, computeEv(games, asm)));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.get("/api/picks", (q, r) => {
  const open = TRACKER.picks.filter(p => p.status === "open").sort((a, b) => new Date(a.commence) - new Date(b.commence));
  r.json({ ok: true, open, kelly: CFG.kelly, thresholds: CFG.thresholds });
});

app.get("/api/track/record", (q, r) => {
  const graded = TRACKER.picks.filter(p => ["won", "lost", "push"].includes(p.status)).sort((a, b) => b.result.gradedAt - a.result.gradedAt);
  const n = Math.min(100, Math.max(1, parseInt(q.query.n) || 25));
  r.json({ ok: true, record: computeRecord(), recent: graded.slice(0, n), daily: dailyPnl(TRACKER.picks),
    pendingGrade: TRACKER.picks.filter(p => p.status === "open" && new Date(p.commence).getTime() < Date.now()).length });
});

app.post("/api/track/grade", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: false, error: "ODDS_API_KEY not set" });
    freezeDueCloses();
    r.json(Object.assign({ ok: true }, await gradeOpenPicks()));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.post("/api/admin/pick/void", (q, r) => {
  const { pid } = q.body || {};
  const p = TRACKER.picks.find(x => x.pid === pid);
  if (!p) return r.status(404).json({ ok: false, error: "pick not found" });
  p.status = "void"; saveTracker();
  r.json({ ok: true, pid });
});

app.get("/api/replay/status", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const [cur, agg, games] = await Promise.all([rGetJ("hb:replay:cursor:" + year), rGetJ("hb:replay:agg:" + year), rGetJ("hb:replay:games:" + year)]);
  r.json({ ok: true, year, cursor: cur, results: games ? { games: games.games.length, mode: games.mode } : null,
    agg: agg ? { days: agg.days, simmed: agg.simmed, picks: agg.picks.ALL.n } : null, hasReport: !!agg, cfg: CFG.replay });
});

app.get("/api/replay/plan", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const from = q.query.from || (year - 1) + "-11-04", to = q.query.to || year + "-04-08";
  const snaps = +(q.query.snaps || CFG.replay.snapTimes.length);
  const days = Math.max(0, Math.round((new Date(to) - new Date(from)) / 86400e3) + 1);
  const credits = replayCostFor(days, snaps);
  const budget = q.query.budget ? +q.query.budget : null;
  r.json({ ok: true, year, from, to, days, snapsPerDay: snaps, costPerCall: CFG.replay.costPerCall, creditsNeeded: credits,
    budget, daysAffordable: budget ? Math.floor(budget / (snaps * CFG.replay.costPerCall)) : null,
    quotaRemaining: QUOTA.remaining, safety: CFG.replay.safetyCredits,
    fits: QUOTA.remaining == null ? "unknown — make any live call first to read quota headers" : (QUOTA.remaining >= credits + CFG.replay.safetyCredits) });
});

app.post("/api/replay/ingest", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: false, error: "ODDS_API_KEY not set" });
    if (!q.body || !q.body.year) return r.status(400).json({ ok: false, error: "need {year}" });
    r.json(await ingestDays(q.body));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.post("/api/replay/results", async (q, r) => {
  try {
    const year = +(q.body && q.body.year);
    if (!year) return r.status(400).json({ ok: false, error: "need {year}" });
    if (q.body.csv) {
      const games = parseResultsCsvManual(q.body.csv);
      if (!games || games.length < 1) return r.status(400).json({ ok: false, error: "manual CSV parse failed — header must include date,away,home,away_pts,home_pts[,neutral]" });
      await rSet("hb:replay:games:" + year, { games, det: "manual", mode: "manual", fetchedAt: Date.now() });
      return r.json({ ok: true, games: games.length, mode: "manual", det: "manual", sample: games[0] });
    }
    r.json(await fetchTorvikGames(year));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.post("/api/replay/run", async (q, r) => {
  try {
    if (!q.body || !q.body.year) return r.status(400).json({ ok: false, error: "need {year}" });
    r.json(await simulateDays(q.body));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.get("/api/replay/report", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const agg = await rGetJ("hb:replay:agg:" + year);
  if (!agg) return r.json({ ok: false, error: "no replay aggregate for " + year + " — ingest, load results, then run" });
  r.json(Object.assign({ ok: true }, buildReport(agg)));
});

app.get("/api/replay/debug/games", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const g = await rGetJ("hb:replay:games:" + year);
  r.json(g ? { ok: true, games: g.games.length, mode: g.mode, det: g.det, sample: (g.sample || []).slice(0, 2), first3: g.games.slice(0, 3) } : { ok: false, error: "no results stored for " + year });
});

// Mobile-friendly point-in-time import: upload the downloaded barttorvik time-machine .gz files
// (date is read from each filename). The server gunzips + parses each and stores it in the
// point-in-time ratings store. Body: { year, files: [{ name, b64 }] }.
app.post("/api/admin/torvik/tmupload", async (q, r) => {
  const b = q.body || {};
  const year = +b.year || seasonYear();
  const files = Array.isArray(b.files) ? b.files : [];
  if (!files.length) return r.status(400).json({ ok: false, error: "no files uploaded" });
  const stored = [], failed = [];
  for (const f of files) {
    const name = String((f && f.name) || "");
    try {
      const m = name.match(/(\d{8})/);
      if (!m) { failed.push({ name: name, error: "no YYYYMMDD date in filename" }); continue; }
      const ymd = m[1];
      const raw = Buffer.from((f && f.b64) || "", "base64");
      const isGz = raw.length > 2 && raw[0] === 0x1f && raw[1] === 0x8b;
      const text = isGz ? zlib.gunzipSync(raw).toString("utf8") : raw.toString("utf8");
      const j = JSON.parse(text);
      const arr = Array.isArray(j) ? j : (j.data || []);
      const pa = ratingsFromArray(arr, null);
      if (!pa.colmap) { failed.push({ name: name, error: "could not detect rating columns" }); continue; }
      const built = buildTorvik(pa.rows, pa.colmap, year, "tm-upload");
      if (!built || built.list.length < 200) { failed.push({ name: name, error: "parsed " + (built ? built.list.length : 0) + " teams (<200)" }); continue; }
      await tmStorePut(year, ymd, built.list);
      stored.push({ date: ymd, teams: built.list.length, top: built.list[0] });
    } catch (e) { failed.push({ name: name, error: e.message }); }
  }
  const dates = await tmIndex(year, true);
  r.json({ ok: stored.length > 0, year: year, stored: stored.length, failed: failed.length, storedDetail: stored.slice(0, 8), failedDetail: failed.slice(0, 8), coverage: { count: dates.length, from: dates[0] || null, to: dates[dates.length - 1] || null } });
});
app.get("/api/replay/tm", async (q, r) => {
  const year = +(q.query.year || seasonYear());
  const dates = await tmIndex(year, true);
  r.json({ ok: true, year: year, count: dates.length, from: dates[0] || null, to: dates[dates.length - 1] || null, dates: dates });
});
app.get("/api/replay/debug/timemachine", async (q, r) => {
  const date = q.query.date;
  if (!date) return r.status(400).json({ ok: false, error: "need ?date=YYYY-MM-DD" });
  const tm = await timeMachineRatings(date, +(q.query.year || seasonYear()));
  r.json(tm ? { ok: true, date, teams: tm.teams, mode: tm.mode, avg: tm.avg, top3: tm.list.slice(0, 3) } : { ok: false, date, error: "Time Machine fetch/parse failed for this date" });
});

app.post("/api/admin/replay/reset", async (q, r) => {
  const { year, what } = q.body || {};
  if (!year || !what) return r.status(400).json({ ok: false, error: "need {year, what: lines|games|sim|all}" });
  const done = [];
  if (what === "lines" || what === "all") { for (let m = 1; m <= 12; m++) { await rDel("hb:replay:lines:" + year + ":" + pad2(m)); } done.push("lines"); }
  if (what === "games" || what === "all") { await rDel("hb:replay:games:" + year); done.push("games"); }
  if (what === "sim" || what === "all") { await rDel("hb:replay:agg:" + year); done.push("agg"); }
  if (what === "all") { await rDel("hb:replay:cursor:" + year); done.push("cursor"); }
  if (what === "sim") { const c = await rGetJ("hb:replay:cursor:" + year); if (c) { delete c.simNext; await rSet("hb:replay:cursor:" + year, c); } }
  r.json({ ok: true, cleared: done });
});

const DASH = Buffer.from("PCFET0NUWVBFIGh0bWw+CjxodG1sIGxhbmc9ImVuIj4KPGhlYWQ+CjxtZXRhIGNoYXJzZXQ9IlVURi04Ij4KPG1ldGEgbmFtZT0idmlld3BvcnQiIGNvbnRlbnQ9IndpZHRoPWRldmljZS13aWR0aCwgaW5pdGlhbC1zY2FsZT0xLjAsIG1heGltdW0tc2NhbGU9MS4wLCB1c2VyLXNjYWxhYmxlPW5vIj4KPHRpdGxlPkhPT1BTQkVUIOKAlCBOQ0FBIEJhc2tldGJhbGw8L3RpdGxlPgo8bGluayBocmVmPSJodHRwczovL2ZvbnRzLmdvb2dsZWFwaXMuY29tL2NzczI/ZmFtaWx5PU91dGZpdDp3Z2h0QDMwMDs0MDA7NTAwOzYwMDs3MDA7ODAwOzkwMCZmYW1pbHk9SmV0QnJhaW5zK01vbm86d2dodEA0MDA7NTAwOzYwMDs3MDA7ODAwJmRpc3BsYXk9c3dhcCIgcmVsPSJzdHlsZXNoZWV0Ij4KPHN0eWxlPgo6cm9vdHstLWJnOiMwYTE0MzA7LS1jYXJkOiMwZjIxNDc7LS1ib3JkZXI6IzIyNDI3ZjstLXRleHQ6I2Y1ZjhmZDstLWRpbTojYWViZmRhOy0tbXV0ZWQ6IzdhOTBiNTstLWFjY2VudDojMmY2ZmUwOy0tYWNjZW50VGV4dDojNmI5N2VlOy0tZ3JlZW46IzE4Yjg3YzstLXJlZDojZTEyZTQ0Oy0tcmVkVGV4dDojZjA1NTZiOy0tYW1iZXI6I2UwYTIzYTstLXB1cnBsZTojNmY5ZWZmOy0tY2FyZDI6IzBjMWEzYX0KKnttYXJnaW46MDtwYWRkaW5nOjA7Ym94LXNpemluZzpib3JkZXItYm94Oy13ZWJraXQtdGFwLWhpZ2hsaWdodC1jb2xvcjp0cmFuc3BhcmVudH0KaHRtbHstd2Via2l0LXRleHQtc2l6ZS1hZGp1c3Q6MTAwJX0KYm9keXtiYWNrZ3JvdW5kOnZhcigtLWJnKTtjb2xvcjp2YXIoLS10ZXh0KTtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3BhZGRpbmc6MTJweCAxNHB4IDEyMHB4O21heC13aWR0aDoxMTAwcHg7bWFyZ2luOjAgYXV0b30KLm1vbm97Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9CmJ1dHRvbjpmb2N1cy12aXNpYmxlLHNlbGVjdDpmb2N1cy12aXNpYmxlLGlucHV0OmZvY3VzLXZpc2libGUsYTpmb2N1cy12aXNpYmxle291dGxpbmU6MnB4IHNvbGlkIHZhcigtLWFjY2VudFRleHQpO291dGxpbmUtb2Zmc2V0OjJweH0KLmhkcntkaXNwbGF5OmZsZXg7YWxpZ24taXRlbXM6Y2VudGVyO2p1c3RpZnktY29udGVudDpzcGFjZS1iZXR3ZWVuO2dhcDo4cHg7bWFyZ2luLWJvdHRvbToxMnB4fQouYnJhbmR7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtnYXA6OXB4fQoubG9nb3t3aWR0aDozNHB4O2hlaWdodDozNHB4O2JvcmRlci1yYWRpdXM6OXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDEzNWRlZywjZTg1ZDJmLHZhcigtLWFjY2VudCkpO2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OmNlbnRlcjtmb250LXdlaWdodDo5MDA7Zm9udC1zaXplOjE2cHh9Ci5idHtmb250LXNpemU6MTVweDtmb250LXdlaWdodDo4MDB9LmJ0IHNwYW57Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ic3Vie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKX0KLmhkci1idG57cGFkZGluZzo4cHggMTRweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo4cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1hY2NlbnQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xKTtjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZn0KLmNhcmR7YmFja2dyb3VuZDpsaW5lYXItZ3JhZGllbnQoMTgwZGVnLHZhcigtLWNhcmQpLHZhcigtLWNhcmQyKSk7Ym9yZGVyOjFweCBzb2xpZCB0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjEwcHg7Ym94LXNoYWRvdzppbnNldCAwIDFweCAwIHJnYmEoMjU1LDI1NSwyNTUsLjA0KSwwIDRweCAxMnB4IHJnYmEoMCwwLDAsLjMyKTtwYWRkaW5nOjExcHggMTJweDttYXJnaW4tYm90dG9tOjhweH0KLnN0cmlwe2Rpc3BsYXk6ZmxleDtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwO21hcmdpbi1ib3R0b206MTBweH0KLmtwaXtmbGV4OjE7bWluLXdpZHRoOjEwNXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO3BhZGRpbmc6OXB4IDExcHh9Ci5rcGkgLmxie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKTt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bGV0dGVyLXNwYWNpbmc6LjRweDtmb250LXdlaWdodDo3MDB9Ci5rcGkgLnZ7Zm9udC1zaXplOjE3cHg7Zm9udC13ZWlnaHQ6ODAwO21hcmdpbi10b3A6MnB4fQoua3BpIC5ze2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDoxcHh9Ci5mYmFye2Rpc3BsYXk6ZmxleDtnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlcjttYXJnaW4tYm90dG9tOjEwcHh9Ci5jaGlwe3BhZGRpbmc6NnB4IDEzcHg7bWluLWhlaWdodDo0NHB4O2JvcmRlci1yYWRpdXM6OHB4O2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtiYWNrZ3JvdW5kOnRyYW5zcGFyZW50O2NvbG9yOnZhcigtLW11dGVkKTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZjtkaXNwbGF5OmlubGluZS1mbGV4O2FsaWduLWl0ZW1zOmNlbnRlcn0KLmNoaXAub257Ym9yZGVyLWNvbG9yOnZhcigtLWFjY2VudFRleHQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xMik7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9CnNlbGVjdC5jaGlwe2FwcGVhcmFuY2U6bm9uZTtwYWRkaW5nLXJpZ2h0OjI2cHg7YmFja2dyb3VuZC1pbWFnZTpsaW5lYXItZ3JhZGllbnQoNDVkZWcsdHJhbnNwYXJlbnQgNTAlLHZhcigtLW11dGVkKSA1MCUpLGxpbmVhci1ncmFkaWVudCgxMzVkZWcsdmFyKC0tbXV0ZWQpIDUwJSx0cmFuc3BhcmVudCA1MCUpO2JhY2tncm91bmQtcG9zaXRpb246Y2FsYygxMDAlIC0gMTRweCkgNTAlLGNhbGMoMTAwJSAtIDlweCkgNTAlO2JhY2tncm91bmQtc2l6ZTo1cHggNXB4O2JhY2tncm91bmQtcmVwZWF0Om5vLXJlcGVhdH0KLmdjYXJke2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO21hcmdpbi1ib3R0b206OHB4O3BhZGRpbmc6MTFweCAxMnB4fQouZy10b3B7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwfQouZy10ZWFtc3tmb250LXNpemU6MTNweDtmb250LXdlaWdodDo4MDA7bWluLXdpZHRoOjB9Ci5nLXRlYW1zIC5ya3tjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTBweDtmb250LXdlaWdodDo4MDA7bWFyZ2luLXJpZ2h0OjJweH0KLmctdGVhbXMgLmF0e2NvbG9yOnZhcigtLW11dGVkKTtmb250LXdlaWdodDo2MDA7bWFyZ2luOjAgNXB4fQouZy1tZXRhe2Rpc3BsYXk6ZmxleDtnYXA6NXB4O2FsaWduLWl0ZW1zOmNlbnRlcjtmbGV4LXdyYXA6d3JhcH0KLnRhZ3twYWRkaW5nOjJweCA3cHg7Ym9yZGVyLXJhZGl1czo1cHg7Zm9udC1zaXplOjEwcHg7Zm9udC13ZWlnaHQ6ODAwO2xldHRlci1zcGFjaW5nOi4zcHh9Ci50YWctdGltZXtiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA1KTtjb2xvcjp2YXIoLS1kaW0pO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKX0KLnRhZy1ue2JhY2tncm91bmQ6cmdiYSgxMTEsMTU4LDI1NSwuMTIpO2NvbG9yOnZhcigtLXB1cnBsZSk7Ym9yZGVyOjFweCBzb2xpZCByZ2JhKDExMSwxNTgsMjU1LC4zKX0KLnRhZy1ia3tiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA0KTtjb2xvcjp2YXIoLS1tdXRlZCk7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQouYXdhaXR7ZGlzcGxheTppbmxpbmUtYmxvY2s7cGFkZGluZzoycHggOHB4O2JvcmRlci1yYWRpdXM6NXB4O2JhY2tncm91bmQ6cmdiYSgyMjQsMTYyLDU4LC4xKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjI0LDE2Miw1OCwuMyk7Y29sb3I6dmFyKC0tYW1iZXIpO2ZvbnQtc2l6ZToxMHB4O2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvantkaXNwbGF5OmZsZXg7Z2FwOjE0cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKX0KLmctcHJvaiBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvaiAubW9ub3tmb250LXNpemU6MTJweH0KLmctZWRnZXN7ZGlzcGxheTpmbGV4O2dhcDo2cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo5cHh9Ci5lZHtwYWRkaW5nOjVweCAxMHB4O2JvcmRlci1yYWRpdXM6N3B4O2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjgwMDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtib3JkZXI6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7Y29sb3I6dmFyKC0tbXV0ZWQpO2JhY2tncm91bmQ6cmdiYSgyNTUsMjU1LDI1NSwuMDIpfQouZWQuaG90e2JvcmRlci1jb2xvcjpyZ2JhKDI0LDE4NCwxMjQsLjQ1KTtiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMSk7Y29sb3I6dmFyKC0tZ3JlZW4pfQouZWQgLnNke2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7Zm9udC13ZWlnaHQ6NzAwO2ZvbnQtc2l6ZToxMHB4O21hcmdpbi1yaWdodDo0cHg7Y29sb3I6aW5oZXJpdDtvcGFjaXR5Oi44NX0KLmctc2hhcnB7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQouZy1zaGFycCBie2NvbG9yOnZhcigtLXB1cnBsZSk7Zm9udC13ZWlnaHQ6NzAwfQouZW1wdHl7cGFkZGluZzoyNnB4IDE4cHg7Ym9yZGVyOjFweCBkYXNoZWQgdmFyKC0tYm9yZGVyKTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEycHg7bGluZS1oZWlnaHQ6MS42NTt0ZXh0LWFsaWduOmNlbnRlcjtjb2xvcjp2YXIoLS1tdXRlZCl9Ci5lbXB0eSBie2NvbG9yOnZhcigtLXRleHQpfQoubW9yZXt3aWR0aDoxMDAlO3BhZGRpbmc6MTFweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo5cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2JhY2tncm91bmQ6dHJhbnNwYXJlbnQ7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7bWFyZ2luOjJweCAwIDEwcHh9Ci5zZWMtaGR7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2NvbG9yOnZhcigtLWRpbSk7bGV0dGVyLXNwYWNpbmc6LjNweDt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bWFyZ2luOjE0cHggMCA4cHh9Ci5zcm93e2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OnNwYWNlLWJldHdlZW47Z2FwOjhweDtwYWRkaW5nOjlweCAxMXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6OXB4O2JveC1zaGFkb3c6aW5zZXQgMCAxcHggMCByZ2JhKDI1NSwyNTUsMjU1LC4wNCksMCAzcHggMTBweCByZ2JhKDAsMCwwLC4zKTttYXJnaW4tYm90dG9tOjZweH0KLnNyb3cgLnR7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwfQouc3JvdyAuc2N7Zm9udC1zaXplOjEzcHg7Zm9udC13ZWlnaHQ6ODAwO2ZvbnQtZmFtaWx5OidKZXRCcmFpbnMgTW9ubycsbW9ub3NwYWNlfQouc3JvdyAuc3R7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQoubGl2ZS1kb3R7Y29sb3I6dmFyKC0tZ3JlZW4pO2ZvbnQtd2VpZ2h0OjgwMH0KdGFibGV7d2lkdGg6MTAwJTtib3JkZXItY29sbGFwc2U6Y29sbGFwc2U7Zm9udC1zaXplOjExcHh9CnRoe3RleHQtYWxpZ246bGVmdDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC1zaXplOjEwcHg7dGV4dC10cmFuc2Zvcm06dXBwZXJjYXNlO2xldHRlci1zcGFjaW5nOi40cHg7Zm9udC13ZWlnaHQ6NzAwO3BhZGRpbmc6NXB4IDZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQp0ZHtwYWRkaW5nOjZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCByZ2JhKDM0LDY2LDEyNywuMzUpfQp0ZC5tb25ve2ZvbnQtc2l6ZToxMXB4fQouc3RhdHVze3BhZGRpbmc6MTZweDt0ZXh0LWFsaWduOmNlbnRlcjtmb250LXNpemU6MTJweDtjb2xvcjp2YXIoLS1hbWJlcil9Ci5zcGlue2Rpc3BsYXk6aW5saW5lLWJsb2NrO3dpZHRoOjEzcHg7aGVpZ2h0OjEzcHg7Ym9yZGVyOjJweCBzb2xpZCB2YXIoLS1hbWJlcik7Ym9yZGVyLXRvcC1jb2xvcjp0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjUwJTthbmltYXRpb246c3AgLjhzIGxpbmVhciBpbmZpbml0ZTt2ZXJ0aWNhbC1hbGlnbjptaWRkbGU7bWFyZ2luLXJpZ2h0OjVweH0KQGtleWZyYW1lcyBzcHt0b3t0cmFuc2Zvcm06cm90YXRlKDM2MGRlZyl9fQoubm90ZXttYXJnaW4tdG9wOjE0cHg7cGFkZGluZzoxMHB4IDEycHg7YmFja2dyb3VuZDpyZ2JhKDQ3LDExMSwyMjQsLjA0KTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tZGltKTtsaW5lLWhlaWdodDoxLjU1fQoubm90ZSBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjYwMH0KLmZvb3Rlcntib3JkZXItdG9wOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO3BhZGRpbmc6MTBweCA0cHggMDttYXJnaW4tdG9wOjE0cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO3RleHQtYWxpZ246Y2VudGVyfQouc2VjdGlvbntkaXNwbGF5Om5vbmV9LnNlY3Rpb24ub257ZGlzcGxheTpibG9ja30KLmJuYXZ7cG9zaXRpb246Zml4ZWQ7bGVmdDowO3JpZ2h0OjA7Ym90dG9tOjA7ZGlzcGxheTpmbGV4O2JhY2tncm91bmQ6cmdiYSgxMCwxNCwyMywuOTYpO2JhY2tkcm9wLWZpbHRlcjpibHVyKDEwcHgpOy13ZWJraXQtYmFja2Ryb3AtZmlsdGVyOmJsdXIoMTBweCk7Ym9yZGVyLXRvcDoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtwYWRkaW5nOjhweCA0cHggY2FsYyg2cHggKyBlbnYoc2FmZS1hcmVhLWluc2V0LWJvdHRvbSkpO3otaW5kZXg6MTAwfQouYm5hdi1idG57ZmxleDoxO2Rpc3BsYXk6ZmxleDtmbGV4LWRpcmVjdGlvbjpjb2x1bW47YWxpZ24taXRlbXM6Y2VudGVyO2dhcDoycHg7cGFkZGluZzo4cHggNHB4IDZweDtib3JkZXI6bm9uZTtiYWNrZ3JvdW5kOm5vbmU7Y29sb3I6dmFyKC0tbXV0ZWQpO2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjYwMDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO2N1cnNvcjpwb2ludGVyO21pbi1oZWlnaHQ6NDRweDtqdXN0aWZ5LWNvbnRlbnQ6Y2VudGVyfQouYm5hdi1idG4ub257Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ibmF2LWljbyBzdmd7ZGlzcGxheTpibG9ja30KLnJwbC1pbnt3aWR0aDo2NHB4O2JhY2tncm91bmQ6dmFyKC0tY2FyZDIpO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtjb2xvcjp2YXIoLS10ZXh0KTtib3JkZXItcmFkaXVzOjZweDtwYWRkaW5nOjZweCA4cHg7Zm9udC1zaXplOjEycHg7Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9Ci5ycGwtdGF7d2lkdGg6MTAwJTttaW4taGVpZ2h0Ojc2cHg7YmFja2dyb3VuZDp2YXIoLS1jYXJkMik7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2NvbG9yOnZhcigtLXRleHQpO2JvcmRlci1yYWRpdXM6N3B4O3BhZGRpbmc6N3B4IDlweDtmb250LXNpemU6MTFweDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtyZXNpemU6dmVydGljYWw7bWFyZ2luLXRvcDo2cHh9Ci5ycGwtbGlua3tiYWNrZ3JvdW5kOm5vbmU7Ym9yZGVyOm5vbmU7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO3BhZGRpbmc6MDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3RleHQtZGVjb3JhdGlvbjp1bmRlcmxpbmV9Ci5jaGlwOmRpc2FibGVke29wYWNpdHk6LjQ7Y3Vyc29yOmRlZmF1bHR9CiNycGwtbG9ne2Rpc3BsYXk6bm9uZTtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtmb250LXNpemU6MTFweDttYXJnaW4tdG9wOjhweDtwYWRkaW5nOjhweCAxMHB4O2JhY2tncm91bmQ6cmdiYSgwLDAsMCwuMjgpO2JvcmRlci1yYWRpdXM6N3B4O2NvbG9yOnZhcigtLWRpbSk7d2hpdGUtc3BhY2U6cHJlLXdyYXA7d29yZC1icmVhazpicmVhay13b3JkO2xpbmUtaGVpZ2h0OjEuNTttYXgtaGVpZ2h0OjIwMHB4O292ZXJmbG93LXk6YXV0b30KPC9zdHlsZT4KPC9oZWFkPgo8Ym9keT4KCjxkaXYgY2xhc3M9ImhkciI+CiAgPGRpdiBjbGFzcz0iYnJhbmQiPgogICAgPGRpdiBjbGFzcz0ibG9nbyI+SDwvZGl2PgogICAgPGRpdj48ZGl2IGNsYXNzPSJidCI+SE9PUFM8c3Bhbj5CRVQ8L3NwYW4+IDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTBweDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC13ZWlnaHQ6NjAwIj52MTwvc3Bhbj48L2Rpdj4KICAgIDxkaXYgY2xhc3M9ImJzdWIiIGlkPSJjb25uIj4mIzk2Nzk7IGNvbm5lY3RpbmcmaGVsbGlwOzwvZGl2PjwvZGl2PgogIDwvZGl2PgogIDxidXR0b24gY2xhc3M9Imhkci1idG4iIG9uY2xpY2s9ImxvYWRBbGwodHJ1ZSkiPiYjODYzNTsgUmVmcmVzaDwvYnV0dG9uPgo8L2Rpdj4KCjwhLS0gR0FNRVMgLS0+CjxkaXYgaWQ9InNlYy1nYW1lcyIgY2xhc3M9InNlY3Rpb24gb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0ia3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8c2VsZWN0IGNsYXNzPSJjaGlwIiBpZD0iZi1jb25mIiBvbmNoYW5nZT0iYXBwbHlGaWx0ZXJzKCkiPjxvcHRpb24gdmFsdWU9IiI+QWxsIGNvbmZlcmVuY2VzPC9vcHRpb24+PC9zZWxlY3Q+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0iZi10b3AiIG9uY2xpY2s9InRnKHRoaXMsJ3RvcCcpIj5Ub3AgMjU8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJmLWVkZ2UiIG9uY2xpY2s9InRnKHRoaXMsJ2VkZ2UnKSI+RWRnZXMgb25seTwvYnV0dG9uPgogICAgPHNlbGVjdCBjbGFzcz0iY2hpcCIgaWQ9ImYtc29ydCIgb25jaGFuZ2U9ImFwcGx5RmlsdGVycygpIj48b3B0aW9uIHZhbHVlPSJlZGdlIj5Tb3J0OiBFZGdlPC9vcHRpb24+PG9wdGlvbiB2YWx1ZT0idGltZSI+U29ydDogVGlwIHRpbWU8L29wdGlvbj48L3NlbGVjdD4KICA8L2Rpdj4KICA8ZGl2IGNsYXNzPSJmYmFyIiBpZD0ibWluZWRnZSI+CiAgICA8c3BhbiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO21hcmdpbi1yaWdodDoycHgiPk1pbiBlZGdlPC9zcGFuPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCBvbiIgb25jbGljaz0ibWUoMCx0aGlzKSI+QWxsPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJtZSgyLHRoaXMpIj4yJSs8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIG9uY2xpY2s9Im1lKDQsdGhpcykiPjQlKzwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0ibWUoNix0aGlzKSI+NiUrPC9idXR0b24+CiAgPC9kaXY+CiAgPGRpdiBpZD0iZ2FtZXMtc3RhdHVzIiBjbGFzcz0ic3RhdHVzIj48c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBMb2FkaW5nIHNsYXRlJmhlbGxpcDs8L2Rpdj4KICA8ZGl2IGlkPSJnYW1lcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ibm90ZSI+PGI+SG93IHRvIHJlYWQ6PC9iPiBwcm9qZWN0aW9ucyBjb21lIGZyb20gdGhlIFRvcnZpay1mZWQgZWZmaWNpZW5jeSBtb2RlbCAoQWRqT0UgJnRpbWVzOyBBZGpERSAmdGltZXM7IHRlbXBvLCBIQ0EtYWRqdXN0ZWQsIHplcm9lZCBvbiBuZXV0cmFsIGZsb29ycykuIEVkZ2UgY2hpcHMgbGlnaHQgdXAgYXQgdGhlIGZsb29yczogTUwgJmdlOyA8YiBpZD0idGgtbWwiPjQ8L2I+JSAmbWlkZG90OyBTUFIgJmdlOyA8YiBpZD0idGgtc3ByIj41PC9iPiUgJm1pZGRvdDsgVE9UICZnZTsgPGIgaWQ9InRoLXRvdCI+NS41PC9iPiUsIGFuZCByZXF1aXJlICZnZTs8YiBpZD0idGgtYmsiPjM8L2I+IGJvb2tzIHBvc3RpbmcgdGhlIG1hcmtldC4gUGlja3MsIHNpemluZywgYW5kIHRyYWNraW5nIGFycml2ZSBpbiBTMyAmbWRhc2g7IHRoaXMgc3VyZmFjZSBpcyBvYnNlcnZhdGlvbmFsLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gRVYgLS0+CjxkaXYgaWQ9InNlYy1ldiIgY2xhc3M9InNlY3Rpb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0iZXYta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBpZD0iZXYtc3RyaWN0IiBvbmNsaWNrPSJldlN0cmljdCh0aGlzKSI+U3Ryb25nIG9ubHk8L2J1dHRvbj4KICAgIDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1tdXRlZCk7bWFyZ2luLWxlZnQ6NHB4Ij5NaW4gRVY8L3NwYW4+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBvbmNsaWNrPSJldk1pbigwLHRoaXMpIj5GbG9vcjwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0iZXZNaW4oMyx0aGlzKSI+MyUrPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJldk1pbig1LHRoaXMpIj41JSs8L2J1dHRvbj4KICA8L2Rpdj4KICA8ZGl2IGlkPSJldi1hcmJzIj48L2Rpdj4KICA8ZGl2IGlkPSJldi1zdGF0dXMiIGNsYXNzPSJzdGF0dXMiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjwvZGl2PgogIDxkaXYgaWQ9ImV2LXJvd3MiPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPk1ldGhvZDo8L2I+IGZhaXIgcHJvYmFiaWxpdHkgPSBQaW5uYWNsZSBuby12aWcuIEVWJSA9IGZhaXIgJnRpbWVzOyBkZWNpbWFsIG9kZHMgJm1pbnVzOyAxLCBmbG9vciA8YiBpZD0iZXYtZmxvb3IiPjI8L2I+JS4gU3ByZWFkcyBhbmQgdG90YWxzIGFyZSBzY3JlZW5lZCA8Yj5vbmx5IHdoZXJlIGEgcmV0YWlsIGJvb2sgcG9zdHMgdGhlIGV4YWN0IFBpbm5hY2xlIGxpbmU8L2I+ICZtZGFzaDsgbWlzbWF0Y2hlZCBsaW5lcyBhcmUgc2tpcHBlZCwgbmV2ZXIgYXBwcm94aW1hdGVkLiA8Yj5TVFJPTkc8L2I+ID0gdGhlIHByaWNlZCBib29rIGlzICZnZTs8YiBpZD0iZXYtZ2FwIj4yPC9iPiBpbXBsaWVkIHBvaW50cyBiZXR0ZXIgdGhhbiB0aGUgcmVzdCBvZiByZXRhaWwgKHN0YWxlLWxpbmUgc2lnbmFsKTsgPGI+V0VBSzwvYj4gPSBhbGwgb2YgcmV0YWlsIGRpc2FncmVlcyB3aXRoIFBpbm5hY2xlLCB3aGljaCBjYW4gbWVhbiBhbmNob3IgbGFnLiBNb2RlbCBjaGlwcyBhcmUgaW5mb3JtYXRpb25hbCBvbmx5LiBUaGlzIGlzIGEgc2NyZWVuLCBub3QgcGlja3MgJm1kYXNoOyBub3RoaW5nIGhlcmUgZW50ZXJzIHRoZSB0cmFja2VyLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gQkVUUyAtLT4KPGRpdiBpZD0ic2VjLWJldHMiIGNsYXNzPSJzZWN0aW9uIj4KICA8ZGl2IGNsYXNzPSJzdHJpcCIgaWQ9ImIta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgaWQ9ImItY3VydmUiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjwvZGl2PgogIDxkaXYgaWQ9ImJldHMtc3RhdHVzIiBjbGFzcz0ic3RhdHVzIiBzdHlsZT0iZGlzcGxheTpub25lIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiPk9wZW4gcGlja3M8L2Rpdj48ZGl2IGlkPSJiLW9wZW4iPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+QnkgbWFya2V0PC9kaXY+PGRpdiBjbGFzcz0ic3RyaXAiIGlkPSJiLW1rdHMiPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+UmVjZW50IGdyYWRlZDwvZGl2PgogIDxkaXYgY2xhc3M9ImZiYXIiIGlkPSJiLWZpbHQiPjxidXR0b24gY2xhc3M9ImNoaXAgb24iIG9uY2xpY2s9ImJmKCdBTEwnLHRoaXMpIj5BbGw8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJiZignTUwnLHRoaXMpIj5NTDwvYnV0dG9uPjxidXR0b24gY2xhc3M9ImNoaXAiIG9uY2xpY2s9ImJmKCdTUFInLHRoaXMpIj5TUFI8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJiZignVE9UJyx0aGlzKSI+VE9UPC9idXR0b24+PC9kaXY+CiAgPGRpdiBpZD0iYi1yZWNlbnQiPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPkhvdyBwaWNrcyB3b3JrOjwvYj4gYSBwaWNrIGF1dG8tbG9ncyB0aGUgZmlyc3QgdGltZSBhIG1hcmtldCBjbGVhcnMgaXRzIGVkZ2UgZmxvb3IgKG9uZSBwZXIgZ2FtZSBwZXIgbWFya2V0KSwgc2l6ZWQgYnkgcXVhcnRlci1LZWxseSAoMXUgPSAxJSBiYW5rcm9sbCwgY2FwcGVkIGF0IDxzcGFuIGlkPSJiLW1heHUiPjI8L3NwYW4+dSkuIENsb3NpbmcgbGluZXMgZnJlZXplIGF0IHRoZSBsYXN0IHJlZnJlc2ggYmVmb3JlIHRpcDsgQ0xWIGlzIGdyYWRlZCBhZ2FpbnN0IFBpbm5hY2xlIHdoZW4gYXZhaWxhYmxlLCBlbHNlIHJldGFpbCBjb25zZW5zdXMuIFBvc2l0aXZlIENMViA9IHRoZSBwaWNrIGJlYXQgdGhlIGNsb3NlLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gU0NPUkVTIC0tPgo8ZGl2IGlkPSJzZWMtc2NvcmVzIiBjbGFzcz0ic2VjdGlvbiI+CiAgPGRpdiBpZD0ic2NvcmVzLXN0YXR1cyIgY2xhc3M9InN0YXR1cyI+PHNwYW4gY2xhc3M9InNwaW4iPjwvc3Bhbj4gTG9hZGluZyBzY29yZXMmaGVsbGlwOzwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCIgaWQ9InNoLWxpdmUiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPiYjOTY3OTsgTGl2ZTwvZGl2PjxkaXYgaWQ9InMtbGl2ZSI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ic2VjLWhkIiBpZD0ic2gtZG9uZSIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+RmluYWw8L2Rpdj48ZGl2IGlkPSJzLWRvbmUiPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCIgaWQ9InNoLXVwIiBzdHlsZT0iZGlzcGxheTpub25lIj5VcGNvbWluZzwvZGl2PjxkaXYgaWQ9InMtdXAiPjwvZGl2Pgo8L2Rpdj4KCjwhLS0gREFUQSAtLT4KPGRpdiBpZD0ic2VjLWRhdGEiIGNsYXNzPSJzZWN0aW9uIj4KICA8ZGl2IGNsYXNzPSJzdHJpcCIgaWQ9ImQta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgaWQ9ImQtaGVhbHRoIiBzdHlsZT0iZGlzcGxheTpub25lIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJjYXJkIiBpZD0iZC1tYXAiPjwvZGl2PgogIDxkaXYgY2xhc3M9ImNhcmQiIGlkPSJkLXR2aW1wb3J0Ij4KICAgIDxkaXYgc3R5bGU9ImRpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OnNwYWNlLWJldHdlZW47Z2FwOjhweDtmbGV4LXdyYXA6d3JhcCI+CiAgICAgIDxiIHN0eWxlPSJmb250LXNpemU6MTJweCI+VG9ydmlrIHJhdGluZ3M8L2I+CiAgICAgIDxidXR0b24gY2xhc3M9InJwbC1saW5rIiBvbmNsaWNrPSJ0dlRvZ2dsZUltcG9ydCgpIj5pbXBvcnQ8L2J1dHRvbj4KICAgIDwvZGl2PgogICAgPGRpdiBpZD0idHYtaW1wb3J0d3JhcCIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+CiAgICAgIDxkaXYgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luOjJweCAwIDVweCI+TGl2ZSBwaWNrcyAmbWRhc2g7IGN1cnJlbnQtc2Vhc29uIHJhdGluZ3MuIDxhIGlkPSJ0di1saW5rLXNlYXNvbiIgaHJlZj0iIyIgdGFyZ2V0PSJfYmxhbmsiIHJlbD0ibm9vcGVuZXIiIHN0eWxlPSJjb2xvcjojN2FhMmY3O3RleHQtZGVjb3JhdGlvbjp1bmRlcmxpbmUiPnRhcCB0byBvcGVuIHRoZSBmaWxlPC9hPiwgY29weSBhbGwsIHBhc3RlIGJlbG93OjwvZGl2PgogICAgICA8dGV4dGFyZWEgaWQ9InR2LWltcG9ydCIgY2xhc3M9InJwbC10YSIgcGxhY2Vob2xkZXI9IlBhc3RlIHRoZSBjb3BpZWQgcmF0aW5ncyAoQ1NWIG9yIEpTT04pIj48L3RleHRhcmVhPgogICAgICA8ZGl2IGNsYXNzPSJmYmFyIiBzdHlsZT0ibWFyZ2luOjhweCAwIDAiPjxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJ0di1pbXBvcnRidG4iIG9uY2xpY2s9InR2SW1wb3J0KCkiPlVzZSBhcyBjdXJyZW50IHJhdGluZ3M8L2J1dHRvbj48L2Rpdj4KICAgICAgPGRpdiBzdHlsZT0iYm9yZGVyLXRvcDoxcHggc29saWQgdmFyKC0tYm9yZGVyKTttYXJnaW4tdG9wOjEycHg7cGFkZGluZy10b3A6MTBweCI+CiAgICAgICAgPGRpdiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tYm90dG9tOjZweCI+QmFja3Rlc3QgKHBvaW50LWluLXRpbWUsIG5vIGxvb2thaGVhZCkuIDxiPjEuPC9iPiBUYXAgZWFjaCBkYXRlIHRvIGRvd25sb2FkIGl0cyByYXRpbmdzIGZpbGU6PC9kaXY+CiAgICAgICAgPGRpdiBpZD0idHYtdG1saW5rcyIgc3R5bGU9ImRpc3BsYXk6ZmxleDtmbGV4LXdyYXA6d3JhcDtnYXA6NXB4O21hcmdpbi1ib3R0b206OHB4Ij48L2Rpdj4KICAgICAgICA8ZGl2IHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbi1ib3R0b206NnB4Ij48Yj4yLjwvYj4gVGhlbiBjaG9vc2UgdGhlIGRvd25sb2FkZWQgZmlsZXMgKHBpY2sgc2V2ZXJhbCBhdCBvbmNlKSBhbmQgdXBsb2FkICZtZGFzaDsgdGhlIGRhdGUgaXMgcmVhZCBmcm9tIGVhY2ggZmlsZW5hbWU6PC9kaXY+CiAgICAgICAgPGRpdiBjbGFzcz0iZmJhciIgc3R5bGU9ImdhcDo2cHg7ZmxleC13cmFwOndyYXA7YWxpZ24taXRlbXM6Y2VudGVyIj48aW5wdXQgaWQ9InR2LWZpbGVzIiB0eXBlPSJmaWxlIiBhY2NlcHQ9Ii5neiwuanNvbiIgbXVsdGlwbGUgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWF4LXdpZHRoOjIxMHB4Ij48YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0idHYtdXBidG4iIG9uY2xpY2s9InR2VXBsb2FkKCkiPlVwbG9hZCAmYW1wOyBzdG9yZTwvYnV0dG9uPjwvZGl2PgogICAgICAgIDxkaXYgaWQ9InR2LWltcG9ydGxvZyIgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDo4cHg7d2hpdGUtc3BhY2U6cHJlLXdyYXA7bGluZS1oZWlnaHQ6MS41Ij48L2Rpdj4KICAgICAgICA8ZGl2IGlkPSJ0di10bWNvdiIgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDo0cHgiPjwvZGl2PgogICAgICA8L2Rpdj4KICAgIDwvZGl2PgogIDwvZGl2PgogIDxkaXYgY2xhc3M9ImNhcmQiIGlkPSJkLXJlcGxheSI+CiAgICA8ZGl2IHN0eWxlPSJkaXNwbGF5OmZsZXg7YWxpZ24taXRlbXM6Y2VudGVyO2p1c3RpZnktY29udGVudDpzcGFjZS1iZXR3ZWVuO2dhcDo4cHg7ZmxleC13cmFwOndyYXAiPgogICAgICA8YiBzdHlsZT0iZm9udC1zaXplOjEycHgiPlJlcGxheSBjYWxpYnJhdGlvbjwvYj4KICAgICAgPGxhYmVsIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1tdXRlZCkiPlNlYXNvbiZuYnNwOzxpbnB1dCBpZD0icnBsLXllYXIiIGNsYXNzPSJycGwtaW4iIHZhbHVlPSIyMDI2IiBpbnB1dG1vZGU9Im51bWVyaWMiIGF1dG9jb21wbGV0ZT0ib2ZmIiBvbmNoYW5nZT0idHZTZWFzb25MaW5rKCk7dHZUbUxpbmtzKCkiPjwvbGFiZWw+CiAgICAgIDxsYWJlbCBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpIj5CdWRnZXQmbmJzcDs8aW5wdXQgaWQ9InJwbC1idWRnZXQiIGNsYXNzPSJycGwtaW4iIHZhbHVlPSIyMDAwMCIgaW5wdXRtb2RlPSJudW1lcmljIiBhdXRvY29tcGxldGU9Im9mZiI+PC9sYWJlbD4KICAgIDwvZGl2PgogICAgPGRpdiBjbGFzcz0iZmJhciIgc3R5bGU9Im1hcmdpbjo5cHggMCAwIj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1wbGFuIiBvbmNsaWNrPSJycGxQbGFuKCkiPlBsYW48L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1pbmdlc3QiIG9uY2xpY2s9InJwbExvb3AoJ2luZ2VzdCcpIj5Jbmdlc3Q8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1yZXN1bHRzIiBvbmNsaWNrPSJycGxSZXN1bHRzKCkiPlJlc3VsdHM8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1ydW4iIG9uY2xpY2s9InJwbExvb3AoJ3J1bicpIj5SdW48L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1yZXBvcnQiIG9uY2xpY2s9InJwbFJlcG9ydCh0cnVlKSI+UmVwb3J0PC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtc3RvcCIgb25jbGljaz0icnBsU3RvcEZuKCkiIHN0eWxlPSJkaXNwbGF5Om5vbmU7Ym9yZGVyLWNvbG9yOnZhcigtLXJlZFRleHQpO2NvbG9yOnZhcigtLXJlZFRleHQpIj4mIzk2MzI7IFN0b3A8L2J1dHRvbj4KICAgIDwvZGl2PgogICAgPGRpdiBzdHlsZT0ibWFyZ2luLXRvcDo3cHgiPjxidXR0b24gY2xhc3M9InJwbC1saW5rIiBvbmNsaWNrPSJycGxUb2dnbGVDc3YoKSI+cGFzdGUgcmVzdWx0cyBDU1Y8L2J1dHRvbj4KICAgICAgPGRpdiBpZD0icnBsLWNzdndyYXAiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjx0ZXh0YXJlYSBpZD0icnBsLWNzdiIgY2xhc3M9InJwbC10YSIgcGxhY2Vob2xkZXI9ImRhdGUsYXdheSxob21lLGF3YXlfcHRzLGhvbWVfcHRzLG5ldXRyYWwmIzEwOzIwMjYtMDEtMTAsR29uemFnYSxEdWtlLDcwLDgwLCI+PC90ZXh0YXJlYT48L2Rpdj4KICAgIDwvZGl2PgogICAgPGRpdiBpZD0icnBsLWxvZyI+PC9kaXY+CiAgICA8ZGl2IGlkPSJycGwtc3RhdHVzIiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tdG9wOjhweDtsaW5lLWhlaWdodDoxLjYiPiZoZWxsaXA7PC9kaXY+CiAgICA8ZGl2IGlkPSJycGwtcmVwb3J0IiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTtsaW5lLWhlaWdodDoxLjYiPjwvZGl2PgogIDwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+VC1SYW5rIFRvcCAyNSA8c3BhbiBzdHlsZT0idGV4dC10cmFuc2Zvcm06bm9uZTtjb2xvcjp2YXIoLS1tdXRlZCkiIGlkPSJkLXlyIj48L3NwYW4+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgc3R5bGU9Im92ZXJmbG93LXg6YXV0byI+PHRhYmxlIGlkPSJkLXRibCI+PHRoZWFkPjx0cj48dGg+IzwvdGg+PHRoPlRlYW08L3RoPjx0aD5Db25mPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkak9FPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkakRFPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkalQ8L3RoPjx0aCBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+QmFydGhhZzwvdGg+PC90cj48L3RoZWFkPjx0Ym9keT48L3Rib2R5PjwvdGFibGU+PC9kaXY+CiAgPGRpdiBjbGFzcz0ibm90ZSI+PGI+RGlhZ25vc3RpY3M6PC9iPiA8c3BhbiBjbGFzcz0ibW9ubyI+L2FwaS9kZWJ1Zy9vZGRzPC9zcGFuPiBwcm9iZXMgdGhlIE9kZHMgQVBJIGxpdmUgJm1pZGRvdDsgPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvZGVidWcvdG9ydmlrPC9zcGFuPiBzaG93cyByYXcgcm93cyArIHRoZSBkZXRlY3RlZCBjb2x1bW4gbG9jayAmbWlkZG90OyA8c3BhbiBjbGFzcz0ibW9ubyI+L2FwaS9kZWJ1Zy90ZWFtbWFwPC9zcGFuPiBsaXN0cyB1bm1hdGNoZWQgbmFtZXMgKGFkZCBmaXhlcyB2aWEgPHNwYW4gY2xhc3M9Im1vbm8iPlBPU1QgL2FwaS9hZG1pbi9hbGlhczwvc3Bhbj4pLjwvZGl2Pgo8L2Rpdj4KCjxkaXYgY2xhc3M9ImZvb3RlciI+SE9PUFNCRVQgdjEuMy4xOCAmbWRhc2g7IE9kZHM6IFRoZSBPZGRzIEFQSSAmbWlkZG90OyBNb2RlbDogYmFydHRvcnZpay5jb20gJmJ1bGw7ICYjOTg4ODsgRW50ZXJ0YWlubWVudCAmYW1wOyBhbmFseXNpcyBvbmx5PC9kaXY+Cgo8ZGl2IGNsYXNzPSJibmF2Ij4KPGJ1dHRvbiBjbGFzcz0iYm5hdi1idG4gb24iIG9uY2xpY2s9ImdvKCdnYW1lcycsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48Y2lyY2xlIGN4PSIxMiIgY3k9IjEyIiByPSI5Ii8+PHBhdGggZD0iTTUuNiA1LjZjNCAzIDguOCA5LjggOS44IDE1TTE4LjQgNS42Yy00IDMtOC44IDkuOC05LjggMTVNMyAxMmgxOCIvPjwvc3ZnPjwvc3Bhbj5HYW1lczwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ2V2Jyx0aGlzKSI+PHNwYW4gY2xhc3M9ImJuYXYtaWNvIj48c3ZnIHdpZHRoPSIxOSIgaGVpZ2h0PSIxOSIgdmlld0JveD0iMCAwIDI0IDI0IiBmaWxsPSJub25lIiBzdHJva2U9ImN1cnJlbnRDb2xvciIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiPjxwYXRoIGQ9Ik0xMyAyTDQgMTRoNmwtMSA4IDktMTJoLTZsMS04eiIvPjwvc3ZnPjwvc3Bhbj5FVjwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ2JldHMnLHRoaXMpIj48c3BhbiBjbGFzcz0iYm5hdi1pY28iPjxzdmcgd2lkdGg9IjE5IiBoZWlnaHQ9IjE5IiB2aWV3Qm94PSIwIDAgMjQgMjQiIGZpbGw9Im5vbmUiIHN0cm9rZT0iY3VycmVudENvbG9yIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCI+PHBhdGggZD0iTTQgN2gxNnYzYTIgMiAwIDAwMCA0djNINHYtM2EyIDIgMCAwMDAtNFY3eiIvPjxwYXRoIGQ9Ik0xMyA3djEwIiBzdHJva2UtZGFzaGFycmF5PSIyIDMiLz48L3N2Zz48L3NwYW4+QmV0czwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ3Njb3JlcycsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48Y2lyY2xlIGN4PSIxMiIgY3k9IjEyIiByPSI5Ii8+PHBhdGggZD0iTTEyIDd2NWwzIDIiLz48L3N2Zz48L3NwYW4+U2NvcmVzPC9idXR0b24+CjxidXR0b24gY2xhc3M9ImJuYXYtYnRuIiBvbmNsaWNrPSJnbygnZGF0YScsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48cGF0aCBkPSJNNCAxOVY1TTQgMTloMTZNOCAxNnYtNU0xMiAxNlY4TTE2IDE2di0zTTIwIDE2VjYiLz48L3N2Zz48L3NwYW4+RGF0YTwvYnV0dG9uPgo8L2Rpdj4KCjxzY3JpcHQ+CnZhciBTTEFURT1udWxsLEZJTFQ9e2NvbmY6IiIsdG9wOmZhbHNlLGVkZ2U6ZmFsc2UsbWluRTowfSxTSE9XPTI1LFRIPXtNTDo0LFNQUjo1LFRPVDo1LjUsQk9PS1M6M307CnZhciBFVkQ9bnVsbCxFVkY9e3N0cmljdDp0cnVlLG1pbjowfSxSQz1udWxsLEJGSUxUPSJBTEwiLEJTSE9XPTI1OwpmdW5jdGlvbiBnbyh0LGJ0bil7WyJnYW1lcyIsImV2IiwiYmV0cyIsInNjb3JlcyIsImRhdGEiXS5mb3JFYWNoKGZ1bmN0aW9uKHMpe2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZWMtIitzKS5jbGFzc0xpc3QudG9nZ2xlKCJvbiIscz09PXQpO30pOwogIGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoIi5ibmF2LWJ0biIpLmZvckVhY2goZnVuY3Rpb24oYil7Yi5jbGFzc0xpc3QucmVtb3ZlKCJvbiIpO30pO2J0bi5jbGFzc0xpc3QuYWRkKCJvbiIpOwogIGlmKHQ9PT0iZXYiKWxvYWRFdigpO2lmKHQ9PT0iYmV0cyIpbG9hZEJldHMoKTtpZih0PT09InNjb3JlcyIpbG9hZFNjb3JlcygpO2lmKHQ9PT0iZGF0YSIpbG9hZERhdGEoKTt9CmZ1bmN0aW9uIHRnKGJ0bixrKXtGSUxUW2tdPSFGSUxUW2tdO2J0bi5jbGFzc0xpc3QudG9nZ2xlKCJvbiIsRklMVFtrXSk7YXBwbHlGaWx0ZXJzKCk7fQpmdW5jdGlvbiBtZSh2LGJ0bil7RklMVC5taW5FPXY7ZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbCgiI21pbmVkZ2UgLmNoaXAiKS5mb3JFYWNoKGZ1bmN0aW9uKGIpe2IuY2xhc3NMaXN0LnJlbW92ZSgib24iKTt9KTtidG4uY2xhc3NMaXN0LmFkZCgib24iKTthcHBseUZpbHRlcnMoKTt9CmZ1bmN0aW9uIGZtdEFtKHYpe2lmKHY9PT1udWxsfHx2PT09dW5kZWZpbmVkKXJldHVybiAiXHUyMDE0IjtyZXR1cm4gdj4wPyIrIit2OiIiK3Y7fQpmdW5jdGlvbiBmbXRTcHIodil7aWYodj09PW51bGx8fHY9PT11bmRlZmluZWQpcmV0dXJuICJcdTIwMTQiO3JldHVybiAodj4wPyIrIjoiIikrdjt9CmZ1bmN0aW9uIHRpcFRpbWUoaXNvKXt0cnl7dmFyIGQ9bmV3IERhdGUoaXNvKTtyZXR1cm4gZC50b0xvY2FsZVRpbWVTdHJpbmcoW10se2hvdXI6Im51bWVyaWMiLG1pbnV0ZToiMi1kaWdpdCJ9KTt9Y2F0Y2goZSl7cmV0dXJuICIiO319CmZ1bmN0aW9uIGxhc3RXb3JkKHMpe3JldHVybiBzP3Muc3BsaXQoIiAiKS5wb3AoKToiPyI7fQpmdW5jdGlvbiBzaG9ydE5hbWUocyl7aWYoIXMpcmV0dXJuICI/Ijt2YXIgdz1zLnNwbGl0KCIgIik7cmV0dXJuIHcubGVuZ3RoPjI/dy5zbGljZSgwLC0xKS5qb2luKCIgIik6czt9CgpmdW5jdGlvbiBiZXN0RWRnZShnKXt2YXIgYj0wO1siTUwiLCJTUFIiLCJUT1QiXS5mb3JFYWNoKGZ1bmN0aW9uKG0pe3ZhciBlPWcuZWRnZXMmJmcuZWRnZXNbbV07aWYoZSYmZS5vayYmZS5lZGdlKjEwMD5iKWI9ZS5lZGdlKjEwMDt9KTtyZXR1cm4gYjt9CmZ1bmN0aW9uIGhhc0hvdChnKXt2YXIgaD1mYWxzZTtbIk1MIiwiU1BSIiwiVE9UIl0uZm9yRWFjaChmdW5jdGlvbihtKXt2YXIgZT1nLmVkZ2VzJiZnLmVkZ2VzW21dO2lmKGUmJmUub2smJmUuaG90KWg9dHJ1ZTt9KTtyZXR1cm4gaDt9CgpmdW5jdGlvbiBhcHBseUZpbHRlcnMoKXsKICBpZighU0xBVEUpcmV0dXJuO1NIT1c9MjU7RklMVC5jb25mPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJmLWNvbmYiKS52YWx1ZTsKICByZW5kZXJHYW1lcygpOwp9CmZ1bmN0aW9uIHJlbmRlckdhbWVzKCl7CiAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcyIpLHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcy1zdGF0dXMiKTsKICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjsKICB2YXIgZ3M9KFNMQVRFLmdhbWVzfHxbXSkuc2xpY2UoKTsKICBpZihGSUxULmNvbmYpZ3M9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiBnLmFDb25mPT09RklMVC5jb25mfHxnLmhDb25mPT09RklMVC5jb25mO30pOwogIGlmKEZJTFQudG9wKWdzPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gKGcuYVJhbmsmJmcuYVJhbms8PTI1KXx8KGcuaFJhbmsmJmcuaFJhbms8PTI1KTt9KTsKICBpZihGSUxULmVkZ2UpZ3M9Z3MuZmlsdGVyKGhhc0hvdCk7CiAgaWYoRklMVC5taW5FPjApZ3M9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiBiZXN0RWRnZShnKT49RklMVC5taW5FO30pOwogIHZhciBzb3J0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJmLXNvcnQiKS52YWx1ZTsKICBpZihzb3J0PT09ImVkZ2UiKWdzLnNvcnQoZnVuY3Rpb24oYSxiKXtyZXR1cm4gYmVzdEVkZ2UoYiktYmVzdEVkZ2UoYSk7fSk7CiAgZWxzZSBncy5zb3J0KGZ1bmN0aW9uKGEsYil7cmV0dXJuIG5ldyBEYXRlKGEuY29tbWVuY2UpLW5ldyBEYXRlKGIuY29tbWVuY2UpO30pOwogIGlmKCFncy5sZW5ndGgpewogICAgdmFyIGlubmVyOwogICAgaWYoIShTTEFURS5nYW1lc3x8W10pLmxlbmd0aCl7CiAgICAgIGlubmVyPSc8Yj5ObyBOQ0FBQiBnYW1lcyBvbiB0aGUgYm9hcmQuPC9iPjxicj48YnI+JysoU0xBVEUubm90ZT9TTEFURS5ub3RlOidUaGUgc2Vhc29uIHJ1bnMgTm92ZW1iZXIgXHUyMDEzIEFwcmlsLiBUaGUgZGF0YSBsYXllciBpcyBsaXZlIGFuZCB3aWxsIHBvcHVsYXRlIHdoZW4gYm9va3MgcG9zdCB0aGUgZmlyc3Qgc2xhdGVzLicpOwogICAgfSBlbHNlIHsKICAgICAgaW5uZXI9J05vIGdhbWVzIG1hdGNoIHRoZSBjdXJyZW50IGZpbHRlcnMgXHUyMDE0ICcrKFNMQVRFLmdhbWVzLmxlbmd0aCkrJyBvbiB0aGUgc2xhdGUgdG9kYXkuIENsZWFyIGEgZmlsdGVyIHRvIHNlZSB0aGVtLic7CiAgICB9CiAgICBlbC5pbm5lckhUTUw9JzxkaXYgY2xhc3M9ImVtcHR5Ij4nK2lubmVyKyc8L2Rpdj4nO3JldHVybjsKICB9CiAgdmFyIGh0bWw9Z3Muc2xpY2UoMCxTSE9XKS5tYXAoZnVuY3Rpb24oZyl7CiAgICB2YXIgYVI9Zy5hUmFuayYmZy5hUmFuazw9MjU/JzxzcGFuIGNsYXNzPSJyayI+IycrZy5hUmFuaysnPC9zcGFuPic6Jyc7CiAgICB2YXIgaFI9Zy5oUmFuayYmZy5oUmFuazw9MjU/JzxzcGFuIGNsYXNzPSJyayI+IycrZy5oUmFuaysnPC9zcGFuPic6Jyc7CiAgICB2YXIgbWV0YT0nPHNwYW4gY2xhc3M9InRhZyB0YWctdGltZSI+Jyt0aXBUaW1lKGcuY29tbWVuY2UpKyc8L3NwYW4+JzsKICAgIGlmKGcubmV1dHJhbCltZXRhKz0nPHNwYW4gY2xhc3M9InRhZyB0YWctbiI+Tjwvc3Bhbj4nOwogICAgbWV0YSs9JzxzcGFuIGNsYXNzPSJ0YWcgdGFnLWJrIj4nK2cubkJvb2tzKycgYms8L3NwYW4+JzsKICAgIGlmKGcucGlja3MmJmcucGlja3MubGVuZ3RoKW1ldGErPSc8c3BhbiBjbGFzcz0idGFnIiBzdHlsZT0iYmFja2dyb3VuZDpyZ2JhKDI0LDE4NCwxMjQsLjEyKTtjb2xvcjp2YXIoLS1ncmVlbik7Ym9yZGVyOjFweCBzb2xpZCByZ2JhKDI0LDE4NCwxMjQsLjM1KSI+XHUyNjA1ICcrZy5waWNrcy5qb2luKCIvIikrJzwvc3Bhbj4nOwogICAgdmFyIHByb2osZWRnZXMsc2hhcnA9IiI7CiAgICBpZighZy5tb2RlbGVkKXsKICAgICAgcHJvaj0nPGRpdiBjbGFzcz0iZy1wcm9qIj48c3BhbiBjbGFzcz0iYXdhaXQiPicrKGcubW9kZWxSZWFzb258fCJ1bnJhdGVkIHRlYW0iKSsnPC9zcGFuPjwvZGl2Pic7ZWRnZXM9IiI7CiAgICB9IGVsc2UgewogICAgICBwcm9qPSc8ZGl2IGNsYXNzPSJnLXByb2oiPicrCiAgICAgICAgJzxzcGFuPlByb2ogPGIgY2xhc3M9Im1vbm8iPicrZy5wcm9qLmFQdHMudG9GaXhlZCgwKSsnXHUyMDEzJytnLnByb2ouaFB0cy50b0ZpeGVkKDApKyc8L2I+PC9zcGFuPicrCiAgICAgICAgJzxzcGFuPk1hcmdpbiA8YiBjbGFzcz0ibW9ubyI+JytsYXN0V29yZChnLmhvbWUpLnNsaWNlKDAsMykudG9VcHBlckNhc2UoKSsnICcrZm10U3ByKCsoLShnLnByb2oubWFyZ2luKSkudG9GaXhlZCgxKSkrJzwvYj4nKyhnLmJvb2suc3BySCE9PW51bGw/JyA8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj5ib29rICcrZm10U3ByKGcuYm9vay5zcHJIKSsnPC9zcGFuPic6JycpKyc8L3NwYW4+JysKICAgICAgICAnPHNwYW4+VG90YWwgPGIgY2xhc3M9Im1vbm8iPicrZy5wcm9qLnRvdGFsLnRvRml4ZWQoMSkrJzwvYj4nKyhnLmJvb2sudG90IT09bnVsbD8nIDxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPmJvb2sgJytnLmJvb2sudG90Kyc8L3NwYW4+JzonJykrJzwvc3Bhbj4nKwogICAgICAnPC9kaXY+JzsKICAgICAgZWRnZXM9JzxkaXYgY2xhc3M9ImctZWRnZXMiPicrWyJNTCIsIlNQUiIsIlRPVCJdLm1hcChmdW5jdGlvbihtKXsKICAgICAgICB2YXIgZT1nLmVkZ2VzW21dOwogICAgICAgIGlmKCFlfHwhZS5vaylyZXR1cm4gJzxzcGFuIGNsYXNzPSJlZCI+PHNwYW4gY2xhc3M9InNkIj4nK20rJzwvc3Bhbj48c3BhbiBjbGFzcz0iYXdhaXQiIHN0eWxlPSJwYWRkaW5nOjAgNHB4Ij4nKyhlJiZlLnJlYXNvbj9lLnJlYXNvbjoiXHUyMDE0IikrJzwvc3Bhbj48L3NwYW4+JzsKICAgICAgICByZXR1cm4gJzxzcGFuIGNsYXNzPSJlZCcrKGUuaG90PyIgaG90IjoiIikrJyI+PHNwYW4gY2xhc3M9InNkIj4nK20rJyAnK2UubGFiZWwrJzwvc3Bhbj4rJysoZS5lZGdlKjEwMCkudG9GaXhlZCgxKSsnJTwvc3Bhbj4nOwogICAgICB9KS5qb2luKCIiKSsnPC9kaXY+JzsKICAgICAgaWYoZy5zaGFycCYmKGcuc2hhcnAuc3BySCE9PW51bGx8fGcuc2hhcnAudG90IT09bnVsbCkpewogICAgICAgIHNoYXJwPSc8ZGl2IGNsYXNzPSJnLXNoYXJwIj48Yj5QaW5uYWNsZTwvYj4gJysoZy5zaGFycC5zcHJIIT09bnVsbD8oInNwcmVhZCAiK2ZtdFNwcihnLnNoYXJwLnNwckgpKToiIikrKGcuc2hhcnAudG90IT09bnVsbD8oIiBcdTAwYjcgdG90YWwgIitnLnNoYXJwLnRvdCk6IiIpKyhnLnNoYXJwLnBIb21lIT09bnVsbD8oIiBcdTAwYjcgbm8tdmlnIGhvbWUgIisoZy5zaGFycC5wSG9tZSoxMDApLnRvRml4ZWQoMCkrIiUiKToiIikrJzwvZGl2Pic7CiAgICAgIH0KICAgIH0KICAgIHJldHVybiAnPGRpdiBjbGFzcz0iZ2NhcmQiPjxkaXYgY2xhc3M9ImctdG9wIj48ZGl2IGNsYXNzPSJnLXRlYW1zIj4nK2FSK3Nob3J0TmFtZShnLmF3YXkpKyc8c3BhbiBjbGFzcz0iYXQiPkA8L3NwYW4+JytoUitzaG9ydE5hbWUoZy5ob21lKSsnPC9kaXY+PGRpdiBjbGFzcz0iZy1tZXRhIj4nK21ldGErJzwvZGl2PjwvZGl2PicrcHJvaitlZGdlcytzaGFycCsnPC9kaXY+JzsKICB9KS5qb2luKCIiKTsKICBpZihncy5sZW5ndGg+U0hPVylodG1sKz0nPGJ1dHRvbiBjbGFzcz0ibW9yZSIgb25jbGljaz0iU0hPVys9MjU7cmVuZGVyR2FtZXMoKSI+U2hvdyBtb3JlICgnKyhncy5sZW5ndGgtU0hPVykrJyByZW1haW5pbmcpPC9idXR0b24+JzsKICBlbC5pbm5lckhUTUw9aHRtbDsKfQpmdW5jdGlvbiByZW5kZXJLcGlzKCl7CiAgdmFyIGM9U0xBVEUuY292ZXJhZ2V8fHt9LGs9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImtwaXMiKTsKICB2YXIgaG90PShTTEFURS5nYW1lc3x8W10pLmZpbHRlcihoYXNIb3QpLmxlbmd0aDsKICBrLmlubmVySFRNTD0KICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5HYW1lczwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGMuZ2FtZXN8fDApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhjLmxpbmVkfHwwKSsnIHdpdGggbGluZXM8L2Rpdj48L2Rpdj4nKwogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPk1vZGVsZWQ8L2Rpdj48ZGl2IGNsYXNzPSJ2Ij4nKyhjLm1vZGVsZWR8fDApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj5Ub3J2aWstcmF0ZWQgYm90aCBzaWRlczwvZGl2PjwvZGl2PicrCiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+RWRnZXM8L2Rpdj48ZGl2IGNsYXNzPSJ2IiBzdHlsZT0iY29sb3I6JysoaG90PjA/InZhcigtLWdyZWVuKSI6InZhcigtLW11dGVkKSIpKyciPicraG90Kyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj5NTCAnK1RILk1MKyclIC8gU1BSICcrVEguU1BSKyclIC8gVE9UICcrVEguVE9UKyclPC9kaXY+PC9kaXY+JzsKICB2YXIgY29uZj17fTsoU0xBVEUuZ2FtZXN8fFtdKS5mb3JFYWNoKGZ1bmN0aW9uKGcpe2lmKGcuYUNvbmYpY29uZltnLmFDb25mXT0xO2lmKGcuaENvbmYpY29uZltnLmhDb25mXT0xO30pOwogIHZhciBzZWw9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImYtY29uZiIpLGN1cj1zZWwudmFsdWU7CiAgc2VsLmlubmVySFRNTD0nPG9wdGlvbiB2YWx1ZT0iIj5BbGwgY29uZmVyZW5jZXM8L29wdGlvbj4nK09iamVjdC5rZXlzKGNvbmYpLnNvcnQoKS5tYXAoZnVuY3Rpb24oeCl7cmV0dXJuICc8b3B0aW9uJysoeD09PWN1cj8iIHNlbGVjdGVkIjoiIikrJz4nK3grJzwvb3B0aW9uPic7fSkuam9pbigiIik7Cn0KZnVuY3Rpb24gbG9hZFNsYXRlKGZvcmNlKXsKICBpZihmb3JjZSl7dmFyIHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcy1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBMb2FkaW5nIHNsYXRlJmhlbGxpcDsnO30KICByZXR1cm4gZmV0Y2goIi9hcGkvc2xhdGUiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGQpewogICAgaWYoZC5vaz09PWZhbHNlKXRocm93IG5ldyBFcnJvcihkLmVycm9yfHwic2xhdGUgZmFpbGVkIik7CiAgICBTTEFURT1kOwogICAgaWYoZC50aHJlc2hvbGRzKXtUSD1kLnRocmVzaG9sZHM7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInRoLW1sIikudGV4dENvbnRlbnQ9VEguTUw7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInRoLXNwciIpLnRleHRDb250ZW50PVRILlNQUjtkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidGgtdG90IikudGV4dENvbnRlbnQ9VEguVE9UO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0aC1iayIpLnRleHRDb250ZW50PVRILkJPT0tTO30KICAgIHJlbmRlcktwaXMoKTtyZW5kZXJHYW1lcygpOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImNvbm4iKS5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1ncmVlbikiPiYjOTY3OTs8L3NwYW4+ICcrKGQucXVvdGEmJmQucXVvdGEucmVtYWluaW5nIT1udWxsPygicXVvdGEgIitkLnF1b3RhLnJlbWFpbmluZyk6ImNvbm5lY3RlZCIpOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpewogICAgdmFyIHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcy1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7CiAgICBzdC5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5ODg4OyAnK2UubWVzc2FnZSsnPC9zcGFuPiAmbWRhc2g7IDxidXR0b24gY2xhc3M9Imhkci1idG4iIG9uY2xpY2s9ImxvYWRBbGwodHJ1ZSkiPlJldHJ5PC9idXR0b24+JzsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJjb25uIikuaW5uZXJIVE1MPSc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tcmVkVGV4dCkiPiYjOTY3OTs8L3NwYW4+IGVycm9yJzsKICB9KTsKfQpmdW5jdGlvbiBzcm93KGcpewogIHZhciBsaXZlPSFnLmNvbXBsZXRlZCYmZy5zY29yZXM7CiAgdmFyIHNjPWcuc2NvcmVzP2cuc2NvcmVzLm1hcChmdW5jdGlvbihzKXtyZXR1cm4gcy5zY29yZTt9KS5qb2luKCIgXHUyMDEzICIpOiIiOwogIHJldHVybiAnPGRpdiBjbGFzcz0ic3JvdyI+PGRpdj48ZGl2IGNsYXNzPSJ0Ij4nK3Nob3J0TmFtZShnLmF3YXlfdGVhbSkrJyBAICcrc2hvcnROYW1lKGcuaG9tZV90ZWFtKSsnPC9kaXY+PGRpdiBjbGFzcz0ic3QiPicrKGcuY29tcGxldGVkPyJGaW5hbCI6KGxpdmU/JzxzcGFuIGNsYXNzPSJsaXZlLWRvdCI+JiM5Njc5OyBsaXZlPC9zcGFuPic6dGlwVGltZShnLmNvbW1lbmNlX3RpbWUpKSkrJzwvZGl2PjwvZGl2PjxkaXYgY2xhc3M9InNjIj4nKyhzY3x8Ilx1MjAxNCIpKyc8L2Rpdj48L2Rpdj4nOwp9CmZ1bmN0aW9uIGxvYWRTY29yZXMoKXsKICB2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNjb3Jlcy1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBMb2FkaW5nIHNjb3JlcyZoZWxsaXA7JzsKICBmZXRjaCgiL2FwaS9zY29yZXMiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGQpewogICAgc3Quc3R5bGUuZGlzcGxheT0ibm9uZSI7CiAgICB2YXIgZ3M9ZC5nYW1lc3x8W107CiAgICB2YXIgbGl2ZT1ncy5maWx0ZXIoZnVuY3Rpb24oZyl7cmV0dXJuICFnLmNvbXBsZXRlZCYmZy5zY29yZXM7fSk7CiAgICB2YXIgZG9uZT1ncy5maWx0ZXIoZnVuY3Rpb24oZyl7cmV0dXJuIGcuY29tcGxldGVkO30pOwogICAgdmFyIHVwPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gIWcuY29tcGxldGVkJiYhZy5zY29yZXM7fSk7CiAgICBmdW5jdGlvbiBwdXQoaWQsaGQsYXJyKXtkb2N1bWVudC5nZXRFbGVtZW50QnlJZChoZCkuc3R5bGUuZGlzcGxheT1hcnIubGVuZ3RoPyJibG9jayI6Im5vbmUiO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKGlkKS5pbm5lckhUTUw9YXJyLm1hcChzcm93KS5qb2luKCIiKTt9CiAgICBwdXQoInMtbGl2ZSIsInNoLWxpdmUiLGxpdmUpO3B1dCgicy1kb25lIiwic2gtZG9uZSIsZG9uZSk7cHV0KCJzLXVwIiwic2gtdXAiLHVwLnNsaWNlKDAsNDApKTsKICAgIGlmKCFncy5sZW5ndGgpe3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxkaXYgY2xhc3M9ImVtcHR5Ij48Yj5ObyBnYW1lcyBpbiB0aGUgc2NvcmVzIHdpbmRvdy48L2I+PGJyPjxicj5TZWFzb24gcnVucyBOb3ZlbWJlciBcdTIwMTMgQXByaWwuPC9kaXY+Jzt9CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7c3QuaW5uZXJIVE1MPSc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tcmVkVGV4dCkiPiYjOTg4ODsgJytlLm1lc3NhZ2UrJzwvc3Bhbj4nO30pOwp9CmZ1bmN0aW9uIGxvYWREYXRhKCl7CiAgUHJvbWlzZS5hbGxTZXR0bGVkKFtmZXRjaCgiL2FwaS9oZWFsdGgiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KSxmZXRjaCgiL2FwaS9yYXRpbmdzP3RvcD0yNSIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLGZldGNoKCIvYXBpL2RlYnVnL3RlYW1tYXA/c3VtbWFyeT0xIikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSldKS50aGVuKGZ1bmN0aW9uKHJlcyl7CiAgICB2YXIgaD1yZXNbMF0uc3RhdHVzPT09ImZ1bGZpbGxlZCI/cmVzWzBdLnZhbHVlOnt9OwogICAgdmFyIHJ0PXJlc1sxXS5zdGF0dXM9PT0iZnVsZmlsbGVkIj9yZXNbMV0udmFsdWU6e307CiAgICB2YXIgdG09cmVzWzJdLnN0YXR1cz09PSJmdWxmaWxsZWQiP3Jlc1syXS52YWx1ZTp7fTsKICAgIHZhciB0dj1oLnRvcnZpa3x8e307CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZC1rcGlzIikuaW5uZXJIVE1MPQogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+T2RkcyBxdW90YTwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyI+JysoaC5xdW90YSYmaC5xdW90YS5yZW1haW5pbmchPW51bGw/aC5xdW90YS5yZW1haW5pbmc6Ilx1MjAxNCIpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj5jcmVkaXRzIHJlbWFpbmluZzwvZGl2PjwvZGl2PicrCiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5Ub3J2aWs8L2Rpdj48ZGl2IGNsYXNzPSJ2Ij4nKyh0di50ZWFtc3x8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKHR2LnllYXJ8fCIiKSsnICZtaWRkb3Q7ICcrKHR2Lm1vZGV8fCJub3QgbG9hZGVkIikrKHR2LmFnZU1pbiE9bnVsbD8oJyAmbWlkZG90OyAnK3R2LmFnZU1pbisnbSBvbGQnKTonJykrJzwvZGl2PjwvZGl2PicrCiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5SZWRpczwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGgucmVkaXM/Im9uIjoib2ZmIikrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKGgucmVkaXM/InBlcnNpc3RlbmNlIGFjdGl2ZSI6InNldCBVcHN0YXNoIGVudiB2YXJzIikrJzwvZGl2PjwvZGl2Pic7CiAgICAoZnVuY3Rpb24oKXsKICAgICAgdmFyIGhoPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJkLWhlYWx0aCIpLGhwPVtdLGhzZXY9Im9rIjsKICAgICAgaWYoaC5zZWFzb25BY3RpdmU9PT1mYWxzZSl7aHAucHVzaCgnPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+JiM5Njc5OyBPZmZzZWFzb24gXHUyMDE0IG9kZHMgcG9sbGluZyBwYXVzZWQgKHNhdmluZyBxdW90YSk8L3NwYW4+Jyk7fQogICAgICBlbHNlIGlmKGgub2Rkc0tleT09PWZhbHNlKXtoc2V2PSJ3YXJuIjtocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6I2UwYTgzYSI+JiM5ODg4OyBPRERTX0FQSV9LRVkgbm90IHNldDwvc3Bhbj4nKTt9CiAgICAgIGVsc2UgaWYoaC5sYXN0T2Rkc0Vycm9yKXtoc2V2PSJlcnIiO2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5ODg4OyBPZGRzIGZldGNoIEZBSUxJTkc6ICcrKGgubGFzdE9kZHNFcnJvci5tc2d8fCJlcnJvciIpKyc8L3NwYW4+Jyk7fQogICAgICBlbHNlIGlmKGguc2xhdGVBZ2VNaW4hPW51bGwmJmguc2xhdGVBZ2VNaW4+NjApe2hzZXY9Indhcm4iO2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjojZTBhODNhIj4mIzk4ODg7IFNsYXRlIHN0YWxlICgnK2guc2xhdGVBZ2VNaW4rJ20gb2xkKSBcdTIwMTQgbGFzdCBmZXRjaCBoYWQgJysoaC5sYXN0U2xhdGVHYW1lcyE9bnVsbD9oLmxhc3RTbGF0ZUdhbWVzOiI/IikrJyBnYW1lczwvc3Bhbj4nKTt9CiAgICAgIGVsc2V7aHAucHVzaCgnPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWdyZWVuKSI+JiM5Njc5OyBMaXZlIG9kZHMgT0snKyhoLmxhc3RTbGF0ZUdhbWVzIT1udWxsPygnIFx1MjAxNCAnK2gubGFzdFNsYXRlR2FtZXMrJyBnYW1lcywgJysoaC5zbGF0ZUFnZU1pbiE9bnVsbD9oLnNsYXRlQWdlTWluKydtIGFnbyc6Imp1c3Qgbm93IikpOiIiKSsnPC9zcGFuPicpO30KICAgICAgaWYodHYuZXJyb3Ipe2lmKGhzZXYhPT0iZXJyIiloc2V2PSJ3YXJuIjtocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6I2UwYTgzYSI+JiM5ODg4OyBSYXRpbmdzOiAnK3R2LmVycm9yKyc8L3NwYW4+Jyk7fQogICAgICBlbHNlIGlmKHR2LnRlYW1zKXtocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tZGltKSI+UmF0aW5nczogJyt0di50ZWFtcysnIHRlYW1zIFx1MDBiNyAnKyh0di55ZWFyfHwiIikrJyAnKyh0di5tb2RlfHwiIikrKHR2LmFnZU1pbiE9bnVsbD8oJyBcdTAwYjcgJyt0di5hZ2VNaW4rJ20gb2xkJyk6IiIpKyc8L3NwYW4+Jyk7fQogICAgICB2YXIgb3Q9aC50cmFja2VyJiZoLnRyYWNrZXIub3BlbjtpZihvdClocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tZGltKSI+JytvdCsnIG9wZW4gcGljaycrKG90PjE/InMiOiIiKSsnIGF3YWl0aW5nIGdyYWRlPC9zcGFuPicpOwogICAgICBoaC5zdHlsZS5kaXNwbGF5PSJibG9jayI7CiAgICAgIGhoLnN0eWxlLmJvcmRlckNvbG9yPWhzZXY9PT0iZXJyIj8icmdiYSgyMjAsODAsODAsLjU1KSI6KGhzZXY9PT0id2FybiI/InJnYmEoMjI0LDE2OCw1OCwuNSkiOiIiKTsKICAgICAgaGguaW5uZXJIVE1MPSc8YiBzdHlsZT0iZm9udC1zaXplOjEycHgiPkxpdmUgc3RhdHVzPC9iPjxkaXYgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O21hcmdpbi10b3A6NXB4O2xpbmUtaGVpZ2h0OjEuOCI+JytocC5qb2luKCI8YnI+IikrJzwvZGl2Pic7CiAgICB9KSgpOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImQtbWFwIikuaW5uZXJIVE1MPSc8YiBzdHlsZT0iZm9udC1zaXplOjEycHgiPlRlYW0tbmFtZSBtYXA8L2I+PGRpdiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tdG9wOjRweCI+JysodG0ubWF0Y2hlZCE9bnVsbD8odG0ubWF0Y2hlZCsiIG1hdGNoZWQgXHUwMGI3ICIrdG0udW5tYXRjaGVkKyIgdW5tYXRjaGVkIisodG0udW5tYXRjaGVkPjA/JyBcdTIwMTQgcmV2aWV3IDxzcGFuIGNsYXNzPSJtb25vIj4vYXBpL2RlYnVnL3RlYW1tYXA8L3NwYW4+JzoiIikpOiJwb3B1bGF0ZXMgb25jZSBhIHNsYXRlIGhhcyBiZWVuIGZldGNoZWQiKSsnPC9kaXY+JzsKICAgIHJwbFN0YXR1cygpO3JwbFJlcG9ydChmYWxzZSk7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZC15ciIpLnRleHRDb250ZW50PXR2LnllYXI/KCJcdTIwMTQgIit0di55ZWFyKToiIjsKICAgIHZhciB0Yj1kb2N1bWVudC5xdWVyeVNlbGVjdG9yKCIjZC10YmwgdGJvZHkiKTsKICAgIHRiLmlubmVySFRNTD0ocnQudGVhbXN8fFtdKS5tYXAoZnVuY3Rpb24odCl7cmV0dXJuICc8dHI+PHRkIGNsYXNzPSJtb25vIj4nK3QucmFuaysnPC90ZD48dGQ+Jyt0LnRlYW0rJzwvdGQ+PHRkIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPicrKHQuY29uZnx8IiIpKyc8L3RkPjx0ZCBjbGFzcz0ibW9ubyIgc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPicrdC5hZGpvZS50b0ZpeGVkKDEpKyc8L3RkPjx0ZCBjbGFzcz0ibW9ubyIgc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPicrdC5hZGpkZS50b0ZpeGVkKDEpKyc8L3RkPjx0ZCBjbGFzcz0ibW9ubyIgc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPicrdC5hZGp0LnRvRml4ZWQoMSkrJzwvdGQ+PHRkIGNsYXNzPSJtb25vIiBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+Jyt0LmJhcnRoYWcudG9GaXhlZCgzKSsnPC90ZD48L3RyPic7fSkuam9pbigiIil8fCc8dHI+PHRkIGNvbHNwYW49IjciIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPlJhdGluZ3Mgbm90IGxvYWRlZCBcdTIwMTQgY2hlY2sgL2FwaS9kZWJ1Zy90b3J2aWs8L3RkPjwvdHI+JzsKICB9KTsKfQpmdW5jdGlvbiBldlN0cmljdChidG4pe0VWRi5zdHJpY3Q9IUVWRi5zdHJpY3Q7YnRuLmNsYXNzTGlzdC50b2dnbGUoIm9uIixFVkYuc3RyaWN0KTtyZW5kZXJFdigpO30KZnVuY3Rpb24gZXZNaW4odixidG4pe0VWRi5taW49djt2YXIgYnM9YnRuLnBhcmVudE5vZGUucXVlcnlTZWxlY3RvckFsbCgiLmNoaXAiKTtmb3IodmFyIGk9MTtpPGJzLmxlbmd0aDtpKyspYnNbaV0uY2xhc3NMaXN0LnJlbW92ZSgib24iKTtidG4uY2xhc3NMaXN0LmFkZCgib24iKTtyZW5kZXJFdigpO30KZnVuY3Rpb24gZXZMYWJlbChyKXtpZihyLm1rdD09PSJNTCIpcmV0dXJuIChyLnNpZGU9PT0iaG9tZSI/c2hvcnROYW1lKHIuaG9tZSk6c2hvcnROYW1lKHIuYXdheSkpKyIgTUwiO2lmKHIubWt0PT09IlNQUiIpcmV0dXJuIChyLnNpZGU9PT0iaG9tZSI/c2hvcnROYW1lKHIuaG9tZSk6c2hvcnROYW1lKHIuYXdheSkpKyIgIitmbXRTcHIoci5saW5lKTtyZXR1cm4gKHIuc2lkZT09PSJvdmVyIj8iT3ZlciAiOiJVbmRlciAiKStyLmxpbmU7fQpmdW5jdGlvbiBldlJvdyhyKXsKICB2YXIgYmFkZ2U9ci5zdHJvbmc/JzxzcGFuIGNsYXNzPSJ0YWciIHN0eWxlPSJiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMTIpO2NvbG9yOnZhcigtLWdyZWVuKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjQsMTg0LDEyNCwuMzUpIj5TVFJPTkc8L3NwYW4+JzonPHNwYW4gY2xhc3M9InRhZyB0YWctYmsiPldFQUs8L3NwYW4+JzsKICB2YXIgbWRsPXIubW9kZWw/KHIubW9kZWwuYWdyZWU/JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1ncmVlbikiPiYjMTAwMDM7IG1vZGVsICcrKHIubW9kZWwucCoxMDApLnRvRml4ZWQoMCkrJyU8L3NwYW4+JzonPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+JiMxMDAwNzsgbW9kZWwgJysoci5tb2RlbC5wKjEwMCkudG9GaXhlZCgwKSsnJTwvc3Bhbj4nKTonPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+Jm1kYXNoOyB1bm1vZGVsZWQ8L3NwYW4+JzsKICByZXR1cm4gJzxkaXYgY2xhc3M9ImdjYXJkIj48ZGl2IGNsYXNzPSJnLXRvcCI+PGRpdiBjbGFzcz0iZy10ZWFtcyI+JytzaG9ydE5hbWUoci5hd2F5KSsnPHNwYW4gY2xhc3M9ImF0Ij5APC9zcGFuPicrc2hvcnROYW1lKHIuaG9tZSkrJzwvZGl2PjxkaXYgY2xhc3M9ImctbWV0YSI+PHNwYW4gY2xhc3M9InRhZyB0YWctdGltZSI+Jyt0aXBUaW1lKHIuY29tbWVuY2UpKyc8L3NwYW4+JytiYWRnZSsnPC9kaXY+PC9kaXY+JysKICAnPGRpdiBjbGFzcz0iZy1wcm9qIj48c3Bhbj48Yj4nK2V2TGFiZWwocikrJzwvYj4gJytmbXRBbShyLm9kZHMpKycgQCAnK3IuYm9vaysnPC9zcGFuPjxzcGFuPkVWIDxiIGNsYXNzPSJtb25vIiBzdHlsZT0iY29sb3I6dmFyKC0tZ3JlZW4pIj4rJytyLmV2UGN0LnRvRml4ZWQoMSkrJyU8L2I+PC9zcGFuPjxzcGFuPmZhaXIgPGIgY2xhc3M9Im1vbm8iPicrKHIucEZhaXIqMTAwKS50b0ZpeGVkKDEpKyclPC9iPjwvc3Bhbj4nKyhyLmdhcCE9bnVsbD8nPHNwYW4+Z2FwIDxiIGNsYXNzPSJtb25vIj4nK3IuZ2FwLnRvRml4ZWQoMSkrJzwvYj48L3NwYW4+JzonJykrJzwvZGl2PicrCiAgJzxkaXYgY2xhc3M9Imctc2hhcnAiPicrbWRsKycgJm1pZGRvdDsgJytyLm5Cb29rcysnIGJvb2snKyhyLm5Cb29rcz4xPyJzIjoiIikrJyBhdCB0aGlzIGxpbmU8L2Rpdj48L2Rpdj4nOwp9CmZ1bmN0aW9uIHJlbmRlckV2KCl7CiAgaWYoIUVWRClyZXR1cm47CiAgdmFyIGM9RVZELmNvdmVyYWdlfHx7fTsKICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYta3BpcyIpLmlubmVySFRNTD0KICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5DYW5kaWRhdGVzPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoYy5jYW5kaWRhdGVzfHwwKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoYy5zdHJvbmd8fDApKycgc3Ryb25nPC9kaXY+PC9kaXY+JysKICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5BbmNob3I8L2Rpdj48ZGl2IGNsYXNzPSJ2Ij4nKyhjLndpdGhTaGFycHx8MCkrJy8nKyhjLmxpbmVkfHwwKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+Z2FtZXMgdy8gUGlubmFjbGU8L2Rpdj48L2Rpdj4nKwogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPkFyYnM8L2Rpdj48ZGl2IGNsYXNzPSJ2IiBzdHlsZT0iY29sb3I6JysoKEVWRC5hcmJzfHxbXSkubGVuZ3RoPyJ2YXIoLS1ncmVlbikiOiJ2YXIoLS1tdXRlZCkiKSsnIj4nKygoRVZELmFyYnN8fFtdKS5sZW5ndGgpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj50d28td2F5IE1MPC9kaXY+PC9kaXY+JzsKICBpZihFVkQuY2ZnKXtkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYtZmxvb3IiKS50ZXh0Q29udGVudD1FVkQuY2ZnLm1pbjtkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYtZ2FwIikudGV4dENvbnRlbnQ9RVZELmNmZy5zdHJvbmdHYXA7fQogIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1hcmJzIikuaW5uZXJIVE1MPShFVkQuYXJic3x8W10pLm1hcChmdW5jdGlvbihhKXsKICAgIHJldHVybiAnPGRpdiBjbGFzcz0iY2FyZCIgc3R5bGU9ImJvcmRlcjoxcHggc29saWQgcmdiYSgyNCwxODQsMTI0LC40KSI+PGIgc3R5bGU9ImZvbnQtc2l6ZToxMnB4O2NvbG9yOnZhcigtLWdyZWVuKSI+QVJCICsnK2EuYXJiUGN0LnRvRml4ZWQoMikrJyU8L2I+PGRpdiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tdG9wOjNweCI+JytzaG9ydE5hbWUoYS5hd2F5KSsnICcrZm10QW0oYS5sZWdBLm9kZHMpKycgQCAnK2EubGVnQS5ib29rKycgJm5ic3A7LyZuYnNwOyAnK3Nob3J0TmFtZShhLmhvbWUpKycgJytmbXRBbShhLmxlZ0gub2RkcykrJyBAICcrYS5sZWdILmJvb2srJzwvZGl2PjwvZGl2Pic7CiAgfSkuam9pbigiIik7CiAgdmFyIHJvd3M9KEVWRC5yb3dzfHxbXSkuZmlsdGVyKGZ1bmN0aW9uKHIpe2lmKEVWRi5zdHJpY3QmJiFyLnN0cm9uZylyZXR1cm4gZmFsc2U7aWYoci5ldlBjdDxFVkYubWluKXJldHVybiBmYWxzZTtyZXR1cm4gdHJ1ZTt9KTsKICB2YXIgZWw9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LXJvd3MiKTsKICBpZighcm93cy5sZW5ndGgpewogICAgdmFyIGlubmVyOwogICAgaWYoIShFVkQucm93c3x8W10pLmxlbmd0aCl7aW5uZXI9RVZELm5vdGU/KCc8Yj5ObyBjYW5kaWRhdGVzLjwvYj48YnI+PGJyPicrRVZELm5vdGUpOighYy5saW5lZD8nPGI+Tm8gbGluZWQgZ2FtZXMgb24gdGhlIGJvYXJkLjwvYj48YnI+PGJyPlRoZSBzY3JlZW4gcG9wdWxhdGVzIHdoZW4gYm9va3MgcG9zdCBzbGF0ZXMuJzooIWMud2l0aFNoYXJwPyc8Yj5ObyBQaW5uYWNsZSBhbmNob3JzIHlldC48L2I+PGJyPjxicj5QaW5uYWNsZSB0eXBpY2FsbHkgcG9zdHMgY2xvc2VyIHRvIHRpcDsgdGhlIHNjcmVlbiBuZWVkcyBpdHMgbm8tdmlnIGxpbmUgYXMgdGhlIGZhaXIgYmFzZWxpbmUuJzonPGI+Tm8gK0VWIGZvdW5kIGFib3ZlIHRoZSAnKyhFVkQuY2ZnP0VWRC5jZmcubWluOjIpKyclIGZsb29yLjwvYj48YnI+PGJyPlJldGFpbCBpcyBpbiBsaW5lIHdpdGggUGlubmFjbGUgcmlnaHQgbm93LicpKTt9CiAgICBlbHNlIGlubmVyPShFVkQucm93cy5sZW5ndGgpKycgY2FuZGlkYXRlJysoRVZELnJvd3MubGVuZ3RoPjE/InMiOiIiKSsnIGhpZGRlbiBieSBmaWx0ZXJzIOKAlCB0b2dnbGUgU3Ryb25nIG9ubHkgb3IgbG93ZXIgbWluIEVWLic7CiAgICBlbC5pbm5lckhUTUw9JzxkaXYgY2xhc3M9ImVtcHR5Ij4nK2lubmVyKyc8L2Rpdj4nO3JldHVybjsKICB9CiAgZWwuaW5uZXJIVE1MPXJvd3MubWFwKGV2Um93KS5qb2luKCIiKTsKfQpmdW5jdGlvbiBsb2FkRXYoKXsKICB2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IFNjYW5uaW5nIHZzIFBpbm5hY2xl4oCmJzsKICBmZXRjaCgiL2FwaS9ldiIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oZCl7CiAgICBpZihkLm9rPT09ZmFsc2UpdGhyb3cgbmV3IEVycm9yKGQuZXJyb3J8fCJldiBmYWlsZWQiKTsKICAgIHN0LnN0eWxlLmRpc3BsYXk9Im5vbmUiO0VWRD1kO3JlbmRlckV2KCk7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7c3QuaW5uZXJIVE1MPSc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tcmVkVGV4dCkiPuKaoCAnK2UubWVzc2FnZSsnPC9zcGFuPic7fSk7Cn0KZnVuY3Rpb24gc3BhcmtTdmcoZGFpbHkpewogIHZhciB3PTMwMCxoPTY0LHBhZD01LHZhbHM9ZGFpbHkubWFwKGZ1bmN0aW9uKHgpe3JldHVybiB4LmN1bTt9KTsKICB2YXIgbW49TWF0aC5taW4oMCxNYXRoLm1pbi5hcHBseShudWxsLHZhbHMpKSxteD1NYXRoLm1heCgwLE1hdGgubWF4LmFwcGx5KG51bGwsdmFscykpOwogIGlmKG14PT09bW4pbXg9bW4rMTsKICBmdW5jdGlvbiBYKGkpe3JldHVybiBwYWQraSoody0yKnBhZCkvKGRhaWx5Lmxlbmd0aC0xKTt9CiAgZnVuY3Rpb24gWSh2KXtyZXR1cm4gaC1wYWQtKHYtbW4pKihoLTIqcGFkKS8obXgtbW4pO30KICB2YXIgZD1kYWlseS5tYXAoZnVuY3Rpb24oeCxpKXtyZXR1cm4gKGk/IkwiOiJNIikrWChpKS50b0ZpeGVkKDEpKyIgIitZKHguY3VtKS50b0ZpeGVkKDEpO30pLmpvaW4oIiAiKTsKICB2YXIgY29sPXZhbHNbdmFscy5sZW5ndGgtMV0+PTA/InZhcigtLWdyZWVuKSI6InZhcigtLXJlZFRleHQpIjsKICByZXR1cm4gJzxzdmcgdmlld0JveD0iMCAwICcrdysnICcraCsnIiBzdHlsZT0id2lkdGg6MTAwJTtoZWlnaHQ6NjRweDtkaXNwbGF5OmJsb2NrO21hcmdpbi10b3A6NnB4Ij48bGluZSB4MT0iMCIgeTE9IicrWSgwKS50b0ZpeGVkKDEpKyciIHgyPSInK3crJyIgeTI9IicrWSgwKS50b0ZpeGVkKDEpKyciIHN0cm9rZT0idmFyKC0tYm9yZGVyKSIgc3Ryb2tlLXdpZHRoPSIxIi8+PHBhdGggZD0iJytkKyciIGZpbGw9Im5vbmUiIHN0cm9rZT0iJytjb2wrJyIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWpvaW49InJvdW5kIiBzdHJva2UtbGluZWNhcD0icm91bmQiLz48L3N2Zz4nOwp9CmZ1bmN0aW9uIGJmKG0sYnRuKXtCRklMVD1tO0JTSE9XPTI1O2RvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoIiNiLWZpbHQgLmNoaXAiKS5mb3JFYWNoKGZ1bmN0aW9uKGIpe2IuY2xhc3NMaXN0LnJlbW92ZSgib24iKTt9KTtidG4uY2xhc3NMaXN0LmFkZCgib24iKTtyZW5kZXJSZWNlbnQoKTt9CmZ1bmN0aW9uIHJlbmRlclJlY2VudCgpewogIGlmKCFSQylyZXR1cm47CiAgdmFyIGxpc3Q9UkMucmVjZW50fHxbXTsKICBpZihCRklMVCE9PSJBTEwiKWxpc3Q9bGlzdC5maWx0ZXIoZnVuY3Rpb24ocCl7cmV0dXJuIHAubWt0PT09QkZJTFQ7fSk7CiAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLXJlY2VudCIpOwogIGlmKCFsaXN0Lmxlbmd0aCl7ZWwuaW5uZXJIVE1MPSc8ZGl2IGNsYXNzPSJlbXB0eSI+Tm90aGluZyBncmFkZWQnKyhCRklMVCE9PSJBTEwiPyIgZm9yICIrQkZJTFQ6IiIpKycgeWV0IOKAlCByZXN1bHRzIGxhbmQgfjJoIGFmdGVyIGZpbmFsLjwvZGl2Pic7cmV0dXJuO30KICB2YXIgaHRtbD1saXN0LnNsaWNlKDAsQlNIT1cpLm1hcChncmFkZWRSb3cpLmpvaW4oIiIpOwogIGlmKGxpc3QubGVuZ3RoPkJTSE9XKWh0bWwrPSc8YnV0dG9uIGNsYXNzPSJtb3JlIiBvbmNsaWNrPSJCU0hPVys9MjU7cmVuZGVyUmVjZW50KCkiPlNob3cgbW9yZSAoJysobGlzdC5sZW5ndGgtQlNIT1cpKycpPC9idXR0b24+JzsKICBlbC5pbm5lckhUTUw9aHRtbDsKfQpmdW5jdGlvbiBjbHZTdHIocCl7aWYoIXAuY2x2KXJldHVybiAiXHUyMDE0Ijt2YXIgdj1wLmNsdi5wdHMhPW51bGw/cC5jbHYucHRzOnAuY2x2LnBwO3JldHVybiAodj4wPyIrIjoiIikrdisocC5jbHYucHRzIT1udWxsPyIgcHRzIjoiIHBwIik7fQpmdW5jdGlvbiBwaWNrQ2FyZChwKXsKICByZXR1cm4gJzxkaXYgY2xhc3M9ImdjYXJkIj48ZGl2IGNsYXNzPSJnLXRvcCI+PGRpdiBjbGFzcz0iZy10ZWFtcyI+JytzaG9ydE5hbWUocC5hd2F5KSsnPHNwYW4gY2xhc3M9ImF0Ij5APC9zcGFuPicrc2hvcnROYW1lKHAuaG9tZSkrJzwvZGl2PjxkaXYgY2xhc3M9ImctbWV0YSI+PHNwYW4gY2xhc3M9InRhZyB0YWctdGltZSI+Jyt0aXBUaW1lKHAuY29tbWVuY2UpKyc8L3NwYW4+PHNwYW4gY2xhc3M9InRhZyB0YWctYmsiPicrcC5ib29rKyc8L3NwYW4+PC9kaXY+PC9kaXY+JysKICAnPGRpdiBjbGFzcz0iZy1wcm9qIj48c3Bhbj48Yj4nK3AubWt0KycgJytwLmxhYmVsKyc8L2I+PC9zcGFuPjxzcGFuPmVkZ2UgPGIgY2xhc3M9Im1vbm8iPicrKHAuZWRnZSoxMDApLnRvRml4ZWQoMSkrJyU8L2I+PC9zcGFuPjxzcGFuPnN0YWtlIDxiIGNsYXNzPSJtb25vIj4nK3Auc3Rha2VVKyd1PC9iPjwvc3Bhbj48c3Bhbj5tb2RlbCA8YiBjbGFzcz0ibW9ubyI+JysocC5wTW9kZWwqMTAwKS50b0ZpeGVkKDApKyclPC9iPjwvc3Bhbj48L2Rpdj48L2Rpdj4nOwp9CmZ1bmN0aW9uIGdyYWRlZFJvdyhwKXsKICB2YXIgY29sPXAuc3RhdHVzPT09IndvbiI/InZhcigtLWdyZWVuKSI6cC5zdGF0dXM9PT0ibG9zdCI/InZhcigtLXJlZFRleHQpIjoidmFyKC0tZGltKSI7CiAgdmFyIHU9cC5yZXN1bHQ/KChwLnJlc3VsdC51bml0cz4wPyIrIjoiIikrcC5yZXN1bHQudW5pdHMudG9GaXhlZCgyKSsidSIpOiIiOwogIHJldHVybiAnPGRpdiBjbGFzcz0ic3JvdyI+PGRpdj48ZGl2IGNsYXNzPSJ0Ij4nK3AubWt0KycgJytwLmxhYmVsKycgPHNwYW4gc3R5bGU9ImNvbG9yOicrY29sKyc7Zm9udC13ZWlnaHQ6ODAwIj4nK3Auc3RhdHVzLnRvVXBwZXJDYXNlKCkrJzwvc3Bhbj48L2Rpdj48ZGl2IGNsYXNzPSJzdCI+JytzaG9ydE5hbWUocC5hd2F5KSsnIEAgJytzaG9ydE5hbWUocC5ob21lKSsnIFx1MDBiNyBDTFYgJytjbHZTdHIocCkrJzwvZGl2PjwvZGl2PjxkaXYgY2xhc3M9InNjIiBzdHlsZT0iY29sb3I6Jytjb2wrJyI+Jyt1Kyc8L2Rpdj48L2Rpdj4nOwp9CmZ1bmN0aW9uIGxvYWRCZXRzKCl7CiAgdmFyIHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiZXRzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IEdyYWRpbmcgJiBsb2FkaW5nXHUyMDI2JzsKICBmZXRjaCgiL2FwaS90cmFjay9ncmFkZSIse21ldGhvZDoiUE9TVCJ9KS5jYXRjaChmdW5jdGlvbigpe3JldHVybiBudWxsO30pLnRoZW4oZnVuY3Rpb24oKXsKICAgIHJldHVybiBQcm9taXNlLmFsbChbZmV0Y2goIi9hcGkvcGlja3MiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KSxmZXRjaCgiL2FwaS90cmFjay9yZWNvcmQ/bj0xMDAiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KV0pOwogIH0pLnRoZW4oZnVuY3Rpb24ocmVzKXsKICAgIHN0LnN0eWxlLmRpc3BsYXk9Im5vbmUiOwogICAgdmFyIHBrPXJlc1swXSxyYz1yZXNbMV0sUj0ocmMucmVjb3JkJiZyYy5yZWNvcmQuQUxMKXx8e307CiAgICBpZihway5rZWxseSlkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1tYXh1IikudGV4dENvbnRlbnQ9cGsua2VsbHkubWF4VTsKICAgIHZhciBuZXRDb2w9Ui5uZXQ+MD8idmFyKC0tZ3JlZW4pIjooUi5uZXQ8MD8idmFyKC0tcmVkVGV4dCkiOiJ2YXIoLS10ZXh0KSIpOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImIta3BpcyIpLmlubmVySFRNTD0KICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPk5ldCB1bml0czwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyIgc3R5bGU9ImNvbG9yOicrbmV0Q29sKyciPicrKFIubmV0PjA/IisiOiIiKSsoUi5uZXQhPW51bGw/Ui5uZXQ6MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKFIuc3Rha2VkfHwwKSsndSBzdGFrZWQ8L2Rpdj48L2Rpdj4nKwogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+UmVjb3JkPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhSLnd8fDApKyctJysoUi5sfHwwKSsoUi5wPyctJytSLnA6JycpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhSLm9wZW58fDApKycgb3BlbicrKHJjLnBlbmRpbmdHcmFkZT8nIFx1MDBiNyAnK3JjLnBlbmRpbmdHcmFkZSsnIGF3YWl0aW5nIGdyYWRlJzonJykrJzwvZGl2PjwvZGl2PicrCiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5ST0k8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iPicrKFIucm9pIT1udWxsPyhSLnJvaSoxMDApLnRvRml4ZWQoMSkrJyUnOidcdTIwMTQnKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+Z3JhZGVkIHN0YWtlczwvZGl2PjwvZGl2PicrCiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5DTFYgYmVhdDwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyI+JysoUi5iZWF0IT1udWxsPyhSLmJlYXQqMTAwKS50b0ZpeGVkKDApKyclJzonXHUyMDE0JykrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKFIuY2x2Tnx8MCkrJyB3aXRoIENMVjwvZGl2PjwvZGl2Pic7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1vcGVuIikuaW5uZXJIVE1MPShway5vcGVuJiZway5vcGVuLmxlbmd0aCk/cGsub3Blbi5tYXAocGlja0NhcmQpLmpvaW4oIiIpOic8ZGl2IGNsYXNzPSJlbXB0eSI+PGI+Tm8gb3BlbiBwaWNrcy48L2I+PGJyPjxicj5QaWNrcyBhdXRvLWxvZyB3aGVuIGEgbW9kZWxlZCBtYXJrZXQgY2xlYXJzIGl0cyBmbG9vciAoTUwgJytUSC5NTCsnJSAvIFNQUiAnK1RILlNQUisnJSAvIFRPVCAnK1RILlRPVCsnJSkuPC9kaXY+JzsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLW1rdHMiKS5pbm5lckhUTUw9WyJNTCIsIlNQUiIsIlRPVCJdLm1hcChmdW5jdGlvbihtKXsKICAgICAgdmFyIHI9KHJjLnJlY29yZCYmcmMucmVjb3JkW21dKXx8e307CiAgICAgIHJldHVybiAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+JyttKyc8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iPicrKHIud3x8MCkrJy0nKyhyLmx8fDApKyhyLnA/Jy0nK3IucDonJykrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKChyLm5ldD4wPyIrIjoiIikrKHIubmV0IT1udWxsP3IubmV0OjApKSsndSBcdTAwYjcgQ0xWICcrKHIuYXZnQ2x2IT1udWxsPygoci5hdmdDbHY+MD8iKyI6IiIpK3IuYXZnQ2x2KyhtPT09Ik1MIj8iIHBwIjoiIHB0cyIpKToiXHUyMDE0IikrJzwvZGl2PjwvZGl2Pic7CiAgICB9KS5qb2luKCIiKTsKICAgIFJDPXJjO0JTSE9XPTI1O3JlbmRlclJlY2VudCgpOwogICAgdmFyIGN2PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLWN1cnZlIik7CiAgICBpZihyYy5kYWlseSYmcmMuZGFpbHkubGVuZ3RoPj0yKXtjdi5zdHlsZS5kaXNwbGF5PSJibG9jayI7Y3YuaW5uZXJIVE1MPSc8YiBzdHlsZT0iZm9udC1zaXplOjEycHgiPkN1bXVsYXRpdmUgdW5pdHM8L2I+PHNwYW4gc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLW11dGVkKSI+IFx1MDBiNyAnK3JjLmRhaWx5Lmxlbmd0aCsnIGRheXM8L3NwYW4+JytzcGFya1N2ZyhyYy5kYWlseSk7fQogICAgZWxzZSBjdi5zdHlsZS5kaXNwbGF5PSJub25lIjsKICB9KS5jYXRjaChmdW5jdGlvbihlKXtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tcmVkVGV4dCkiPlx1MjZhMCAnK2UubWVzc2FnZSsnPC9zcGFuPic7fSk7Cn0KdmFyIFJQTHJ1bm5pbmc9ZmFsc2UsUlBMc3RvcD1mYWxzZTsKZnVuY3Rpb24gcnBsWWVhcigpe3JldHVybiBwYXJzZUludChkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLXllYXIiKS52YWx1ZSl8fG5ldyBEYXRlKCkuZ2V0RnVsbFllYXIoKTt9CmZ1bmN0aW9uIHJwbEJ1ZGdldCgpe3JldHVybiBNYXRoLm1heCgxLHBhcnNlSW50KGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtYnVkZ2V0IikudmFsdWUpfHwyMDAwMCk7fQpmdW5jdGlvbiBycGxMb2cocyxhcHBlbmQpe3ZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLWxvZyIpO2VsLnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtpZihhcHBlbmQpZWwudGV4dENvbnRlbnQrPSJcbiIrcztlbHNlIGVsLnRleHRDb250ZW50PXM7ZWwuc2Nyb2xsVG9wPWVsLnNjcm9sbEhlaWdodDt9CmZ1bmN0aW9uIHJwbEJ1c3kob24pe1JQTHJ1bm5pbmc9b247WyJycGwtcGxhbiIsInJwbC1pbmdlc3QiLCJycGwtcmVzdWx0cyIsInJwbC1ydW4iLCJycGwtcmVwb3J0Il0uZm9yRWFjaChmdW5jdGlvbihpZCl7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoaWQpLmRpc2FibGVkPW9uO30pO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtc3RvcCIpLnN0eWxlLmRpc3BsYXk9b24/ImlubGluZS1mbGV4Ijoibm9uZSI7fQpmdW5jdGlvbiBycGxTdG9wRm4oKXtSUExzdG9wPXRydWU7cnBsTG9nKCJTdG9wcGluZyBhZnRlciBjdXJyZW50IHJlcXVlc3RcdTIwMjYiLHRydWUpO30KZnVuY3Rpb24gcnBsVG9nZ2xlQ3N2KCl7dmFyIHc9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC1jc3Z3cmFwIik7dy5zdHlsZS5kaXNwbGF5PXcuc3R5bGUuZGlzcGxheT09PSJub25lIj8iYmxvY2siOiJub25lIjt9CmZ1bmN0aW9uIHJwbFBsYW4oKXsKICB2YXIgeT1ycGxZZWFyKCksYnVkPXJwbEJ1ZGdldCgpO3JwbExvZygiUGxhbm5pbmcgIit5KyJcdTIwMjYiKTsKICBmZXRjaCgiL2FwaS9yZXBsYXkvcGxhbj95ZWFyPSIreSsiJmJ1ZGdldD0iK2J1ZCkudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSkudGhlbihmdW5jdGlvbihqKXsKICAgIGlmKCFqLm9rKXJldHVybiBycGxMb2coIlBsYW4gZXJyb3I6ICIrKGouZXJyb3J8fCI/IikpOwogICAgdmFyIGZpdHM9ai5maXRzPT09dHJ1ZT8iXHUyNzEzIGZpdHMiOihqLmZpdHM9PT1mYWxzZT8iXHUyNzE3IGV4Y2VlZHMgcXVvdGEiOiJxdW90YSB1bmtub3duIFx1MjAxNCBvcGVuIEdhbWVzIG9uY2UgdG8gcmVhZCBpdCIpOwogICAgcnBsTG9nKHkrIjogICIrai5mcm9tKyIgXHUyMTkyICIrai50bysiXG4iK2ouZGF5cysiIGRheXMgXHUwMGQ3ICIrai5zbmFwc1BlckRheSsiIHNuYXBzIFx1MDBkNyAiK2ouY29zdFBlckNhbGwrIi9jYWxsID0gIitqLmNyZWRpdHNOZWVkZWQrIiBjciAoZnVsbCBzZWFzb24pXG5xdW90YSAiKyhqLnF1b3RhUmVtYWluaW5nIT1udWxsP2oucXVvdGFSZW1haW5pbmc6Ij8iKSsiIChzYWZldHkgIitqLnNhZmV0eSsiKSAgXHUwMGI3ICAiK2ZpdHMrIlxuYnVkZ2V0ICIrYnVkKyIgY3IgXHUyMTkyIH4iKyhqLmRheXNBZmZvcmRhYmxlIT1udWxsP2ouZGF5c0FmZm9yZGFibGU6Ij8iKSsiIGRheXMgcGVyIHJ1biIpOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3JwbExvZygiUGxhbiBmYWlsZWQ6ICIrZS5tZXNzYWdlKTt9KTsKfQpmdW5jdGlvbiBycGxSZXN1bHRzKCl7CiAgdmFyIHk9cnBsWWVhcigpLGNzdj1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLWNzdiIpLnZhbHVlLnRyaW0oKTsKICBycGxMb2coY3N2PyJMb2FkaW5nIG1hbnVhbCBDU1ZcdTIwMjYiOiJGZXRjaGluZyBUb3J2aWsgcmVzdWx0c1x1MjAyNiIpOwogIGZldGNoKCIvYXBpL3JlcGxheS9yZXN1bHRzIix7bWV0aG9kOiJQT1NUIixoZWFkZXJzOnsiQ29udGVudC1UeXBlIjoiYXBwbGljYXRpb24vanNvbiJ9LGJvZHk6SlNPTi5zdHJpbmdpZnkoY3N2P3t5ZWFyOnksY3N2OmNzdn06e3llYXI6eX0pfSkudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSkudGhlbihmdW5jdGlvbihqKXsKICAgIGlmKCFqLm9rKXJldHVybiBycGxMb2coIlJlc3VsdHMgZXJyb3I6ICIrKGouZXJyb3J8fCI/IiksdHJ1ZSk7CiAgICBycGxMb2coIlx1MjcxMyBSZXN1bHRzIGxvYWRlZDogIitqLmdhbWVzKyIgZ2FtZXMgKCIrKGouZGV0fHxqLm1vZGUpKyIpIisoai5zYW1wbGU/IiBcdTIwMTQgZS5nLiAiK2ouc2FtcGxlLmhvbWUrIiAiK2ouc2FtcGxlLmhQdHMrIiwgIitqLnNhbXBsZS5hd2F5KyIgIitqLnNhbXBsZS5hUHRzOiIiKSx0cnVlKTtycGxTdGF0dXMoKTsKICB9KS5jYXRjaChmdW5jdGlvbihlKXtycGxMb2coIlJlc3VsdHMgZmFpbGVkOiAiK2UubWVzc2FnZSx0cnVlKTt9KTsKfQpmdW5jdGlvbiBycGxMb29wKGtpbmQpewogIGlmKFJQTHJ1bm5pbmcpcmV0dXJuOwogIHZhciB5PXJwbFllYXIoKTtSUExzdG9wPWZhbHNlO3JwbEJ1c3kodHJ1ZSk7CiAgdmFyIGVwPSIvYXBpL3JlcGxheS8iK2tpbmQsaXRlcj0wLHQwPURhdGUubm93KCkscHJldk5leHQ9bnVsbDsKICB2YXIgYnVkZ2V0PWtpbmQ9PT0iaW5nZXN0Ij9ycGxCdWRnZXQoKTowLHNlc3NTdGFydD1udWxsLHNlc3NTcGVudD0wOwogIHJwbExvZygoa2luZD09PSJpbmdlc3QiPyJJbmdlc3RpbmcgIjoiU2ltdWxhdGluZyAiKSt5KyhidWRnZXQ/KCIgXHUwMGI3IGJ1ZGdldCAiK2J1ZGdldCsiIGNyIik6IiIpKyJcdTIwMjYiKTsKICBmdW5jdGlvbiBzdGVwKCl7CiAgICBpZihSUExzdG9wKXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjVhMCBTdG9wcGVkIGFmdGVyICIraXRlcisiIGJhdGNoKGVzKSIrKGtpbmQ9PT0iaW5nZXN0Ij8oIiwgfiIrc2Vzc1NwZW50KyIgY3Igc3BlbnQiKToiIikrIi4iLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICBpdGVyKys7CiAgICB2YXIgYm9keT1raW5kPT09ImluZ2VzdCI/e3llYXI6eSxkYXlzOjE1LG1heENyZWRpdHM6TWF0aC5tYXgoMSxidWRnZXQtc2Vzc1NwZW50KX06e3llYXI6eSxkYXlzOjMwLHJlc3RhcnQ6aXRlcj09PTF9OwogICAgZmV0Y2goZXAse21ldGhvZDoiUE9TVCIsaGVhZGVyczp7IkNvbnRlbnQtVHlwZSI6ImFwcGxpY2F0aW9uL2pzb24ifSxib2R5OkpTT04uc3RyaW5naWZ5KGJvZHkpfSkudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSkudGhlbihmdW5jdGlvbihqKXsKICAgICAgaWYoIWoub2smJmoucHJvY2Vzc2VkRGF5cz09bnVsbCl7cnBsQnVzeShmYWxzZSk7cnBsTG9nKCJFcnJvcjogIisoai5lcnJvcnx8Ij8iKSx0cnVlKTtycGxTdGF0dXMoKTtyZXR1cm47fQogICAgICB2YXIgc2Vjcz1NYXRoLnJvdW5kKChEYXRlLm5vdygpLXQwKS8xMDAwKTsKICAgICAgaWYoa2luZD09PSJpbmdlc3QiJiZqLnF1b3RhKXsKICAgICAgICBpZihzZXNzU3RhcnQ9PW51bGwmJmoucXVvdGEucmVtYWluaW5nIT1udWxsKXNlc3NTdGFydD1qLnF1b3RhLnJlbWFpbmluZysoai5yZWFsU3BlbnQhPW51bGw/ai5yZWFsU3BlbnQ6KGouY3JlZGl0c1VzZWR8fDApKTsKICAgICAgICBzZXNzU3BlbnQ9KHNlc3NTdGFydCE9bnVsbCYmai5xdW90YS5yZW1haW5pbmchPW51bGwpPyhzZXNzU3RhcnQtai5xdW90YS5yZW1haW5pbmcpOihzZXNzU3BlbnQrKGouY3JlZGl0c1VzZWR8fDApKTsKICAgICAgfQogICAgICBpZighai5kb25lJiZwcmV2TmV4dCE9PW51bGwmJmoubmV4dERhdGU9PT1wcmV2TmV4dCl7cnBsQnVzeShmYWxzZSk7cnBsTG9nKCJcdTI2YTAgU3RvcHBlZDogbm8gZm9yd2FyZCBwcm9ncmVzcyBhdCAiK2oubmV4dERhdGUrIiAoY3Vyc29yIG5vdCBhZHZhbmNpbmcgXHUyMDE0IGNoZWNrIFJlZGlzKS4iLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICAgIHByZXZOZXh0PWoubmV4dERhdGU7CiAgICAgIGlmKGtpbmQ9PT0iaW5nZXN0Iil7CiAgICAgICAgcnBsTG9nKCJcdTAwYjcgIitqLm5leHREYXRlKyIgICAofiIrc2Vzc1NwZW50KyIgY3IgdGhpcyBydW4sICIrKGoudG90YWxDcmVkaXRzIT1udWxsP2oudG90YWxDcmVkaXRzKyIgdG90YWwiOiI/IikrIiwgYmF0Y2ggIitpdGVyKyIpIix0cnVlKTsKICAgICAgICBpZihqLmhhbHRlZCl7cnBsQnVzeShmYWxzZSk7cnBsTG9nKCJcdTI2YTAgSGFsdGVkOiAiK2ouaGFsdGVkLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICAgICAgaWYoai5kb25lKXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjcxMyBJbmdlc3QgY29tcGxldGUgdGhyb3VnaCAiK2oubmV4dERhdGUrIiAgXHUyMDE0ICAiK3NlY3MrInMsIH4iK3Nlc3NTcGVudCsiIGNyIix0cnVlKTtycGxTdGF0dXMoKTtyZXR1cm47fQogICAgICAgIGlmKHNlc3NTcGVudD49YnVkZ2V0KXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjVhMCBCdWRnZXQgcmVhY2hlZCAofiIrc2Vzc1NwZW50KyIvIitidWRnZXQrIiBjcikuIFRhcCBJbmdlc3QgYWdhaW4gdG8gcmVzdW1lIGZyb20gIitqLm5leHREYXRlKyIuIix0cnVlKTtycGxTdGF0dXMoKTtyZXR1cm47fQogICAgICB9ZWxzZXsKICAgICAgICBycGxMb2coIlx1MDBiNyAiK2oubmV4dERhdGUrIiAgICgiK2ouc2ltbWVkKyIgc2ltbWVkLCBiYXRjaCAiK2l0ZXIrIikiLHRydWUpOwogICAgICAgIGlmKGouZG9uZSl7cnBsQnVzeShmYWxzZSk7dmFyIHNtc2c9Ilx1MjcxMyBTaW0gY29tcGxldGUgdGhyb3VnaCAiK2oubmV4dERhdGUrIiAoIitqLnNpbW1lZCsiIGdhbWVzIisoai5yZXN1bHREYXRlU2hpZnQ/IiwgIitqLnJlc3VsdERhdGVTaGlmdCsiIGRhdGUtYWxpZ25lZCI6IiIpKyIpICBcdTIwMTQgICIrc2VjcysicyI7aWYoai5zaW1tZWQ9PT0wKXtzbXNnKz0iXG4gICBkaWFnOiAiKyhqLmxpbmVHYW1lc3x8MCkrIiBsaW5lLWdhbWVzIFx1MDBiNyAiKyhqLnJhdGluZ3NNaXNzaW5nRGF5c3x8MCkrIiBkYXlzIHcvbyByYXRpbmdzIFx1MDBiNyAiKyhqLnVubWF0Y2hlZFJhdGluZ3N8fDApKyIgb2Rkcy10ZWFtcyB1bm1hdGNoZWQgXHUwMGI3ICIrKGoudW5tYXRjaGVkUmVzdWx0c3x8MCkrIiByZXN1bHRzIHVubWF0Y2hlZCBcdTAwYjcgIisoai5yZXN1bHREYXRlU2hpZnR8fDApKyIgZGF0ZS1zaGlmdGVkIjtpZihqLnVubWF0Y2hlZFNhbXBsZSYmai51bm1hdGNoZWRTYW1wbGVbMF0pc21zZys9IlxuICAgZS5nLiB3YW50IFsiK2oudW5tYXRjaGVkU2FtcGxlWzBdLndhbnQrIl0gXHUyMDE0IHJlc3VsdHMgbmVhcmJ5OiBbIisoai51bm1hdGNoZWRTYW1wbGVbMF0uaGF2ZXx8W10pLmpvaW4oIl0gWyIpKyJdIjt9cnBsTG9nKHNtc2csdHJ1ZSk7cnBsU3RhdHVzKCk7cnBsUmVwb3J0KGZhbHNlKTtyZXR1cm47fQogICAgICB9CiAgICAgIHN0ZXAoKTsKICAgIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiUmVxdWVzdCBmYWlsZWQ6ICIrZS5tZXNzYWdlLHRydWUpO30pOwogIH0KICBzdGVwKCk7Cn0KZnVuY3Rpb24gcnBsU3RhdHVzKCl7CiAgdmFyIHk9cnBsWWVhcigpOwogIGZldGNoKCIvYXBpL3JlcGxheS9zdGF0dXM/eWVhcj0iK3kpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24ocnMpewogICAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtc3RhdHVzIik7CiAgICBpZihycyYmcnMuY3Vyc29yKXsKICAgICAgZWwuaW5uZXJIVE1MPSdJbmdlc3QgPHNwYW4gY2xhc3M9Im1vbm8iPicrKHJzLmN1cnNvci5pbmdlc3ROZXh0fHxycy5jdXJzb3IuZnJvbSkrJzwvc3Bhbj4nKyhycy5jdXJzb3IuZG9uZT8nIChkb25lKSc6JycpKyhycy5jdXJzb3IuY3JlZGl0cz8oJyBcdTAwYjcgJytycy5jdXJzb3IuY3JlZGl0cysnIGNyIHVzZWQnKTonJykrKHJzLnJlc3VsdHM/KCcgXHUwMGI3IHJlc3VsdHMgJytycy5yZXN1bHRzLmdhbWVzKycgKCcrcnMucmVzdWx0cy5tb2RlKycpJyk6JyBcdTAwYjcgPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWFtYmVyKSI+cmVzdWx0cyBub3QgbG9hZGVkPC9zcGFuPicpKycgXHUwMGI3IHNpbSAnKyhycy5jdXJzb3Iuc2ltTmV4dD8nPHNwYW4gY2xhc3M9Im1vbm8iPicrcnMuY3Vyc29yLnNpbU5leHQrJzwvc3Bhbj4nOidub3Qgc3RhcnRlZCcpOwogICAgfSBlbHNlIGVsLmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+Tm90IHN0YXJ0ZWQgXHUyMDE0IFBsYW4gdG8gc2l6ZSB0aGUgc3BlbmQsIHRoZW4gSW5nZXN0IFx1MjE5MiBSZXN1bHRzIFx1MjE5MiBSdW4uPC9zcGFuPic7CiAgfSkuY2F0Y2goZnVuY3Rpb24oKXt9KTsKfQpmdW5jdGlvbiBycGxSZXBvcnQodG9Mb2cpewogIHZhciB5PXJwbFllYXIoKTsKICBmZXRjaCgiL2FwaS9yZXBsYXkvcmVwb3J0P3llYXI9Iit5KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKHJwKXsKICAgIHZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLXJlcG9ydCIpOwogICAgaWYocnAmJnJwLm9rKXsKICAgICAgdmFyIEE9cnAucGlja3MuQUxMLHJlYz1ycC5yZWNvbW1lbmR8fHt9OwogICAgICBlbC5pbm5lckhUTUw9JzxkaXYgc3R5bGU9ImJvcmRlci10b3A6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7bWFyZ2luLXRvcDo3cHg7cGFkZGluZy10b3A6N3B4Ij4nK3JwLnllYXIrJyBcdTAwYjcgJytycC5jb3ZlcmFnZS5zaW1tZWQrJyBzaW1tZWQgXHUwMGI3IHBpY2tzIDxiPicrQS5yZWNvcmQrJzwvYj4gKCcrKEEudW5pdHM+MD8iKyI6IiIpK0EudW5pdHMrJ3UsIFJPSSAnKyhBLnJvaSE9bnVsbD8oQS5yb2kqMTAwKS50b0ZpeGVkKDEpKyclJzonXHUyMDE0JykrJykgXHUwMGI3IENMViBiZWF0ICcrKEEuY2x2QmVhdCE9bnVsbD8oQS5jbHZCZWF0KjEwMCkudG9GaXhlZCgwKSsnJSc6J1x1MjAxNCcpKwogICAgICAgICc8YnI+bWFyZ2luIFNEIDxiPicrKHJwLnJlc2lkdWFscy5tYXJnaW4/cnAucmVzaWR1YWxzLm1hcmdpbi5zZDonXHUyMDE0JykrJzwvYj4gXHUwMGI3IHRvdGFscyBiaWFzIDxiPicrKHJlYy50b3RhbHNCaWFzIT1udWxsPygocmVjLnRvdGFsc0JpYXM+MD8iKyI6IiIpK3JlYy50b3RhbHNCaWFzKTonXHUyMDE0JykrJzwvYj4gXHUwMGI3IEhDQSBpbXBsaWVkIDxiPicrKHJlYy5IQ0FfaW1wbGllZCE9bnVsbD9yZWMuSENBX2ltcGxpZWQ6J1x1MjAxNCcpKyc8L2I+JysKICAgICAgICAnPGJyPjxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPkZ1bGwgSlNPTjogPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvcmVwbGF5L3JlcG9ydD95ZWFyPScrcnAueWVhcisnPC9zcGFuPiBcdTAwYjcgcmVjb21tZW5kYXRpb25zIGRpc3BsYXktb25seTwvc3Bhbj48L2Rpdj4nOwogICAgICBpZih0b0xvZyl7CiAgICAgICAgdmFyIHN3PXJwLnN3ZWVwfHx7fTsKICAgICAgICBycGxMb2coIlJlcG9ydCAiK3JwLnllYXIrIjpcbiAgcGlja3MgIitBLnJlY29yZCsiICAiKyhBLnVuaXRzPjA/IisiOiIiKStBLnVuaXRzKyJ1ICBST0kgIisoQS5yb2khPW51bGw/KEEucm9pKjEwMCkudG9GaXhlZCgxKSsiJSI6Ilx1MjAxNCIpKyIgIENMViBiZWF0ICIrKEEuY2x2QmVhdCE9bnVsbD8oQS5jbHZCZWF0KjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKwogICAgICAgICAgIlxuICBieSBlZGdlOiAiK1siMi00IiwiNC02IiwiNi04IiwiOCsiXS5tYXAoZnVuY3Rpb24oayl7dmFyIHM9c3dba118fHt9O3JldHVybiBrKyIgIisocy5yb2khPW51bGw/KHMucm9pKjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKyIoIisocy5ufHwwKSsiKSI7fSkuam9pbigiICAiKSsKICAgICAgICAgICJcbiAgcmVzaWQgU0QgbWFyZ2luICIrKHJwLnJlc2lkdWFscy5tYXJnaW4/cnAucmVzaWR1YWxzLm1hcmdpbi5zZDoiXHUyMDE0IikrIiB0b3RhbCAiKyhycC5yZXNpZHVhbHMudG90YWw/cnAucmVzaWR1YWxzLnRvdGFsLnNkOiJcdTIwMTQiKSsiICBCcmllciAiKyhycC5jYWxpYnJhdGlvbj9ycC5jYWxpYnJhdGlvbi5icmllcjoiXHUyMDE0IikrCiAgICAgICAgICAiXG4gIHJlYzogU0QgIityZWMuU0QrIiAgVE9UX1NEICIrcmVjLlRPVF9TRCsiICB0b3RhbHNCaWFzICIrcmVjLnRvdGFsc0JpYXMrIiAgSENBICIrcmVjLkhDQV9pbXBsaWVkKTsKICAgICAgfQogICAgfSBlbHNlIHsgZWwuaW5uZXJIVE1MPScnOyBpZih0b0xvZylycGxMb2coIk5vIHJlcG9ydCB5ZXQgXHUyMDE0IGluZ2VzdCwgbG9hZCByZXN1bHRzLCB0aGVuIHJ1bi4iLHRydWUpOyB9CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7aWYodG9Mb2cpcnBsTG9nKCJSZXBvcnQgZmFpbGVkOiAiK2UubWVzc2FnZSx0cnVlKTt9KTsKfQpmdW5jdGlvbiBsb2FkQWxsKGZvcmNlKXtsb2FkU2xhdGUoZm9yY2UpO30KbG9hZEFsbCh0cnVlKTsKc2V0SW50ZXJ2YWwoZnVuY3Rpb24oKXtsb2FkU2xhdGUoZmFsc2UpO30sMTgwMDAwKTsKZnVuY3Rpb24gdHZUb2dnbGVJbXBvcnQoKXt2YXIgdz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0d3JhcCIpO2lmKHcpe3ZhciBvcGVuPXcuc3R5bGUuZGlzcGxheT09PSJub25lIjt3LnN0eWxlLmRpc3BsYXk9b3Blbj8iYmxvY2siOiJub25lIjtpZihvcGVuKXt0dlNlYXNvbkxpbmsoKTt0dlRtTGlua3MoKTt0dlRtQ292ZXJhZ2UoKTt9fX0KZnVuY3Rpb24gdHZTZWFzb25MaW5rKCl7dmFyIGE9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LWxpbmstc2Vhc29uIik7aWYoYSlhLmhyZWY9Imh0dHBzOi8vYmFydHRvcnZpay5jb20vIitycGxZZWFyKCkrIl90ZWFtX3Jlc3VsdHMuanNvbiI7fQpmdW5jdGlvbiB0dlRtTGlua3MoKXt2YXIgeT1ycGxZZWFyKCksd3JhcD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1saW5rcyIpO2lmKCF3cmFwKXJldHVybjt2YXIgb3V0PVtdLGQ9bmV3IERhdGUoRGF0ZS5VVEMoeS0xLDEwLDgpKSxlbmQ9bmV3IERhdGUoRGF0ZS5VVEMoeSwyLDIyKSk7d2hpbGUoZDw9ZW5kKXt2YXIgZHM9ZC50b0lTT1N0cmluZygpLnNsaWNlKDAsMTApLHltZD1kcy5yZXBsYWNlKC8tL2csIiIpO291dC5wdXNoKCc8YSBocmVmPSJodHRwczovL2JhcnR0b3J2aWsuY29tL3RpbWVtYWNoaW5lL3RlYW1fcmVzdWx0cy8nK3ltZCsnX3RlYW1fcmVzdWx0cy5qc29uLmd6IiB0YXJnZXQ9Il9ibGFuayIgcmVsPSJub29wZW5lciIgY2xhc3M9ImNoaXAiIHN0eWxlPSJ0ZXh0LWRlY29yYXRpb246bm9uZTtmb250LXNpemU6MTFweDtwYWRkaW5nOjRweCA4cHgiPicrZHMuc2xpY2UoNSkrJzwvYT4nKTtkPW5ldyBEYXRlKGQuZ2V0VGltZSgpKzE0Kjg2NGU1KTt9d3JhcC5pbm5lckhUTUw9b3V0LmpvaW4oIiIpO30KZnVuY3Rpb24gdHZVcGxvYWQoKXsKICB2YXIgaW5wPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1maWxlcyIpLGxvZz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0bG9nIiksYnRuPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di11cGJ0biIpOwogIHZhciBmaWxlcz1pbnAmJmlucC5maWxlcz9pbnAuZmlsZXM6W107CiAgaWYoIWZpbGVzLmxlbmd0aCl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iUGljayB0aGUgZG93bmxvYWRlZCAuZ3ogZmlsZXMgZmlyc3QuIjtyZXR1cm47fQogIGlmKGJ0bilidG4uZGlzYWJsZWQ9dHJ1ZTtpZihsb2cpbG9nLnRleHRDb250ZW50PSJSZWFkaW5nICIrZmlsZXMubGVuZ3RoKyIgZmlsZShzKVx1MjAyNiI7CiAgdmFyIGFycj1bXSxkb25lPTAsdG90YWw9ZmlsZXMubGVuZ3RoOwogIGZ1bmN0aW9uIGZpbigpe2RvbmUrKztpZihkb25lIT09dG90YWwpcmV0dXJuO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlVwbG9hZGluZyAiK2Fyci5sZW5ndGgrIiBmaWxlKHMpXHUyMDI2IjsKICAgIGZldGNoKCIvYXBpL2FkbWluL3RvcnZpay90bXVwbG9hZCIse21ldGhvZDoiUE9TVCIsaGVhZGVyczp7IkNvbnRlbnQtVHlwZSI6ImFwcGxpY2F0aW9uL2pzb24ifSxib2R5OkpTT04uc3RyaW5naWZ5KHt5ZWFyOnJwbFllYXIoKSxmaWxlczphcnJ9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICAgIGlmKGJ0bilidG4uZGlzYWJsZWQ9ZmFsc2U7CiAgICAgIGlmKGxvZyl7bG9nLnRleHRDb250ZW50PShqLm9rPyJcdTI3MTMgU3RvcmVkICIrai5zdG9yZWQrIiBzbmFwc2hvdChzKSI6Ilx1MjcxNyAwIHN0b3JlZCIpKyhqLmZhaWxlZD8iLCAiK2ouZmFpbGVkKyIgZmFpbGVkIjoiIikrIi4gQ292ZXJhZ2U6ICIrKGouY292ZXJhZ2U/ai5jb3ZlcmFnZS5jb3VudDowKSsiICgiKygoai5jb3ZlcmFnZSYmai5jb3ZlcmFnZS5mcm9tKXx8IiIpKyJcdTIwMTMiKygoai5jb3ZlcmFnZSYmai5jb3ZlcmFnZS50byl8fCIiKSsiKS4iO3ZhciB0cD1qLnN0b3JlZERldGFpbCYmai5zdG9yZWREZXRhaWxbMF0mJmouc3RvcmVkRGV0YWlsWzBdLnRvcDtpZih0cClsb2cudGV4dENvbnRlbnQrPSJcbnBhcnNlZCBlLmcuICIrdHAudGVhbSsiIFx1MjAxNCBPRSAiKygrdHAuYWRqb2UpLnRvRml4ZWQoMSkrIiAvIERFICIrKCt0cC5hZGpkZSkudG9GaXhlZCgxKSsiIC8gdGVtcG8gIisoK3RwLmFkanQpLnRvRml4ZWQoMSk7aWYoai5mYWlsZWQmJmouZmFpbGVkRGV0YWlsJiZqLmZhaWxlZERldGFpbFswXSlsb2cudGV4dENvbnRlbnQrPSJcbiIrai5mYWlsZWREZXRhaWxbMF0ubmFtZSsiOiAiK2ouZmFpbGVkRGV0YWlsWzBdLmVycm9yO30KICAgICAgdHZUbUNvdmVyYWdlKCk7CiAgICB9KS5jYXRjaChmdW5jdGlvbihlKXtpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9Ilx1MjcxNyAiK2UubWVzc2FnZTt9KTt9CiAgZm9yKHZhciBpPTA7aTxmaWxlcy5sZW5ndGg7aSsrKXsoZnVuY3Rpb24oZmlsZSl7dmFyIHJkPW5ldyBGaWxlUmVhZGVyKCk7cmQub25sb2FkPWZ1bmN0aW9uKCl7dmFyIHM9U3RyaW5nKHJkLnJlc3VsdCk7YXJyLnB1c2goe25hbWU6ZmlsZS5uYW1lLGI2NDpzLmluZGV4T2YoIiwiKT49MD9zLnNwbGl0KCIsIilbMV06c30pO2ZpbigpO307cmQub25lcnJvcj1mdW5jdGlvbigpe2ZpbigpO307cmQucmVhZEFzRGF0YVVSTChmaWxlKTt9KShmaWxlc1tpXSk7fQp9CmZ1bmN0aW9uIHR2VG1Db3ZlcmFnZSgpe3ZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1jb3YiKTtpZighZWwpcmV0dXJuO2ZldGNoKCIvYXBpL3JlcGxheS90bT95ZWFyPSIrcnBsWWVhcigpKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGope2VsLnRleHRDb250ZW50PShqLm9rJiZqLmNvdW50KT8oIlN0b3JlZDogIitqLmNvdW50KyIgc25hcHNob3RzLCAiKyhqLmZyb218fCIiKSsiXHUyMDEzIisoai50b3x8IiIpKyIuIik6Ik5vIGRhdGVkIHNuYXBzaG90cyB5ZXQuIjt9KS5jYXRjaChmdW5jdGlvbigpe30pO30KZnVuY3Rpb24gdHZJbXBvcnRUbSgpewogIHZhciB0YT1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0IiksbG9nPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1pbXBvcnRsb2ciKSxidG49ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LXRtYnRuIik7CiAgdmFyIGRhdGE9dGE/dGEudmFsdWUudHJpbSgpOiIiLGR0PShkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1kYXRlIil8fHt9KS52YWx1ZSx5PXJwbFllYXIoKTsKICBpZighZGF0YSl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iUGFzdGUgdGhlIHJhdGluZ3MgYWJvdmUgZmlyc3QuIjtyZXR1cm47fQogIGlmKCFkdCl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iRW50ZXIgdGhlIGRhdGUgdGhlc2UgcmF0aW5ncyByZWZsZWN0IChZWVlZLU1NLUREKS4iO3JldHVybjt9CiAgaWYoYnRuKWJ0bi5kaXNhYmxlZD10cnVlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlN0b3JpbmcgZGF0ZWQgc25hcHNob3RcdTIwMjYiOwogIGZldGNoKCIvYXBpL2FkbWluL3RvcnZpay90bSIse21ldGhvZDoiUE9TVCIsaGVhZGVyczp7IkNvbnRlbnQtVHlwZSI6ImFwcGxpY2F0aW9uL2pzb24ifSxib2R5OkpTT04uc3RyaW5naWZ5KHt5ZWFyOnksZGF0ZTpkdCxkYXRhOmRhdGF9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICBpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlOwogICAgaWYoai5vayl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzEzIFN0b3JlZCAiKyhqLnN0b3JlZERldGFpbFswXT9qLnN0b3JlZERldGFpbFswXS50ZWFtczoiPyIpKyIgdGVhbXMgYXQgIitkdCsiLiBDb3ZlcmFnZTogIitqLmNvdmVyYWdlLmNvdW50KyIgc25hcHNob3RzICgiKyhqLmNvdmVyYWdlLmZyb218fCIiKSsiXHUyMDEzIisoai5jb3ZlcmFnZS50b3x8IiIpKyIpLiI7dHZUbUNvdmVyYWdlKCk7fQogICAgZWxzZSBpZihsb2cpbG9nLnRleHRDb250ZW50PSJcdTI3MTcgIisoai5lcnJvcnx8KGouZmFpbGVkRGV0YWlsJiZqLmZhaWxlZERldGFpbFswXSYmai5mYWlsZWREZXRhaWxbMF0uZXJyb3IpfHwic3RvcmUgZmFpbGVkIik7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7aWYoYnRuKWJ0bi5kaXNhYmxlZD1mYWxzZTtpZihsb2cpbG9nLnRleHRDb250ZW50PSJcdTI3MTcgIitlLm1lc3NhZ2U7fSk7Cn0KZnVuY3Rpb24gdHZJbXBvcnQoKXsKICB2YXIgdGE9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LWltcG9ydCIpLGxvZz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0bG9nIiksYnRuPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1pbXBvcnRidG4iKTsKICB2YXIgZGF0YT10YT90YS52YWx1ZS50cmltKCk6IiIseT1ycGxZZWFyKCk7CiAgaWYoIWRhdGEpe2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlBhc3RlIHRoZSBDU1Ygb3IgSlNPTiBmaXJzdC4iO3JldHVybjt9CiAgaWYoYnRuKWJ0bi5kaXNhYmxlZD10cnVlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IkltcG9ydGluZ1x1MjAyNiI7CiAgZmV0Y2goIi9hcGkvYWRtaW4vdG9ydmlrIix7bWV0aG9kOiJQT1NUIixoZWFkZXJzOnsiQ29udGVudC1UeXBlIjoiYXBwbGljYXRpb24vanNvbiJ9LGJvZHk6SlNPTi5zdHJpbmdpZnkoe2RhdGE6ZGF0YSx5ZWFyOnl9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICBpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlOwogICAgaWYoai5vayl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzEzIExvYWRlZCAiK2oudGVhbXMrIiB0ZWFtcyAoIitqLm1vZGUrIiwgIitqLnllYXIrIikuIFRvcDogIisoai50b3AzfHxbXSkubWFwKGZ1bmN0aW9uKHQpe3JldHVybiB0LnRlYW07fSkuam9pbigiLCAiKTtsb2FkRGF0YSgpO30KICAgIGVsc2UgaWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzE3ICIrKGouZXJyb3J8fCJpbXBvcnQgZmFpbGVkIikrKGouc2FtcGxlPyJcbnNhbXBsZSByb3c6ICIrSlNPTi5zdHJpbmdpZnkoai5zYW1wbGVbMF0pOiIiKTsKICB9KS5jYXRjaChmdW5jdGlvbihlKXtpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9Ilx1MjcxNyAiK2UubWVzc2FnZTt9KTsKfQo8L3NjcmlwdD4KPC9ib2R5Pgo8L2h0bWw+Cg==", "base64").toString("utf8");
app.get("/", (q, r) => r.type("html").send(DASH));

// ═══ BOOT ═════════════════════════════════════════════════════════════════════
(async () => {
  try {
    const [al, nu, mc, lk, tk] = await Promise.all([rGet("hb:aliases"), rGet("hb:neutral"), rGet("hb:model"), rGet("hb:torvik:lock"), rGet("hb:tracker")]);
    const J = v => { try { return typeof v === "string" ? JSON.parse(v) : v; } catch (e) { return null; } };
    if (al) ALIASES = Object.assign({}, ALIAS_SEED, J(al) || {});
    if (nu) NEUTRAL = J(nu) || {};
    if (mc) { const c = J(mc); if (c && c.thresholds) CFG = Object.assign(CFG, c); }
    if (lk) TORVIK_LOCK = J(lk);
    if (tk) { const t = J(tk); if (t && Array.isArray(t.picks)) TRACKER = t; }
  } catch (e) {}
  fetchTorvik().catch(() => {});
  app.listen(PORT, "0.0.0.0", () => console.log("HOOPSBET v" + VERSION + " listening on " + PORT + " | season year " + seasonYear()));
})();
