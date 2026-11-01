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

const VERSION = "1.5.0";
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
  thresholds: { ML: 3.0, SPR: 3.0, TOT: 3.0, BOOKS: 3 }, // v1.5.0: floors on MARKET-ANCHORED edge (prob points vs retail price)
  blend: { model: 0.25 },                                  // v1.5.0: weight on Torvik; the rest on Pinnacle no-vig (consensus fallback). 1 = pure model. Fit it: replay report → blendFit
  mlBand: { min: -250, max: 250 },                         // v1.5.0: moneyline picks only inside this price band
  oneSidePerGame: true,                                    // v1.5.0: ML or spread per game, never both
  neutral: { auto: true, requireVerified: true },          // v1.5.0: ESPN neutral-site check; no auto-pick on unverified venues
  evTrack: { enabled: true, minEv: 2.0, strongOnly: false }, // v1.5.0: Pinnacle-EV plays logged to their own ledger
  alerts: { enabled: true, model: true, ev: "strong" },    // v1.5.0: push alerts (ntfy) — ev: "strong" | "all" | "off"
  kelly: { fraction: 0.25, maxU: 2.0, minU: 0.25 },       // quarter-Kelly; 1u = 1% of bankroll
  earlySeason: { enabled: false, startFrac: 0.25, rampDays: 40 },
  live: { enabled: true, baseMin: 30, preTipMin: 12, discoverMin: 180, gradeMin: 30 }, // v1.4.0 server-side scheduler (in season only) // OFF by default: opening-week stake x startFrac, ramping to x1 by rampDays into the season (fit vs replay before enabling)
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
function todayKey() { return new Date().toLocaleDateString("en-CA", { timeZone: "America/New_York" }).replace(/-/g, ""); } // v1.4.0: ET day (was UTC: picks after 8pm ET landed on tomorrow)
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
  const oldest = duePicks().reduce((m, p) => Math.min(m, Date.parse(p.commence) || Infinity), Infinity);
  const daysFrom = (isFinite(oldest) && Date.now() - oldest > 20 * 3600e3) ? 3 : 1; // v1.4.0: catch up after downtime
  const r = await fetch(ODDS_HOST + "/v4/sports/" + SPORT + "/scores?daysFrom=" + daysFrom + "&apiKey=" + ODDS_KEY);
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

// ═══ v1.5.0 SHARPEN ═══════════════════════════════════════════════════════════════════
// (1) Neutral sites, detected from ESPN's public scoreboard (competitions[0].neutralSite) instead of
//     by hand. A missed neutral flag hands the listed "home" team 3 points of HCA ≈ 11% win prob.
//     Games whose venue can't be verified (feed down, no match, home/away reversed) are still
//     modeled but never auto-picked while CFG.neutral.requireVerified is on.
const ESPN_SB = "https://site.api.espn.com/apis/site/v2/sports/basketball/mens-college-basketball/scoreboard";
let VENUES = {};          // "YYYYMMDD" (ET) -> { t, ok, events:[{home:[names], away:[names], neutral, venue}], err }
let VENUE_ERR = null;
function venueNames(t) {
  if (!t) return [];
  return [t.displayName, t.shortDisplayName, t.location, ((t.location || "") + " " + (t.name || "")).trim()].filter(Boolean).map(normName);
}
async function fetchVenueDay(ymd) {
  const c = VENUES[ymd];
  if (c && Date.now() - c.t < (c.ok ? 30 : 10) * 60e3) return c;
  try {
    const r = await fetch(ESPN_SB + "?dates=" + ymd + "&groups=50&limit=500", { headers: { "User-Agent": "Mozilla/5.0 HOOPSBET" } });
    if (!r.ok) throw new Error("ESPN HTTP " + r.status);
    const j = await r.json();
    const events = (j.events || []).map(ev => {
      const c0 = (ev.competitions || [])[0] || {}, cs = c0.competitors || [];
      const h = cs.find(x => x.homeAway === "home"), a = cs.find(x => x.homeAway === "away");
      if (!h || !a) return null;
      return { home: venueNames(h.team), away: venueNames(a.team), neutral: !!c0.neutralSite, venue: (c0.venue && c0.venue.fullName) || null };
    }).filter(Boolean);
    VENUES[ymd] = { t: Date.now(), ok: true, events: events };
    VENUE_ERR = null;
  } catch (e) {
    VENUES[ymd] = { t: Date.now(), ok: false, events: [], err: e.message };
    VENUE_ERR = { msg: e.message, at: Date.now() };
  }
  const keep = new Date(Date.now() - 4 * 86400e3).toLocaleDateString("en-CA", { timeZone: "America/New_York" }).replace(/-/g, "");
  Object.keys(VENUES).forEach(k => { if (k < keep) delete VENUES[k]; });
  return VENUES[ymd];
}
async function refreshVenues(games) {
  if (!(CFG.neutral && CFG.neutral.auto)) return;
  const days = new Set();
  (games || []).forEach(g => { const d = etYmd(g.commence); if (d) days.add(d.replace(/-/g, "")); });
  for (const d of days) await fetchVenueDay(d);
}
// Name similarity: exact 1; candidate fully contained (e.g. ESPN location "UNC Wilmington") 0.8; else token Jaccard.
function venueNameSim(oddsName, cands) {
  const n = normName(oddsName), A = new Set(n.split(" "));
  let best = 0;
  (cands || []).forEach(c => {
    if (!c) return;
    if (c === n) { best = 1; return; }
    const B = c.split(" ");
    if (B.length && B.every(t => A.has(t))) best = Math.max(best, 0.8);
    let inter = 0; B.forEach(t => { if (A.has(t)) inter++; });
    best = Math.max(best, inter / (A.size + B.length - inter));
  });
  return best;
}
function venueFor(g) {
  const man = NEUTRAL[g.id];
  if (man === 1 || man === true) return { status: "neutral", neutral: true, src: "manual" };
  if (man === 0 || man === false) return { status: "home", neutral: false, src: "manual" };
  if (!(CFG.neutral && CFG.neutral.auto)) return { status: "home", neutral: false, src: "assumed" };
  const d = etYmd(g.commence), day = d ? VENUES[d.replace(/-/g, "")] : null;
  if (!day) return { status: "unchecked", neutral: false };
  if (!day.ok) return { status: "unavailable", neutral: false, err: day.err };
  let best = null;
  day.events.forEach(ev => {
    const s1 = Math.min(venueNameSim(g.home, ev.home), venueNameSim(g.away, ev.away));
    const s2 = Math.min(venueNameSim(g.home, ev.away), venueNameSim(g.away, ev.home));
    const s = Math.max(s1, s2);
    if (!best || s > best.s) best = { s: s, flip: s2 > s1, ev: ev };
  });
  if (!best || best.s < 0.5) return { status: "unmatched", neutral: false };
  if (best.ev.neutral) return { status: "neutral", neutral: true, src: "espn", venue: best.ev.venue };
  if (best.flip) return { status: "flip", neutral: false, src: "espn", venue: best.ev.venue };
  return { status: "home", neutral: false, src: "espn", venue: best.ev.venue };
}

// (2) Market shrinkage. The model's view is blended toward Pinnacle's no-vig line (consensus when
//     Pinnacle is missing) before any price is judged:  blended = w·model + (1−w)·market.
//     Edges are then the blended probability minus the RETAIL price you'd actually pay.
//     w = 1 reproduces the pre-v1.5 pure-model behaviour exactly.
function marketAnchor(g) {
  const s = g.sharp || {}, b = g.book || {};
  const pick = (a, c) => a != null ? { v: a, src: "pinnacle" } : (c != null ? { v: c, src: "consensus" } : { v: null, src: null });
  const spr = pick(s.sprH, b.sprH), ml = pick(s.pHome, b.pHome), tot = pick(s.tot, b.tot);
  return { margin: spr.v != null ? -spr.v : null, sprSrc: spr.src, pHome: ml.v, mlSrc: ml.src, total: tot.v, totSrc: tot.src };
}
function blendProj(proj, g) {
  const w = (CFG.blend && CFG.blend.model != null) ? CFG.blend.model : 1;
  const m = marketAnchor(g);
  const margin = m.margin != null ? w * proj.margin + (1 - w) * m.margin : (w >= 1 ? proj.margin : null);
  const pHome = m.pHome != null ? w * proj.pHomeML + (1 - w) * m.pHome
    : (w >= 1 ? proj.pHomeML : (margin != null ? normCdf(margin / CFG.SD) : null));
  const total = m.total != null ? w * proj.total + (1 - w) * m.total : (w >= 1 ? proj.total : null);
  return { w: w, margin: margin, pHome: pHome, total: total, src: { spr: m.sprSrc, ml: m.mlSrc, tot: m.totSrc } };
}
// One side bet per game: of ML and spread, keep the one with the higher EV% at its price.
function evPctOf(e) { const o = e.odds != null ? e.odds : e.juice; return e.pModel * decOdds(o) - 1; }
function chooseSideMarket(edges) {
  const c = ["ML", "SPR"].filter(m => edges && edges[m] && edges[m].ok && edges[m].hot);
  if (!c.length) return null;
  return c.sort((a, b) => evPctOf(edges[b]) - evPctOf(edges[a]))[0];
}

// (3) Push alerts via ntfy (free; install the ntfy iOS app and subscribe to your topic).
//     Env: NTFY_TOPIC (required to send), NTFY_SERVER (default https://ntfy.sh), NTFY_TOKEN (optional).
const NTFY_TOPIC = process.env.NTFY_TOPIC || "";
const NTFY_SERVER = (process.env.NTFY_SERVER || "https://ntfy.sh").replace(/\/+$/, "");
const NTFY_TOKEN = process.env.NTFY_TOKEN || "";
const PUBLIC_URL = process.env.PUBLIC_URL || process.env.RENDER_EXTERNAL_URL || "";
let NEW_PICKS = [];
let ALERTS = { sent: 0, lastAt: 0, lastErr: null };
function tipET(iso) { const t = Date.parse(iso); return isNaN(t) ? "" : new Date(t).toLocaleTimeString("en-US", { timeZone: "America/New_York", hour: "numeric", minute: "2-digit" }); }
function shortTeam(n) {
  try { const r = TORVIK ? resolveTeam(n) : null; if (r && r.team) return r.team; } catch (e) {} // Torvik short name ("Duke", "Notre Dame")
  const w = String(n || "").split(" "); return w.length > 2 ? w.slice(0, -1).join(" ") : (w[0] || "");
}
function alertLine(p) {
  const ev = p.evPct != null ? p.evPct : +((p.pModel * decOdds(p.odds) - 1) * 100).toFixed(1);
  const odds = p.odds > 0 ? "+" + p.odds : String(p.odds);
  const what = p.mkt === "TOT" ? (p.side === "over" ? "Over " : "Under ") + p.line
    : (p.side === "home" ? shortTeam(p.home) : shortTeam(p.away)) + (p.mkt === "ML" ? " ML" : " " + (p.line > 0 ? "+" + p.line : p.line));
  return (p.src === "ev" ? "[EV] " : "") + what + " " + odds + " " + p.book + " · " + shortTeam(p.away) + " @ " + shortTeam(p.home) +
    " " + tipET(p.commence) + " · EV " + (ev > 0 ? "+" : "") + ev + "% · " + p.stakeU + "u";
}
async function notify(title, message, opts) {
  if (!NTFY_TOPIC) return { ok: false, error: "NTFY_TOPIC not set" };
  try {
    const body = { topic: NTFY_TOPIC, title: title, message: message, tags: (opts && opts.tags) || ["basketball"], priority: (opts && opts.priority) || 3 };
    if (PUBLIC_URL) body.click = PUBLIC_URL;
    const headers = { "Content-Type": "application/json" };
    if (NTFY_TOKEN) headers.Authorization = "Bearer " + NTFY_TOKEN;
    const r = await fetch(NTFY_SERVER, { method: "POST", headers: headers, body: JSON.stringify(body) });
    if (!r.ok) throw new Error("ntfy HTTP " + r.status);
    ALERTS.sent++; ALERTS.lastAt = Date.now(); ALERTS.lastErr = null;
    return { ok: true };
  } catch (e) { ALERTS.lastErr = { msg: e.message, at: Date.now() }; return { ok: false, error: e.message }; }
}
async function flushPickAlerts() {
  if (!NEW_PICKS.length) return { sent: 0 };
  const picks = NEW_PICKS.splice(0);
  const A = CFG.alerts || {};
  if (!A.enabled) return { sent: 0 };
  const send = picks.filter(p => (p.src || "model") === "model" ? A.model !== false : (A.ev === "all" || (A.ev === "strong" && p.strong)))
    .sort((a, b) => Date.parse(a.commence) - Date.parse(b.commence));
  if (!send.length) return { sent: 0 };
  const title = send.length === 1 ? "HOOPSBET pick" : "HOOPSBET: " + send.length + " new picks";
  const message = send.slice(0, 12).map(alertLine).join("\n") + (send.length > 12 ? "\n+" + (send.length - 12) + " more on the Bets tab" : "");
  const r = await notify(title, message, { priority: send.some(p => (p.src || "model") === "model") ? 4 : 3 });
  return { sent: r.ok ? send.length : 0, error: r.error };
}

// (4) EV ledger: the Pinnacle-anchored screen's plays are now tracked as picks (src "ev"), with
//     their own CLV and record, separate from the model's.
function evLabel(r) {
  const tm = (r.side === "home" ? lastWord(r.home) : lastWord(r.away)).slice(0, 3).toUpperCase();
  if (r.mkt === "ML") return tm + " " + (r.odds > 0 ? "+" + r.odds : r.odds);
  if (r.mkt === "SPR") return tm + " " + (r.line > 0 ? "+" + r.line : r.line);
  return (r.side === "over" ? "O" : "U") + " " + r.line;
}
function harvestEvPicks(games, asm) {
  const T = CFG.evTrack;
  if (!T || !T.enabled) return 0;
  const now = Date.now(), byId = {};
  (games || []).forEach(g => { byId[g.id] = g; });
  const pickable = {};
  ((asm && asm.games) || []).forEach(o => { pickable[o.id] = o.pickable !== false; });
  const ev = computeEv(games, asm);
  let made = 0;
  ev.rows.forEach(r => {
    if (Date.parse(r.commence) <= now) return;
    if (r.evPct < (T.minEv != null ? T.minEv : CFG.ev.min)) return;
    if (T.strongOnly && !r.strong) return;
    const pid = "EV|" + r.gameId + "|" + r.mkt;
    if (TRACKER.picks.some(p => p.pid === pid)) return;
    const g = byId[r.gameId]; if (!g) return;
    const stakeU = kellyStake(r.pFair, r.odds, todayKey(), seasonYear());
    if (!stakeU) return;
    const pick = { pid: pid, src: "ev", gameId: r.gameId, mkt: r.mkt, side: r.side, line: r.line != null ? r.line : null,
      odds: r.odds, book: r.book, edge: +(r.pFair - impProb(r.odds)).toFixed(4), pModel: r.pFair, evPct: r.evPct, strong: r.strong, gap: r.gap,
      label: evLabel(r), stakeU: stakeU, away: r.away, home: r.home, commence: r.commence, date: todayKey(), at: now, mv: VERSION,
      snap: snapOf(g), close: null, status: "open", result: null, clv: null, venueOk: pickable[r.gameId] !== false };
    TRACKER.picks.push(pick); NEW_PICKS.push(pick); made++;
  });
  if (made) { trackerDirty = true; saveTracker(); }
  return made;
}

function computeEdges(g, proj) {
  const TH = CFG.thresholds;
  const out = { ML: null, SPR: null, TOT: null };
  const gate = (n, min) => n >= min ? null : n + " bk";
  const B = blendProj(proj, g); // v1.5.0 market shrinkage
  out.blend = { w: B.w, margin: B.margin != null ? +B.margin.toFixed(2) : null, total: B.total != null ? +B.total.toFixed(2) : null,
    pHome: B.pHome != null ? +B.pHome.toFixed(4) : null, src: B.src };
  const band = CFG.mlBand || { min: -100000, max: 100000 };

  // ML — best retail price each side vs model prob
  {
    const reason = gate(g.nML, TH.BOOKS) || (B.pHome == null ? "no anchor" : null);
    if (reason) out.ML = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.mlA == null || b.mlH == null) return;
        [["home", b.mlH, B.pHome], ["away", b.mlA, 1 - B.pHome]].forEach(([side, ml, pm]) => {
          const e = pm - impProb(ml), inB = ml >= band.min && ml <= band.max;
          if (!best || (inB && !best.inB) || (inB === best.inB && e > best.edge)) best = { side, edge: e, odds: ml, book: k, pModel: pm, inB };
        });
      });
      out.ML = best ? { ok: true, side: best.side, edge: best.edge, odds: best.odds, book: best.book, pModel: best.pModel,
        label: (best.side === "home" ? lastWord(g.home) : lastWord(g.away)).slice(0, 3).toUpperCase() + " " + (best.odds > 0 ? "+" + best.odds : best.odds),
        outOfBand: !best.inB, hot: best.inB && best.edge * 100 >= TH.ML } : { ok: false, reason: "no prices" };
    }
  }
  // SPR — per-book line; P(home covers)=Φ((margin+sprH)/SD)
  {
    const reason = gate(g.nSPR, TH.BOOKS) || (B.margin == null ? "no anchor" : null);
    if (reason) out.SPR = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.sprH == null || b.sprHJ == null || b.sprAJ == null) return;
        const pH = normCdf((B.margin + b.sprH) / CFG.SD);
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
    const reason = gate(g.nTOT, TH.BOOKS) || (B.total == null ? "no anchor" : null);
    if (reason) out.TOT = { ok: false, reason };
    else {
      let best = null;
      RETAIL.forEach(k => {
        const b = g.books[k]; if (!b || b.tot == null || b.overJ == null || b.underJ == null) return;
        const pO = normCdf((B.total - b.tot) / CFG.TOT_SD);
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
    const o = { id: g.id, away: g.away, home: g.home, commence: g.commence, nBooks: g.nBooks, nML: g.nML, nSPR: g.nSPR, nTOT: g.nTOT, book: g.book, sharp: g.sharp, neutral: false };
    const V = venueFor(g); // v1.5.0
    o.neutral = V.neutral; o.venue = V.status; o.venueSrc = V.src || null; if (V.venue) o.venueName = V.venue;
    if (CFG.neutral && CFG.neutral.requireVerified && ["unavailable", "unmatched", "flip", "unchecked"].includes(V.status)) { o.pickable = false; o.pickBlock = "venue " + V.status; }
    if (g.nBooks > 0) lined++;
    const hR = resolveTeam(g.home), aR = resolveTeam(g.away);
    if (hR) { o.hRank = hR.rank; o.hConf = hR.conf; }
    if (aR) { o.aRank = aR.rank; o.aConf = aR.conf; }
    if (!TORVIK) { o.modeled = false; o.modelReason = "ratings not loaded"; return o; }
    if (TORVIK.year !== seasonYear()) { o.modeled = false; o.modelReason = "ratings are " + TORVIK.year + ", season is " + seasonYear(); return o; } // v1.4.0
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
  // v1.4.0: settled picks are archived (archiveSettled); this hard cap only bites if Redis archiving
  // keeps failing, and it never drops an open pick.
  if (TRACKER.picks.length > TRACKER_HARD_CAP) {
    const settled = TRACKER.picks.filter(p => p.status !== "open").sort((a, b) => settledAt(a) - settledAt(b));
    const drop = new Set(settled.slice(0, TRACKER.picks.length - TRACKER_HARD_CAP).map(p => p.pid));
    TRACKER.picks = TRACKER.picks.filter(p => !drop.has(p.pid));
  }
  rSet("hb:tracker", TRACKER); trackerDirty = false;
}
function decOdds(am) { return am > 0 ? 1 + am / 100 : 1 + 100 / (-am); }
// Early-season stake taper (OFF by default). Ratings are noisiest in the opening weeks, so when
// enabled this scales the final (clamped) stake down near the opener and ramps linearly back to
// full by rampDays into the season. Returns 1 when disabled or args are missing, so kellyStake is
// byte-identical to before for every existing path until the flag is flipped. Season opens
// (year-1)-11-04, matching the replay window.
function earlySeasonTaper(dateStr, year) {
  const c = CFG.earlySeason;
  if (!c || !c.enabled || !dateStr || !year) return 1;
  const d = normalizeDateStr(dateStr);
  if (!/^\d{4}-\d{2}-\d{2}$/.test(d)) return 1;
  const start = Date.parse((year - 1) + "-11-04T00:00:00Z"), cur = Date.parse(d + "T00:00:00Z");
  if (isNaN(start) || isNaN(cur)) return 1;
  const days = (cur - start) / 86400000;
  if (days >= c.rampDays) return 1;
  if (days <= 0) return c.startFrac;
  return c.startFrac + (1 - c.startFrac) * (days / c.rampDays);
}
function kellyStake(p, am, dateStr, year) {
  const b = decOdds(am) - 1, q = 1 - p;
  const f = (p * b - q) / b;
  if (f <= 0) return 0;
  const u = CFG.kelly.fraction * f * 100;
  const clamped = Math.min(CFG.kelly.maxU, Math.max(CFG.kelly.minU, Math.round(u * 100) / 100));
  return +(clamped * earlySeasonTaper(dateStr, year)).toFixed(2);
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
  const stakeU = kellyStake(e.pModel, odds, todayKey(), seasonYear());
  if (!stakeU) return null;
  const pick = { pid, gameId: g.id, mkt, side: e.side, line: e.line != null ? e.line : null,
    odds, book: e.book, edge: +e.edge.toFixed(4), pModel: +e.pModel.toFixed(4), label: e.label,
    stakeU, away: g.away, home: g.home, commence: g.commence, date: todayKey(), at: Date.now(), mv: VERSION, src: "model",
    evPct: +((e.pModel * decOdds(odds) - 1) * 100).toFixed(2), blendW: CFG.blend ? CFG.blend.model : 1, neutral: !!o.neutral, venue: o.venue || null,
    snap: snapOf(g), close: null, status: "open", result: null, clv: null };
  TRACKER.picks.push(pick); trackerDirty = true; NEW_PICKS.push(pick);
  return pick;
}
function harvestPicks(asm, games) {
  const now = Date.now(); let made = 0;
  const byId = {}; games.forEach(g => { byId[g.id] = g; });
  const one = CFG.oneSidePerGame !== false;
  asm.games.forEach(o => {
    if (!o.modeled) return;
    if (new Date(o.commence).getTime() <= now) return;
    if (o.pickable === false) return; // v1.5.0: unverified venue
    const sideMkt = one ? chooseSideMarket(o.edges) : null;
    const hasSide = one && TRACKER.picks.some(p => p.gameId === o.id && (p.src || "model") === "model" && (p.mkt === "ML" || p.mkt === "SPR") && p.status !== "void");
    ["ML", "SPR", "TOT"].forEach(mkt => {
      const e = o.edges[mkt];
      if (!(e && e.ok && e.hot)) return;
      if (one && mkt !== "TOT" && (mkt !== sideMkt || hasSide)) return;
      if (ensurePick(byId[o.id], o, mkt)) made++;
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

// ═══ v1.4.0 SEASONREADY — server-side scheduler · pick archive · season-split record ═════════
// Before v1.4.0 nothing ran unless the dashboard was open: picks were logged, closing lines frozen
// and bets graded only on a dash poll. The scheduler now does it on a 5-minute tick in season:
//   • odds pull every CFG.live.baseMin while a tip is within 12h, plus ONE pull inside the last
//     CFG.live.preTipMin before each tip cluster (fresh closing line), plus a discovery pull every
//     CFG.live.discoverMin otherwise. ~3 credits per pull.
//   • closes freeze every tick (free); grading at most every CFG.live.gradeMin (scores = 2 credits).
let CYCLE = { running: false, lastTick: 0, lastRun: 0, lastPull: 0, lastGrade: 0, pullDay: null, pullsToday: 0,
  runs: 0, errors: 0, lastError: null, lastReason: null, lastMade: 0, lastArchived: 0 };
function upcomingTips(games, now) {
  const set = {};
  (games || []).forEach(g => { const t = Date.parse(g && g.commence); if (!isNaN(t) && t > now) set[t] = 1; });
  return Object.keys(set).map(Number).sort((a, b) => a - b);
}
function pullDecision(now, lastPull, tips, L) {
  const pre = (L.preTipMin || 12) * 60e3;
  const soon = (tips || []).filter(t => t > now && t <= now + pre);
  if (soon.length && lastPull < soon[0] - pre) return "pre-tip";
  const since = now - (lastPull || 0);
  const busy = (tips || []).some(t => t > now && t <= now + 12 * 3600e3);
  if (busy && since >= (L.baseMin || 30) * 60e3) return "cadence";
  if (since >= (L.discoverMin || 180) * 60e3) return "discover";
  return null;
}
async function liveCycle(force) {
  const now = Date.now(); CYCLE.lastTick = now;
  if (CYCLE.running) return { skipped: "busy" };
  if (!force && !(CFG.live && CFG.live.enabled)) return { skipped: "disabled" };
  if (!ODDS_KEY) return { skipped: "ODDS_API_KEY not set" };
  if (!force && isOffseason()) return { skipped: "offseason" };
  const why = force ? "manual" : pullDecision(now, CYCLE.lastPull, upcomingTips(slateCache.d || [], now), CFG.live);
  const gradeDue = duePicks().length > 0 && (force || now - CYCLE.lastGrade >= (CFG.live.gradeMin || 30) * 60e3);
  CYCLE.running = true;
  try {
    freezeDueCloses();
    let made = 0, graded = null;
    if (why) {
      await fetchTorvik();
      const games = await getSlate(true);
      CYCLE.lastPull = Date.now();
      await refreshVenues(games); // v1.5.0
      const day = todayKey(); if (CYCLE.pullDay !== day) { CYCLE.pullDay = day; CYCLE.pullsToday = 0; } CYCLE.pullsToday++;
      const asm = assembleSlate(games);
      freezeDueCloses();
      made = harvestPicks(asm, games);
      CYCLE.lastEv = harvestEvPicks(games, asm); // v1.5.0
      await saveLastSeen();
      const al = await flushPickAlerts(); CYCLE.lastAlerted = al.sent || 0;
    }
    if (gradeDue) { graded = await gradeOpenPicks(); CYCLE.lastGrade = Date.now(); }
    const arch = await archiveSettled();
    CYCLE.runs++; CYCLE.lastRun = Date.now(); CYCLE.lastReason = why; CYCLE.lastMade = made; CYCLE.lastArchived = arch.moved || 0;
    return { pulled: !!why, reason: why, made, graded, archived: arch.moved || 0 };
  } catch (e) {
    CYCLE.errors++; CYCLE.lastError = { msg: e.message, at: Date.now() };
    return { error: e.message };
  } finally { CYCLE.running = false; }
}

// LASTSEEN (the pre-tip line that becomes the close) survives restarts.
async function saveLastSeen() {
  const cut = Date.now() - 3 * 86400e3, keep = {};
  Object.keys(LASTSEEN).forEach(id => { if ((LASTSEEN[id].ts || 0) >= cut) keep[id] = LASTSEEN[id]; });
  LASTSEEN = keep;
  await rSet("hb:lastseen", LASTSEEN);
}

// ── pick archive: settled picks move out of hb:tracker into compressed per-month keys ──
// hb:tracker was capped at 400 picks (≈8 days at the backtest's ~50 picks/day). Settled picks
// older than ARCHIVE_AFTER_DAYS now move to hb:arch:YYYYMM (gzip+base64), indexed in hb:arch:index.
const ARCH_PREFIX = "hb:arch:", ARCH_INDEX = "hb:arch:index", ARCHIVE_AFTER_DAYS = 3, TRACKER_HARD_CAP = 3000;
let ARCH_CACHE = {};
// Redis call that tells "missing" (ok, null) apart from "failed" (not ok) — archive merges must
// never overwrite a month after a failed read.
async function rCmdX(cmd) {
  if (!REDIS_URL || !REDIS_TOKEN) return { ok: false, result: null };
  try {
    const r = await fetch(REDIS_URL, { method: "POST", headers: { Authorization: "Bearer " + REDIS_TOKEN, "Content-Type": "application/json" }, body: JSON.stringify(cmd) });
    if (!r.ok) return { ok: false, result: null };
    const j = await r.json();
    return j && j.error ? { ok: false, result: null } : { ok: true, result: j ? j.result : null };
  } catch (e) { return { ok: false, result: null }; }
}
function archEncode(arr) { return "gz:" + zlib.gzipSync(Buffer.from(JSON.stringify(arr), "utf8")).toString("base64"); }
function archDecode(v) {
  if (v == null) return [];
  if (typeof v !== "string") return Array.isArray(v) ? v : [];
  if (v.slice(0, 3) === "gz:") return JSON.parse(zlib.gunzipSync(Buffer.from(v.slice(3), "base64")).toString("utf8"));
  return JSON.parse(v);
}
function etYmd(iso) { const t = Date.parse(iso); if (isNaN(t)) return null; return new Date(t).toLocaleDateString("en-CA", { timeZone: "America/New_York" }); }
function pickMonthKey(p) { const d = etYmd(p.commence) || etYmd(p.at ? new Date(p.at).toISOString() : null); return d ? d.slice(0, 4) + d.slice(5, 7) : "000000"; }
// App season label = the year the season ends (2027 = 2026-27), matching seasonYear().
function pickSeasonOf(p) { const mk = pickMonthKey(p); if (mk === "000000") return null; const y = +mk.slice(0, 4), m = +mk.slice(4, 6); return m >= 8 ? y + 1 : y; }
function seasonLabelHB(s) { return s === "all" ? "All seasons" : (s - 1) + "-" + String(s % 100).padStart(2, "0"); }
function parseSeasonQ(v) { const s = v == null ? "" : String(v).trim().toLowerCase(); if (s === "all") return "all"; if (s === "prev") return seasonYear() - 1; if (/^\d{4}$/.test(s)) return +s; return seasonYear(); }
function settledAt(p) { return (p.result && p.result.gradedAt) || Date.parse(p.commence) || p.at || 0; }

async function archLoadMonth(mk, fresh) {
  if (!fresh && ARCH_CACHE[mk] && Date.now() - ARCH_CACHE[mk].t < 10 * 60e3) return ARCH_CACHE[mk].picks;
  const r = await rCmdX(["GET", ARCH_PREFIX + mk]);
  if (!r.ok) return null;
  let picks; try { picks = archDecode(r.result); } catch (e) { return null; }
  ARCH_CACHE[mk] = { t: Date.now(), picks: picks };
  return picks;
}
async function archMonths() {
  const r = await rCmdX(["SMEMBERS", ARCH_INDEX]);
  return r.ok && Array.isArray(r.result) ? r.result.slice().sort() : [];
}
async function archiveSettled(nowMs) {
  if (!REDIS_URL || !REDIS_TOKEN) return { moved: 0, reason: "no redis" };
  const cut = (nowMs || Date.now()) - ARCHIVE_AFTER_DAYS * 86400e3;
  const done = TRACKER.picks.filter(p => p.status !== "open" && settledAt(p) < cut);
  if (!done.length) return { moved: 0 };
  const byMonth = {};
  done.forEach(p => { const mk = pickMonthKey(p); (byMonth[mk] = byMonth[mk] || []).push(p); });
  const movedPids = new Set();
  for (const mk of Object.keys(byMonth)) {
    const existing = await archLoadMonth(mk, true);
    if (existing === null) continue;                         // read failed → leave picks in tracker
    const have = new Set(existing.map(p => p.pid));
    const merged = existing.concat(byMonth[mk].filter(p => !have.has(p.pid)));
    const w = await rCmdX(["SET", ARCH_PREFIX + mk, archEncode(merged)]);
    if (!w.ok || w.result !== "OK") continue;
    await rCmdX(["SADD", ARCH_INDEX, mk]);
    ARCH_CACHE[mk] = { t: Date.now(), picks: merged };
    byMonth[mk].forEach(p => movedPids.add(p.pid));
  }
  if (movedPids.size) { TRACKER.picks = TRACKER.picks.filter(p => !movedPids.has(p.pid)); saveTracker(); }
  return { moved: movedPids.size };
}
// All picks for a season (archive + live tracker, de-duplicated by pid).
async function seasonPicks(season) {
  const months = await archMonths();
  const want = months.filter(mk => season === "all" || (function () { const y = +mk.slice(0, 4), m = +mk.slice(4, 6); return (m >= 8 ? y + 1 : y) === season; })());
  const seen = new Set(), out = [];
  for (const mk of want) {
    const arr = await archLoadMonth(mk, false);
    (arr || []).forEach(p => { if (!seen.has(p.pid)) { seen.add(p.pid); out.push(p); } });
  }
  TRACKER.picks.forEach(p => { if (!seen.has(p.pid) && (season === "all" || pickSeasonOf(p) === season)) { seen.add(p.pid); out.push(p); } });
  const seasons = {}; months.forEach(mk => { const y = +mk.slice(0, 4), m = +mk.slice(4, 6); seasons[m >= 8 ? y + 1 : y] = 1; });
  TRACKER.picks.forEach(p => { const s = pickSeasonOf(p); if (s) seasons[s] = 1; });
  seasons[seasonYear()] = 1;
  return { picks: out, seasons: Object.keys(seasons).map(Number).sort((a, b) => b - a), archivedMonths: want.length };
}

// Loud health: everything that would make the dashboard look quiet for the wrong reason.
function healthAlerts(now) {
  const t = now || Date.now(), out = [];
  const inSeason = !isOffseason(new Date(t));
  if (TORVIK && TORVIK.year !== seasonYear()) out.push({ sev: "err", msg: "Ratings are for the " + seasonLabelHB(TORVIK.year) + " season, not " + seasonLabelHB(seasonYear()) + " — picks paused. Import " + seasonYear() + " ratings on the Data tab." });
  else if (!TORVIK) out.push({ sev: inSeason ? "err" : "warn", msg: "Ratings not loaded" + (TORVIK_ERR ? " (" + TORVIK_ERR + ")" : "") });
  else if (t - TORVIK.fetchedAt > CFG.RATINGS_MAX_AGE_H * 3600e3) out.push({ sev: "warn", msg: "Ratings " + Math.round((t - TORVIK.fetchedAt) / 3600e3) + "h old — picks paused until refreshed" });
  if (inSeason && CFG.live && CFG.live.enabled) {
    if (!CYCLE.lastTick || t - CYCLE.lastTick > 15 * 60e3) out.push({ sev: "err", msg: "Scheduler not running (last tick " + (CYCLE.lastTick ? Math.round((t - CYCLE.lastTick) / 60e3) + "m ago" : "never") + ") — is the Render instance sleeping?" });
    else if (CYCLE.lastError && t - CYCLE.lastError.at < 60 * 60e3) out.push({ sev: "warn", msg: "Scheduler error: " + CYCLE.lastError.msg });
  }
  if (CFG.neutral && CFG.neutral.auto && VENUE_ERR && t - VENUE_ERR.at < 60 * 60e3) out.push({ sev: "warn", msg: "Neutral-site check failing (" + VENUE_ERR.msg + ") \u2014 picks paused on unverified games" });
  if (CFG.alerts && CFG.alerts.enabled && ALERTS.lastErr && t - ALERTS.lastErr.at < 6 * 3600e3) out.push({ sev: "warn", msg: "Push alert failed: " + ALERTS.lastErr.msg });
  return out;
}

function computeRecord(list) {
  const mk = () => ({ n: 0, w: 0, l: 0, p: 0, open: 0, voided: 0, staked: 0, net: 0, clvN: 0, clvSum: 0, beatN: 0 });
  const rec = { ML: mk(), SPR: mk(), TOT: mk(), ALL: mk() };
  (list || TRACKER.picks).forEach(pk => {
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
  return { year, startedAt: Date.now(), cfg: { HCA: CFG.HCA, SD: CFG.SD, TOT_SD: CFG.TOT_SD, thresholds: Object.assign({}, CFG.thresholds), kelly: Object.assign({}, CFG.kelly), earlySeason: Object.assign({}, CFG.earlySeason),
      blend: Object.assign({}, CFG.blend), mlBand: Object.assign({}, CFG.mlBand), oneSidePerGame: CFG.oneSidePerGame },
    days: 0, lineGames: 0, simmed: 0, unmatchedRatings: {}, unmatchedResults: 0, ratingsMissingDays: 0, resultDateShift: 0, unmatchedSample: [], noPreTip: 0, sameSnap: 0,
    picks: { ML: pk(), SPR: pk(), TOT: pk(), ALL: pk() },
    sweep: { "2-4": swb(), "4-6": swb(), "6-8": swb(), "8+": swb() },
    cal: { buckets: Array.from({ length: 10 }, () => ({ n: 0, w: 0, pSum: 0 })), brierSum: 0, brierN: 0 },
    resid: { margin: st(), home: st(), neutral: st(), total: st() },
    vsClose: { n: 0, absSum: 0, sideN: 0, sideHit: 0 },
    blendFit: { spr: { n: 0, xy: 0, xx: 0 }, tot: { n: 0, xy: 0, xx: 0 } } };
}
function mkReplayPick(rec, e, mkt, dateStr, year) {
  const odds = e.odds != null ? e.odds : e.juice;
  const stakeU = kellyStake(e.pModel, odds, dateStr, year);
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
    // v1.5.0 blend fit: regress the open→close line move on (model − open). The slope is the share of
    // Torvik's disagreement the market adopts by close = the CLV-optimal weight for CFG.blend.model.
    if (closeS.t !== openS.t) {
      const bf = agg.blendFit = agg.blendFit || { spr: { n: 0, xy: 0, xx: 0 }, tot: { n: 0, xy: 0, xx: 0 } };
      const lineOf = (gg, k) => gg.sharp && gg.sharp[k] != null ? gg.sharp[k] : (gg.book ? gg.book[k] : null);
      const oS = lineOf(gO, "sprH"), cS = lineOf(gC, "sprH"), oT = lineOf(gO, "tot"), cT = lineOf(gC, "tot");
      if (oS != null && cS != null) { const x = proj.margin - (-oS), y = (-cS) - (-oS); bf.spr.n++; bf.spr.xy += x * y; bf.spr.xx += x * x; }
      if (oT != null && cT != null) { const x = proj.total - oT, y = cT - oT; bf.tot.n++; bf.tot.xy += x * y; bf.tot.xx += x * x; }
    }
    const edges = computeEdges(gO, proj);
    const sideMkt = CFG.oneSidePerGame !== false ? chooseSideMarket(edges) : null; // v1.5.0
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
      if (CFG.oneSidePerGame !== false && mkt !== "TOT" && mkt !== sideMkt) return;
      const pick = mkReplayPick(rec, e, mkt, dateStr, agg.year);
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
    blendFit: (function () {
      const bf = agg.blendFit; if (!bf) return null;
      const w = b => b.n >= 50 && b.xx > 0 ? +(b.xy / b.xx).toFixed(3) : null;
      return { spread: { n: bf.spr.n, w: w(bf.spr) }, total: { n: bf.tot.n, w: w(bf.tot) }, current: CFG.blend ? CFG.blend.model : 1,
        note: "w = share of Torvik's disagreement with the open that the market adopts by close. Set blend.model near the spread w (a total w far below it means Torvik's totals add little)." };
    })(),
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
    torvik: TORVIK ? { year: TORVIK.year, season: seasonYear(), yearOk: TORVIK.year === seasonYear(), teams: TORVIK.teams, mode: TORVIK.mode, ageMin: Math.round((Date.now() - TORVIK.fetchedAt) / 60e3) } : { error: TORVIK_ERR || "not loaded", season: seasonYear() },
    live: { enabled: !!(CFG.live && CFG.live.enabled), lastTickMin: CYCLE.lastTick ? Math.round((Date.now() - CYCLE.lastTick) / 60e3) : null,
      lastPullMin: CYCLE.lastPull ? Math.round((Date.now() - CYCLE.lastPull) / 60e3) : null, pullsToday: CYCLE.pullsToday, lastReason: CYCLE.lastReason, errors: CYCLE.errors },
    alerts: healthAlerts(),
    push: { topicSet: !!NTFY_TOPIC, enabled: !!(CFG.alerts && CFG.alerts.enabled), sent: ALERTS.sent, lastAtMin: ALERTS.lastAt ? Math.round((Date.now() - ALERTS.lastAt) / 60e3) : null, lastErr: ALERTS.lastErr },
    venues: { auto: !!(CFG.neutral && CFG.neutral.auto), days: Object.keys(VENUES).length, lastErr: VENUE_ERR },
    model: { blendW: CFG.blend ? CFG.blend.model : 1, thresholds: CFG.thresholds, mlBand: CFG.mlBand, oneSidePerGame: CFG.oneSidePerGame },
    tracker: { picks: TRACKER.picks.length, open: TRACKER.picks.filter(p => p.status === "open").length },
    redis: rp.ok, redisInfo: rp.ok ? undefined : rp
  });
});

app.get("/api/slate", async (q, r) => {
  try {
    if (!ODDS_KEY) return r.json({ ok: true, games: [], coverage: { games: 0, lined: 0, modeled: 0 }, thresholds: CFG.thresholds, note: "ODDS_API_KEY not set \u2014 add it in the Render dashboard.", quota: QUOTA });
    await fetchTorvik();
    const games = await getSlate(q.query.force === "1");
    await refreshVenues(games); // v1.5.0
    const asm = assembleSlate(games);
    freezeDueCloses();
    harvestPicks(asm, games);
    harvestEvPicks(games, asm);
    flushPickAlerts().catch(() => {});
    const pickMap = {};
    TRACKER.picks.forEach(p => { if (p.status !== "void" && (p.src || "model") === "model") (pickMap[p.gameId] = pickMap[p.gameId] || []).push(p.mkt); });
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
  const { gameId, off, clear } = q.body || {};
  if (!gameId) return r.status(400).json({ ok: false, error: "need gameId" });
  if (clear) delete NEUTRAL[gameId]; else NEUTRAL[gameId] = off ? 0 : 1; // v1.5.0: 1 = force neutral, 0 = force home, clear = back to auto (ESPN)
  await rSet("hb:neutral", NEUTRAL);
  r.json({ ok: true, neutral: Object.keys(NEUTRAL) });
});

app.post("/api/admin/model", async (q, r) => {
  const b = q.body || {};
  ["HCA", "SD", "TOT_SD", "RATINGS_MAX_AGE_H"].forEach(k => { if (typeof b[k] === "number") CFG[k] = b[k]; });
  if (b.thresholds) Object.keys(CFG.thresholds).forEach(k => { if (typeof b.thresholds[k] === "number") CFG.thresholds[k] = b.thresholds[k]; });
  if (b.kelly) Object.keys(CFG.kelly).forEach(k => { if (typeof b.kelly[k] === "number") CFG.kelly[k] = b.kelly[k]; });
  if (b.blend && typeof b.blend.model === "number" && b.blend.model >= 0 && b.blend.model <= 1) CFG.blend.model = b.blend.model;
  if (b.mlBand) ["min", "max"].forEach(k => { if (typeof b.mlBand[k] === "number") CFG.mlBand[k] = b.mlBand[k]; });
  if (typeof b.oneSidePerGame === "boolean") CFG.oneSidePerGame = b.oneSidePerGame;
  if (b.neutral) ["auto", "requireVerified"].forEach(k => { if (typeof b.neutral[k] === "boolean") CFG.neutral[k] = b.neutral[k]; });
  if (b.evTrack) { ["enabled", "strongOnly"].forEach(k => { if (typeof b.evTrack[k] === "boolean") CFG.evTrack[k] = b.evTrack[k]; }); if (typeof b.evTrack.minEv === "number") CFG.evTrack.minEv = b.evTrack.minEv; }
  if (b.alerts) { ["enabled", "model"].forEach(k => { if (typeof b.alerts[k] === "boolean") CFG.alerts[k] = b.alerts[k]; }); if (["strong", "all", "off"].includes(b.alerts.ev)) CFG.alerts.ev = b.alerts.ev; }
  if (b.live) { if (typeof b.live.enabled === "boolean") CFG.live.enabled = b.live.enabled; ["baseMin", "preTipMin", "discoverMin", "gradeMin"].forEach(k => { if (typeof b.live[k] === "number" && b.live[k] > 0) CFG.live[k] = b.live[k]; }); }
  if (b.earlySeason) { if (typeof b.earlySeason.enabled === "boolean") CFG.earlySeason.enabled = b.earlySeason.enabled; ["startFrac", "rampDays"].forEach(k => { if (typeof b.earlySeason[k] === "number") CFG.earlySeason[k] = b.earlySeason[k]; }); }
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
    await refreshVenues(games); // v1.5.0
    const asm = assembleSlate(games);
    r.json(Object.assign({ ok: true, generatedAt: slateCache.t, cfg: CFG.ev, quota: QUOTA,
      note: (!games.length && isOffseason()) ? OFFSEASON_NOTE : undefined }, computeEv(games, asm)));
  } catch (e) { r.status(500).json({ ok: false, error: e.message }); }
});

app.get("/api/picks", (q, r) => {
  const open = TRACKER.picks.filter(p => p.status === "open").sort((a, b) => new Date(a.commence) - new Date(b.commence));
  r.json({ ok: true, open, kelly: CFG.kelly, thresholds: CFG.thresholds });
});

app.get("/api/track/record", async (q, r) => {
  // v1.4.0: season-split (default current season; ?season=prev|all|YYYY) over archive + live tracker
  const season = parseSeasonQ(q.query.season);
  const sp = await seasonPicks(season);
  const src = q.query.src === "ev" ? "ev" : "model"; // v1.5.0: model vs Pinnacle-EV ledger
  const list = sp.picks.filter(p => (p.src || "model") === src);
  const graded = list.filter(p => ["won", "lost", "push"].includes(p.status)).sort((a, b) => b.result.gradedAt - a.result.gradedAt);
  const n = Math.min(100, Math.max(1, parseInt(q.query.n) || 25));
  r.json({ ok: true, src: src, season: season, seasonLabel: seasonLabelHB(season), seasons: sp.seasons, totalPicks: list.length, archivedMonths: sp.archivedMonths,
    record: computeRecord(list), recent: graded.slice(0, n), daily: dailyPnl(list),
    pendingGrade: TRACKER.picks.filter(p => (p.src || "model") === src && p.status === "open" && new Date(p.commence).getTime() < Date.now()).length });
});

// v1.5.0 push-alert test (sends one notification to NTFY_TOPIC)
app.get("/api/notify/test", async (q, r) => {
  const res = await notify("HOOPSBET test", "Alerts are working. New picks will arrive here." + (PUBLIC_URL ? "\nTap to open the dashboard." : ""), { tags: ["white_check_mark"] });
  r.json(Object.assign({ topicSet: !!NTFY_TOPIC, server: NTFY_SERVER }, res));
});

// v1.4.0 scheduler status + manual run
app.get("/api/live/status", (q, r) => {
  const now = Date.now(), tips = upcomingTips(slateCache.d || [], now);
  r.json({ ok: true, config: CFG.live, seasonActive: !isOffseason(), cycle: Object.assign({}, CYCLE, {
      lastTickMin: CYCLE.lastTick ? Math.round((now - CYCLE.lastTick) / 60e3) : null,
      lastPullMin: CYCLE.lastPull ? Math.round((now - CYCLE.lastPull) / 60e3) : null }),
    nextTips: tips.slice(0, 8).map(t => new Date(t).toISOString()), wouldPullNow: pullDecision(now, CYCLE.lastPull, tips, CFG.live),
    tracker: { live: TRACKER.picks.length, open: TRACKER.picks.filter(p => p.status === "open").length } });
});
app.post("/api/live/run", async (q, r) => { r.json(Object.assign({ ok: true }, await liveCycle(true))); });

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

const DASH = Buffer.from("PCFET0NUWVBFIGh0bWw+CjxodG1sIGxhbmc9ImVuIj4KPGhlYWQ+CjxtZXRhIGNoYXJzZXQ9IlVURi04Ij4KPG1ldGEgbmFtZT0idmlld3BvcnQiIGNvbnRlbnQ9IndpZHRoPWRldmljZS13aWR0aCwgaW5pdGlhbC1zY2FsZT0xLjAsIG1heGltdW0tc2NhbGU9MS4wLCB1c2VyLXNjYWxhYmxlPW5vIj4KPHRpdGxlPkhPT1BTQkVUIOKAlCBOQ0FBIEJhc2tldGJhbGw8L3RpdGxlPgo8bGluayByZWw9ImFwcGxlLXRvdWNoLWljb24iIGhyZWY9Ii9hcHBsZS10b3VjaC1pY29uLnBuZyI+CjxsaW5rIHJlbD0iaWNvbiIgdHlwZT0iaW1hZ2UvcG5nIiBzaXplcz0iMTkyeDE5MiIgaHJlZj0iL2ljb24tMTkyLnBuZyI+CjxsaW5rIHJlbD0ibWFuaWZlc3QiIGhyZWY9Ii9tYW5pZmVzdC53ZWJtYW5pZmVzdCI+CjxtZXRhIG5hbWU9ImFwcGxlLW1vYmlsZS13ZWItYXBwLWNhcGFibGUiIGNvbnRlbnQ9InllcyI+CjxtZXRhIG5hbWU9Im1vYmlsZS13ZWItYXBwLWNhcGFibGUiIGNvbnRlbnQ9InllcyI+CjxtZXRhIG5hbWU9ImFwcGxlLW1vYmlsZS13ZWItYXBwLXRpdGxlIiBjb250ZW50PSJIT09QU0JFVCI+CjxtZXRhIG5hbWU9ImFwcGxlLW1vYmlsZS13ZWItYXBwLXN0YXR1cy1iYXItc3R5bGUiIGNvbnRlbnQ9ImJsYWNrIj4KPG1ldGEgbmFtZT0idGhlbWUtY29sb3IiIGNvbnRlbnQ9IiMwYTE0MzAiPgo8bGluayBocmVmPSJodHRwczovL2ZvbnRzLmdvb2dsZWFwaXMuY29tL2NzczI/ZmFtaWx5PU91dGZpdDp3Z2h0QDMwMDs0MDA7NTAwOzYwMDs3MDA7ODAwOzkwMCZmYW1pbHk9SmV0QnJhaW5zK01vbm86d2dodEA0MDA7NTAwOzYwMDs3MDA7ODAwJmRpc3BsYXk9c3dhcCIgcmVsPSJzdHlsZXNoZWV0Ij4KPHN0eWxlPgo6cm9vdHstLWJnOiMwYTE0MzA7LS1jYXJkOiMwZjIxNDc7LS1ib3JkZXI6IzIyNDI3ZjstLXRleHQ6I2Y1ZjhmZDstLWRpbTojYWViZmRhOy0tbXV0ZWQ6IzdhOTBiNTstLWFjY2VudDojMmY2ZmUwOy0tYWNjZW50VGV4dDojNmI5N2VlOy0tZ3JlZW46IzE4Yjg3YzstLXJlZDojZTEyZTQ0Oy0tcmVkVGV4dDojZjA1NTZiOy0tYW1iZXI6I2UwYTIzYTstLXB1cnBsZTojNmY5ZWZmOy0tY2FyZDI6IzBjMWEzYX0KKnttYXJnaW46MDtwYWRkaW5nOjA7Ym94LXNpemluZzpib3JkZXItYm94Oy13ZWJraXQtdGFwLWhpZ2hsaWdodC1jb2xvcjp0cmFuc3BhcmVudH0KaHRtbHstd2Via2l0LXRleHQtc2l6ZS1hZGp1c3Q6MTAwJX0KYm9keXtiYWNrZ3JvdW5kOnZhcigtLWJnKTtjb2xvcjp2YXIoLS10ZXh0KTtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3BhZGRpbmc6MTJweCAxNHB4IDEyMHB4O21heC13aWR0aDoxMTAwcHg7bWFyZ2luOjAgYXV0b30KLm1vbm97Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9CmJ1dHRvbjpmb2N1cy12aXNpYmxlLHNlbGVjdDpmb2N1cy12aXNpYmxlLGlucHV0OmZvY3VzLXZpc2libGUsYTpmb2N1cy12aXNpYmxle291dGxpbmU6MnB4IHNvbGlkIHZhcigtLWFjY2VudFRleHQpO291dGxpbmUtb2Zmc2V0OjJweH0KLmhkcntkaXNwbGF5OmZsZXg7YWxpZ24taXRlbXM6Y2VudGVyO2p1c3RpZnktY29udGVudDpzcGFjZS1iZXR3ZWVuO2dhcDo4cHg7bWFyZ2luLWJvdHRvbToxMnB4fQouYnJhbmR7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtnYXA6OXB4fQoubG9nb3t3aWR0aDozNHB4O2hlaWdodDozNHB4O2JvcmRlci1yYWRpdXM6OXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDEzNWRlZywjZTg1ZDJmLHZhcigtLWFjY2VudCkpO2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OmNlbnRlcjtmb250LXdlaWdodDo5MDA7Zm9udC1zaXplOjE2cHh9Ci5idHtmb250LXNpemU6MTVweDtmb250LXdlaWdodDo4MDB9LmJ0IHNwYW57Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ic3Vie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKX0KLmhkci1idG57cGFkZGluZzo4cHggMTRweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo4cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1hY2NlbnQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xKTtjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZn0KLmNhcmR7YmFja2dyb3VuZDpsaW5lYXItZ3JhZGllbnQoMTgwZGVnLHZhcigtLWNhcmQpLHZhcigtLWNhcmQyKSk7Ym9yZGVyOjFweCBzb2xpZCB0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjEwcHg7Ym94LXNoYWRvdzppbnNldCAwIDFweCAwIHJnYmEoMjU1LDI1NSwyNTUsLjA0KSwwIDRweCAxMnB4IHJnYmEoMCwwLDAsLjMyKTtwYWRkaW5nOjExcHggMTJweDttYXJnaW4tYm90dG9tOjhweH0KLnN0cmlwe2Rpc3BsYXk6ZmxleDtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwO21hcmdpbi1ib3R0b206MTBweH0KLmtwaXtmbGV4OjE7bWluLXdpZHRoOjEwNXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO3BhZGRpbmc6OXB4IDExcHh9Ci5rcGkgLmxie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKTt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bGV0dGVyLXNwYWNpbmc6LjRweDtmb250LXdlaWdodDo3MDB9Ci5rcGkgLnZ7Zm9udC1zaXplOjE3cHg7Zm9udC13ZWlnaHQ6ODAwO21hcmdpbi10b3A6MnB4fQoua3BpIC5ze2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDoxcHh9Ci5mYmFye2Rpc3BsYXk6ZmxleDtnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlcjttYXJnaW4tYm90dG9tOjEwcHh9Ci5jaGlwe3BhZGRpbmc6NnB4IDEzcHg7bWluLWhlaWdodDo0NHB4O2JvcmRlci1yYWRpdXM6OHB4O2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtiYWNrZ3JvdW5kOnRyYW5zcGFyZW50O2NvbG9yOnZhcigtLW11dGVkKTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZjtkaXNwbGF5OmlubGluZS1mbGV4O2FsaWduLWl0ZW1zOmNlbnRlcn0KLmNoaXAub257Ym9yZGVyLWNvbG9yOnZhcigtLWFjY2VudFRleHQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xMik7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9CnNlbGVjdC5jaGlwe2FwcGVhcmFuY2U6bm9uZTtwYWRkaW5nLXJpZ2h0OjI2cHg7YmFja2dyb3VuZC1pbWFnZTpsaW5lYXItZ3JhZGllbnQoNDVkZWcsdHJhbnNwYXJlbnQgNTAlLHZhcigtLW11dGVkKSA1MCUpLGxpbmVhci1ncmFkaWVudCgxMzVkZWcsdmFyKC0tbXV0ZWQpIDUwJSx0cmFuc3BhcmVudCA1MCUpO2JhY2tncm91bmQtcG9zaXRpb246Y2FsYygxMDAlIC0gMTRweCkgNTAlLGNhbGMoMTAwJSAtIDlweCkgNTAlO2JhY2tncm91bmQtc2l6ZTo1cHggNXB4O2JhY2tncm91bmQtcmVwZWF0Om5vLXJlcGVhdH0KLmdjYXJke2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO21hcmdpbi1ib3R0b206OHB4O3BhZGRpbmc6MTFweCAxMnB4fQouZy10b3B7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwfQouZy10ZWFtc3tmb250LXNpemU6MTNweDtmb250LXdlaWdodDo4MDA7bWluLXdpZHRoOjB9Ci5nLXRlYW1zIC5ya3tjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTBweDtmb250LXdlaWdodDo4MDA7bWFyZ2luLXJpZ2h0OjJweH0KLmctdGVhbXMgLmF0e2NvbG9yOnZhcigtLW11dGVkKTtmb250LXdlaWdodDo2MDA7bWFyZ2luOjAgNXB4fQouZy1tZXRhe2Rpc3BsYXk6ZmxleDtnYXA6NXB4O2FsaWduLWl0ZW1zOmNlbnRlcjtmbGV4LXdyYXA6d3JhcH0KLnRhZ3twYWRkaW5nOjJweCA3cHg7Ym9yZGVyLXJhZGl1czo1cHg7Zm9udC1zaXplOjEwcHg7Zm9udC13ZWlnaHQ6ODAwO2xldHRlci1zcGFjaW5nOi4zcHh9Ci50YWctdGltZXtiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA1KTtjb2xvcjp2YXIoLS1kaW0pO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKX0KLnRhZy1ue2JhY2tncm91bmQ6cmdiYSgxMTEsMTU4LDI1NSwuMTIpO2NvbG9yOnZhcigtLXB1cnBsZSk7Ym9yZGVyOjFweCBzb2xpZCByZ2JhKDExMSwxNTgsMjU1LC4zKX0KLnRhZy1ia3tiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA0KTtjb2xvcjp2YXIoLS1tdXRlZCk7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQouYXdhaXR7ZGlzcGxheTppbmxpbmUtYmxvY2s7cGFkZGluZzoycHggOHB4O2JvcmRlci1yYWRpdXM6NXB4O2JhY2tncm91bmQ6cmdiYSgyMjQsMTYyLDU4LC4xKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjI0LDE2Miw1OCwuMyk7Y29sb3I6dmFyKC0tYW1iZXIpO2ZvbnQtc2l6ZToxMHB4O2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvantkaXNwbGF5OmZsZXg7Z2FwOjE0cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKX0KLmctcHJvaiBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvaiAubW9ub3tmb250LXNpemU6MTJweH0KLmctZWRnZXN7ZGlzcGxheTpmbGV4O2dhcDo2cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo5cHh9Ci5lZHtwYWRkaW5nOjVweCAxMHB4O2JvcmRlci1yYWRpdXM6N3B4O2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjgwMDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtib3JkZXI6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7Y29sb3I6dmFyKC0tbXV0ZWQpO2JhY2tncm91bmQ6cmdiYSgyNTUsMjU1LDI1NSwuMDIpfQouZWQuaG90e2JvcmRlci1jb2xvcjpyZ2JhKDI0LDE4NCwxMjQsLjQ1KTtiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMSk7Y29sb3I6dmFyKC0tZ3JlZW4pfQouZWQgLnNke2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7Zm9udC13ZWlnaHQ6NzAwO2ZvbnQtc2l6ZToxMHB4O21hcmdpbi1yaWdodDo0cHg7Y29sb3I6aW5oZXJpdDtvcGFjaXR5Oi44NX0KLmctc2hhcnB7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQouZy1zaGFycCBie2NvbG9yOnZhcigtLXB1cnBsZSk7Zm9udC13ZWlnaHQ6NzAwfQouZW1wdHl7cGFkZGluZzoyNnB4IDE4cHg7Ym9yZGVyOjFweCBkYXNoZWQgdmFyKC0tYm9yZGVyKTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEycHg7bGluZS1oZWlnaHQ6MS42NTt0ZXh0LWFsaWduOmNlbnRlcjtjb2xvcjp2YXIoLS1tdXRlZCl9Ci5lbXB0eSBie2NvbG9yOnZhcigtLXRleHQpfQoubW9yZXt3aWR0aDoxMDAlO3BhZGRpbmc6MTFweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo5cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2JhY2tncm91bmQ6dHJhbnNwYXJlbnQ7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7bWFyZ2luOjJweCAwIDEwcHh9Ci5zZWMtaGR7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2NvbG9yOnZhcigtLWRpbSk7bGV0dGVyLXNwYWNpbmc6LjNweDt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bWFyZ2luOjE0cHggMCA4cHh9Ci5zcm93e2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OnNwYWNlLWJldHdlZW47Z2FwOjhweDtwYWRkaW5nOjlweCAxMXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6OXB4O2JveC1zaGFkb3c6aW5zZXQgMCAxcHggMCByZ2JhKDI1NSwyNTUsMjU1LC4wNCksMCAzcHggMTBweCByZ2JhKDAsMCwwLC4zKTttYXJnaW4tYm90dG9tOjZweH0KLnNyb3cgLnR7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwfQouc3JvdyAuc2N7Zm9udC1zaXplOjEzcHg7Zm9udC13ZWlnaHQ6ODAwO2ZvbnQtZmFtaWx5OidKZXRCcmFpbnMgTW9ubycsbW9ub3NwYWNlfQouc3JvdyAuc3R7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQoubGl2ZS1kb3R7Y29sb3I6dmFyKC0tZ3JlZW4pO2ZvbnQtd2VpZ2h0OjgwMH0KdGFibGV7d2lkdGg6MTAwJTtib3JkZXItY29sbGFwc2U6Y29sbGFwc2U7Zm9udC1zaXplOjExcHh9CnRoe3RleHQtYWxpZ246bGVmdDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC1zaXplOjEwcHg7dGV4dC10cmFuc2Zvcm06dXBwZXJjYXNlO2xldHRlci1zcGFjaW5nOi40cHg7Zm9udC13ZWlnaHQ6NzAwO3BhZGRpbmc6NXB4IDZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQp0ZHtwYWRkaW5nOjZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCByZ2JhKDM0LDY2LDEyNywuMzUpfQp0ZC5tb25ve2ZvbnQtc2l6ZToxMXB4fQouc3RhdHVze3BhZGRpbmc6MTZweDt0ZXh0LWFsaWduOmNlbnRlcjtmb250LXNpemU6MTJweDtjb2xvcjp2YXIoLS1hbWJlcil9Ci5zcGlue2Rpc3BsYXk6aW5saW5lLWJsb2NrO3dpZHRoOjEzcHg7aGVpZ2h0OjEzcHg7Ym9yZGVyOjJweCBzb2xpZCB2YXIoLS1hbWJlcik7Ym9yZGVyLXRvcC1jb2xvcjp0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjUwJTthbmltYXRpb246c3AgLjhzIGxpbmVhciBpbmZpbml0ZTt2ZXJ0aWNhbC1hbGlnbjptaWRkbGU7bWFyZ2luLXJpZ2h0OjVweH0KQGtleWZyYW1lcyBzcHt0b3t0cmFuc2Zvcm06cm90YXRlKDM2MGRlZyl9fQoubm90ZXttYXJnaW4tdG9wOjE0cHg7cGFkZGluZzoxMHB4IDEycHg7YmFja2dyb3VuZDpyZ2JhKDQ3LDExMSwyMjQsLjA0KTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tZGltKTtsaW5lLWhlaWdodDoxLjU1fQoubm90ZSBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjYwMH0KLmZvb3Rlcntib3JkZXItdG9wOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO3BhZGRpbmc6MTBweCA0cHggMDttYXJnaW4tdG9wOjE0cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO3RleHQtYWxpZ246Y2VudGVyfQouc2VjdGlvbntkaXNwbGF5Om5vbmV9LnNlY3Rpb24ub257ZGlzcGxheTpibG9ja30KLmJuYXZ7cG9zaXRpb246Zml4ZWQ7bGVmdDowO3JpZ2h0OjA7Ym90dG9tOjA7ZGlzcGxheTpmbGV4O2JhY2tncm91bmQ6cmdiYSgxMCwxNCwyMywuOTYpO2JhY2tkcm9wLWZpbHRlcjpibHVyKDEwcHgpOy13ZWJraXQtYmFja2Ryb3AtZmlsdGVyOmJsdXIoMTBweCk7Ym9yZGVyLXRvcDoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtwYWRkaW5nOjhweCA0cHggY2FsYyg2cHggKyBlbnYoc2FmZS1hcmVhLWluc2V0LWJvdHRvbSkpO3otaW5kZXg6MTAwfQouYm5hdi1idG57ZmxleDoxO2Rpc3BsYXk6ZmxleDtmbGV4LWRpcmVjdGlvbjpjb2x1bW47YWxpZ24taXRlbXM6Y2VudGVyO2dhcDoycHg7cGFkZGluZzo4cHggNHB4IDZweDtib3JkZXI6bm9uZTtiYWNrZ3JvdW5kOm5vbmU7Y29sb3I6dmFyKC0tbXV0ZWQpO2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjYwMDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO2N1cnNvcjpwb2ludGVyO21pbi1oZWlnaHQ6NDRweDtqdXN0aWZ5LWNvbnRlbnQ6Y2VudGVyfQouYm5hdi1idG4ub257Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ibmF2LWljbyBzdmd7ZGlzcGxheTpibG9ja30KLnJwbC1pbnt3aWR0aDo2NHB4O2JhY2tncm91bmQ6dmFyKC0tY2FyZDIpO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtjb2xvcjp2YXIoLS10ZXh0KTtib3JkZXItcmFkaXVzOjZweDtwYWRkaW5nOjZweCA4cHg7Zm9udC1zaXplOjEycHg7Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9Ci5ycGwtdGF7d2lkdGg6MTAwJTttaW4taGVpZ2h0Ojc2cHg7YmFja2dyb3VuZDp2YXIoLS1jYXJkMik7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2NvbG9yOnZhcigtLXRleHQpO2JvcmRlci1yYWRpdXM6N3B4O3BhZGRpbmc6N3B4IDlweDtmb250LXNpemU6MTFweDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtyZXNpemU6dmVydGljYWw7bWFyZ2luLXRvcDo2cHh9Ci5ycGwtbGlua3tiYWNrZ3JvdW5kOm5vbmU7Ym9yZGVyOm5vbmU7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO3BhZGRpbmc6MDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3RleHQtZGVjb3JhdGlvbjp1bmRlcmxpbmV9Ci5jaGlwOmRpc2FibGVke29wYWNpdHk6LjQ7Y3Vyc29yOmRlZmF1bHR9CiNycGwtbG9ne2Rpc3BsYXk6bm9uZTtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtmb250LXNpemU6MTFweDttYXJnaW4tdG9wOjhweDtwYWRkaW5nOjhweCAxMHB4O2JhY2tncm91bmQ6cmdiYSgwLDAsMCwuMjgpO2JvcmRlci1yYWRpdXM6N3B4O2NvbG9yOnZhcigtLWRpbSk7d2hpdGUtc3BhY2U6cHJlLXdyYXA7d29yZC1icmVhazpicmVhay13b3JkO2xpbmUtaGVpZ2h0OjEuNTttYXgtaGVpZ2h0OjIwMHB4O292ZXJmbG93LXk6YXV0b30KPC9zdHlsZT4KPC9oZWFkPgo8Ym9keT4KCjxkaXYgY2xhc3M9ImhkciI+CiAgPGRpdiBjbGFzcz0iYnJhbmQiPgogICAgPGRpdiBjbGFzcz0ibG9nbyI+SDwvZGl2PgogICAgPGRpdj48ZGl2IGNsYXNzPSJidCI+SE9PUFM8c3Bhbj5CRVQ8L3NwYW4+IDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTBweDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC13ZWlnaHQ6NjAwIj52MTwvc3Bhbj48L2Rpdj4KICAgIDxkaXYgY2xhc3M9ImJzdWIiIGlkPSJjb25uIj4mIzk2Nzk7IGNvbm5lY3RpbmcmaGVsbGlwOzwvZGl2PjwvZGl2PgogIDwvZGl2PgogIDxidXR0b24gY2xhc3M9Imhkci1idG4iIG9uY2xpY2s9ImxvYWRBbGwodHJ1ZSkiPiYjODYzNTsgUmVmcmVzaDwvYnV0dG9uPgo8L2Rpdj4KCjwhLS0gR0FNRVMgLS0+CjxkaXYgaWQ9InNlYy1nYW1lcyIgY2xhc3M9InNlY3Rpb24gb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0ia3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8c2VsZWN0IGNsYXNzPSJjaGlwIiBpZD0iZi1jb25mIiBvbmNoYW5nZT0iYXBwbHlGaWx0ZXJzKCkiPjxvcHRpb24gdmFsdWU9IiI+QWxsIGNvbmZlcmVuY2VzPC9vcHRpb24+PC9zZWxlY3Q+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0iZi10b3AiIG9uY2xpY2s9InRnKHRoaXMsJ3RvcCcpIj5Ub3AgMjU8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJmLWVkZ2UiIG9uY2xpY2s9InRnKHRoaXMsJ2VkZ2UnKSI+RWRnZXMgb25seTwvYnV0dG9uPgogICAgPHNlbGVjdCBjbGFzcz0iY2hpcCIgaWQ9ImYtc29ydCIgb25jaGFuZ2U9ImFwcGx5RmlsdGVycygpIj48b3B0aW9uIHZhbHVlPSJlZGdlIj5Tb3J0OiBFZGdlPC9vcHRpb24+PG9wdGlvbiB2YWx1ZT0idGltZSI+U29ydDogVGlwIHRpbWU8L29wdGlvbj48L3NlbGVjdD4KICA8L2Rpdj4KICA8ZGl2IGNsYXNzPSJmYmFyIiBpZD0ibWluZWRnZSI+CiAgICA8c3BhbiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO21hcmdpbi1yaWdodDoycHgiPk1pbiBlZGdlPC9zcGFuPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCBvbiIgb25jbGljaz0ibWUoMCx0aGlzKSI+QWxsPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJtZSgyLHRoaXMpIj4yJSs8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIG9uY2xpY2s9Im1lKDQsdGhpcykiPjQlKzwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0ibWUoNix0aGlzKSI+NiUrPC9idXR0b24+CiAgPC9kaXY+CiAgPGRpdiBpZD0iZ2FtZXMtc3RhdHVzIiBjbGFzcz0ic3RhdHVzIj48c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBMb2FkaW5nIHNsYXRlJmhlbGxpcDs8L2Rpdj4KICA8ZGl2IGlkPSJnYW1lcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ibm90ZSI+PGI+SG93IHRvIHJlYWQ6PC9iPiBwcm9qZWN0aW9ucyBjb21lIGZyb20gdGhlIFRvcnZpay1mZWQgZWZmaWNpZW5jeSBtb2RlbCAoQWRqT0UgJnRpbWVzOyBBZGpERSAmdGltZXM7IHRlbXBvLCBIQ0EtYWRqdXN0ZWQsIHplcm9lZCBvbiBuZXV0cmFsIGZsb29ycykuIEVkZ2UgY2hpcHMgbGlnaHQgdXAgYXQgdGhlIGZsb29yczogTUwgJmdlOyA8YiBpZD0idGgtbWwiPjQ8L2I+JSAmbWlkZG90OyBTUFIgJmdlOyA8YiBpZD0idGgtc3ByIj41PC9iPiUgJm1pZGRvdDsgVE9UICZnZTsgPGIgaWQ9InRoLXRvdCI+NS41PC9iPiUsIGFuZCByZXF1aXJlICZnZTs8YiBpZD0idGgtYmsiPjM8L2I+IGJvb2tzIHBvc3RpbmcgdGhlIG1hcmtldC4gUGlja3MsIHNpemluZywgYW5kIHRyYWNraW5nIGFycml2ZSBpbiBTMyAmbWRhc2g7IHRoaXMgc3VyZmFjZSBpcyBvYnNlcnZhdGlvbmFsLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gRVYgLS0+CjxkaXYgaWQ9InNlYy1ldiIgY2xhc3M9InNlY3Rpb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0iZXYta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBpZD0iZXYtc3RyaWN0IiBvbmNsaWNrPSJldlN0cmljdCh0aGlzKSI+U3Ryb25nIG9ubHk8L2J1dHRvbj4KICAgIDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1tdXRlZCk7bWFyZ2luLWxlZnQ6NHB4Ij5NaW4gRVY8L3NwYW4+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBvbmNsaWNrPSJldk1pbigwLHRoaXMpIj5GbG9vcjwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0iZXZNaW4oMyx0aGlzKSI+MyUrPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJldk1pbig1LHRoaXMpIj41JSs8L2J1dHRvbj4KICA8L2Rpdj4KICA8ZGl2IGlkPSJldi1hcmJzIj48L2Rpdj4KICA8ZGl2IGlkPSJldi1zdGF0dXMiIGNsYXNzPSJzdGF0dXMiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjwvZGl2PgogIDxkaXYgaWQ9ImV2LXJvd3MiPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPk1ldGhvZDo8L2I+IGZhaXIgcHJvYmFiaWxpdHkgPSBQaW5uYWNsZSBuby12aWcuIEVWJSA9IGZhaXIgJnRpbWVzOyBkZWNpbWFsIG9kZHMgJm1pbnVzOyAxLCBmbG9vciA8YiBpZD0iZXYtZmxvb3IiPjI8L2I+JS4gU3ByZWFkcyBhbmQgdG90YWxzIGFyZSBzY3JlZW5lZCA8Yj5vbmx5IHdoZXJlIGEgcmV0YWlsIGJvb2sgcG9zdHMgdGhlIGV4YWN0IFBpbm5hY2xlIGxpbmU8L2I+ICZtZGFzaDsgbWlzbWF0Y2hlZCBsaW5lcyBhcmUgc2tpcHBlZCwgbmV2ZXIgYXBwcm94aW1hdGVkLiA8Yj5TVFJPTkc8L2I+ID0gdGhlIHByaWNlZCBib29rIGlzICZnZTs8YiBpZD0iZXYtZ2FwIj4yPC9iPiBpbXBsaWVkIHBvaW50cyBiZXR0ZXIgdGhhbiB0aGUgcmVzdCBvZiByZXRhaWwgKHN0YWxlLWxpbmUgc2lnbmFsKTsgPGI+V0VBSzwvYj4gPSBhbGwgb2YgcmV0YWlsIGRpc2FncmVlcyB3aXRoIFBpbm5hY2xlLCB3aGljaCBjYW4gbWVhbiBhbmNob3IgbGFnLiBNb2RlbCBjaGlwcyBhcmUgaW5mb3JtYXRpb25hbCBvbmx5LiBUaGlzIGlzIGEgc2NyZWVuLCBub3QgcGlja3MgJm1kYXNoOyBub3RoaW5nIGhlcmUgZW50ZXJzIHRoZSB0cmFja2VyLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gQkVUUyAtLT4KPGRpdiBpZD0ic2VjLWJldHMiIGNsYXNzPSJzZWN0aW9uIj4KICA8ZGl2IGlkPSJiLXNlYXNvbiIgc3R5bGU9ImRpc3BsYXk6ZmxleDtnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlcjttYXJnaW46MCAwIDEwcHgiPjxidXR0b24gY2xhc3M9ImNoaXAgb24iIGRhdGEtcz0iY3VyIiBvbmNsaWNrPSJzZXRCU2Vhc29uKCdjdXInLHRoaXMpIj5UaGlzIHNlYXNvbjwvYnV0dG9uPjxidXR0b24gY2xhc3M9ImNoaXAiIGRhdGEtcz0icHJldiIgb25jbGljaz0ic2V0QlNlYXNvbigncHJldicsdGhpcykiPkxhc3Qgc2Vhc29uPC9idXR0b24+PGJ1dHRvbiBjbGFzcz0iY2hpcCIgZGF0YS1zPSJhbGwiIG9uY2xpY2s9InNldEJTZWFzb24oJ2FsbCcsdGhpcykiPkFsbDwvYnV0dG9uPjxzcGFuIGlkPSJiLXNsYWJlbCIgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLW11dGVkKTttYXJnaW4tbGVmdDo0cHgiPjwvc3Bhbj48L2Rpdj4KICA8ZGl2IGlkPSJiLXNyYyIgc3R5bGU9ImRpc3BsYXk6ZmxleDtnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlcjttYXJnaW46MCAwIDEwcHgiPjxidXR0b24gY2xhc3M9ImNoaXAgb24iIG9uY2xpY2s9InNldEJTcmMoJ21vZGVsJyx0aGlzKSI+TW9kZWwgcGlja3M8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJzZXRCU3JjKCdldicsdGhpcykiPlBpbm5hY2xlIEVWPC9idXR0b24+PC9kaXY+CiAgPGRpdiBjbGFzcz0ic3RyaXAiIGlkPSJiLWtwaXMiPjwvZGl2PgogIDxkaXYgY2xhc3M9ImNhcmQiIGlkPSJiLWN1cnZlIiBzdHlsZT0iZGlzcGxheTpub25lIj48L2Rpdj4KICA8ZGl2IGlkPSJiZXRzLXN0YXR1cyIgY2xhc3M9InN0YXR1cyIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ic2VjLWhkIj5PcGVuIHBpY2tzPC9kaXY+PGRpdiBpZD0iYi1vcGVuIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiPkJ5IG1hcmtldDwvZGl2PjxkaXYgY2xhc3M9InN0cmlwIiBpZD0iYi1ta3RzIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiPlJlY2VudCBncmFkZWQ8L2Rpdj4KICA8ZGl2IGNsYXNzPSJmYmFyIiBpZD0iYi1maWx0Ij48YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBvbmNsaWNrPSJiZignQUxMJyx0aGlzKSI+QWxsPC9idXR0b24+PGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0iYmYoJ01MJyx0aGlzKSI+TUw8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJiZignU1BSJyx0aGlzKSI+U1BSPC9idXR0b24+PGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0iYmYoJ1RPVCcsdGhpcykiPlRPVDwvYnV0dG9uPjwvZGl2PgogIDxkaXYgaWQ9ImItcmVjZW50Ij48L2Rpdj4KICA8ZGl2IGNsYXNzPSJub3RlIj48Yj5Ib3cgcGlja3Mgd29yazo8L2I+IGEgcGljayBhdXRvLWxvZ3MgdGhlIGZpcnN0IHRpbWUgYSBtYXJrZXQgY2xlYXJzIGl0cyBlZGdlIGZsb29yIChvbmUgcGVyIGdhbWUgcGVyIG1hcmtldCksIHNpemVkIGJ5IHF1YXJ0ZXItS2VsbHkgKDF1ID0gMSUgYmFua3JvbGwsIGNhcHBlZCBhdCA8c3BhbiBpZD0iYi1tYXh1Ij4yPC9zcGFuPnUpLiBDbG9zaW5nIGxpbmVzIGZyZWV6ZSBhdCB0aGUgbGFzdCByZWZyZXNoIGJlZm9yZSB0aXA7IENMViBpcyBncmFkZWQgYWdhaW5zdCBQaW5uYWNsZSB3aGVuIGF2YWlsYWJsZSwgZWxzZSByZXRhaWwgY29uc2Vuc3VzLiBQb3NpdGl2ZSBDTFYgPSB0aGUgcGljayBiZWF0IHRoZSBjbG9zZS48L2Rpdj4KPC9kaXY+Cgo8IS0tIFNDT1JFUyAtLT4KPGRpdiBpZD0ic2VjLXNjb3JlcyIgY2xhc3M9InNlY3Rpb24iPgogIDxkaXYgaWQ9InNjb3Jlcy1zdGF0dXMiIGNsYXNzPSJzdGF0dXMiPjxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IExvYWRpbmcgc2NvcmVzJmhlbGxpcDs8L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiIGlkPSJzaC1saXZlIiBzdHlsZT0iZGlzcGxheTpub25lIj4mIzk2Nzk7IExpdmU8L2Rpdj48ZGl2IGlkPSJzLWxpdmUiPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCIgaWQ9InNoLWRvbmUiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPkZpbmFsPC9kaXY+PGRpdiBpZD0icy1kb25lIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiIGlkPSJzaC11cCIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+VXBjb21pbmc8L2Rpdj48ZGl2IGlkPSJzLXVwIj48L2Rpdj4KPC9kaXY+Cgo8IS0tIERBVEEgLS0+CjxkaXYgaWQ9InNlYy1kYXRhIiBjbGFzcz0ic2VjdGlvbiI+CiAgPGRpdiBjbGFzcz0ic3RyaXAiIGlkPSJkLWtwaXMiPjwvZGl2PgogIDxkaXYgY2xhc3M9ImNhcmQiIGlkPSJkLWhlYWx0aCIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgaWQ9ImQtbWFwIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJjYXJkIiBpZD0iZC10dmltcG9ydCI+CiAgICA8ZGl2IHN0eWxlPSJkaXNwbGF5OmZsZXg7YWxpZ24taXRlbXM6Y2VudGVyO2p1c3RpZnktY29udGVudDpzcGFjZS1iZXR3ZWVuO2dhcDo4cHg7ZmxleC13cmFwOndyYXAiPgogICAgICA8YiBzdHlsZT0iZm9udC1zaXplOjEycHgiPlRvcnZpayByYXRpbmdzPC9iPgogICAgICA8YnV0dG9uIGNsYXNzPSJycGwtbGluayIgb25jbGljaz0idHZUb2dnbGVJbXBvcnQoKSI+aW1wb3J0PC9idXR0b24+CiAgICA8L2Rpdj4KICAgIDxkaXYgaWQ9InR2LWltcG9ydHdyYXAiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPgogICAgICA8ZGl2IHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbjoycHggMCA1cHgiPkxpdmUgcGlja3MgJm1kYXNoOyBjdXJyZW50LXNlYXNvbiByYXRpbmdzLiA8YSBpZD0idHYtbGluay1zZWFzb24iIGhyZWY9IiMiIHRhcmdldD0iX2JsYW5rIiByZWw9Im5vb3BlbmVyIiBzdHlsZT0iY29sb3I6IzdhYTJmNzt0ZXh0LWRlY29yYXRpb246dW5kZXJsaW5lIj50YXAgdG8gb3BlbiB0aGUgZmlsZTwvYT4sIGNvcHkgYWxsLCBwYXN0ZSBiZWxvdzo8L2Rpdj4KICAgICAgPHRleHRhcmVhIGlkPSJ0di1pbXBvcnQiIGNsYXNzPSJycGwtdGEiIHBsYWNlaG9sZGVyPSJQYXN0ZSB0aGUgY29waWVkIHJhdGluZ3MgKENTViBvciBKU09OKSI+PC90ZXh0YXJlYT4KICAgICAgPGRpdiBjbGFzcz0iZmJhciIgc3R5bGU9Im1hcmdpbjo4cHggMCAwIj48YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0idHYtaW1wb3J0YnRuIiBvbmNsaWNrPSJ0dkltcG9ydCgpIj5Vc2UgYXMgY3VycmVudCByYXRpbmdzPC9idXR0b24+PC9kaXY+CiAgICAgIDxkaXYgc3R5bGU9ImJvcmRlci10b3A6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7bWFyZ2luLXRvcDoxMnB4O3BhZGRpbmctdG9wOjEwcHgiPgogICAgICAgIDxkaXYgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLWJvdHRvbTo2cHgiPkJhY2t0ZXN0IChwb2ludC1pbi10aW1lLCBubyBsb29rYWhlYWQpLiA8Yj4xLjwvYj4gVGFwIGVhY2ggZGF0ZSB0byBkb3dubG9hZCBpdHMgcmF0aW5ncyBmaWxlOjwvZGl2PgogICAgICAgIDxkaXYgaWQ9InR2LXRtbGlua3MiIHN0eWxlPSJkaXNwbGF5OmZsZXg7ZmxleC13cmFwOndyYXA7Z2FwOjVweDttYXJnaW4tYm90dG9tOjhweCI+PC9kaXY+CiAgICAgICAgPGRpdiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tYm90dG9tOjZweCI+PGI+Mi48L2I+IFRoZW4gY2hvb3NlIHRoZSBkb3dubG9hZGVkIGZpbGVzIChwaWNrIHNldmVyYWwgYXQgb25jZSkgYW5kIHVwbG9hZCAmbWRhc2g7IHRoZSBkYXRlIGlzIHJlYWQgZnJvbSBlYWNoIGZpbGVuYW1lOjwvZGl2PgogICAgICAgIDxkaXYgY2xhc3M9ImZiYXIiIHN0eWxlPSJnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlciI+PGlucHV0IGlkPSJ0di1maWxlcyIgdHlwZT0iZmlsZSIgYWNjZXB0PSIuZ3osLmpzb24iIG11bHRpcGxlIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21heC13aWR0aDoyMTBweCI+PGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InR2LXVwYnRuIiBvbmNsaWNrPSJ0dlVwbG9hZCgpIj5VcGxvYWQgJmFtcDsgc3RvcmU8L2J1dHRvbj48L2Rpdj4KICAgICAgICA8ZGl2IGlkPSJ0di1pbXBvcnRsb2ciIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbi10b3A6OHB4O3doaXRlLXNwYWNlOnByZS13cmFwO2xpbmUtaGVpZ2h0OjEuNSI+PC9kaXY+CiAgICAgICAgPGRpdiBpZD0idHYtdG1jb3YiIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbi10b3A6NHB4Ij48L2Rpdj4KICAgICAgPC9kaXY+CiAgICA8L2Rpdj4KICA8L2Rpdj4KICA8ZGl2IGNsYXNzPSJjYXJkIiBpZD0iZC1yZXBsYXkiPgogICAgPGRpdiBzdHlsZT0iZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwIj4KICAgICAgPGIgc3R5bGU9ImZvbnQtc2l6ZToxMnB4Ij5SZXBsYXkgY2FsaWJyYXRpb248L2I+CiAgICAgIDxsYWJlbCBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpIj5TZWFzb24mbmJzcDs8aW5wdXQgaWQ9InJwbC15ZWFyIiBjbGFzcz0icnBsLWluIiB2YWx1ZT0iMjAyNiIgaW5wdXRtb2RlPSJudW1lcmljIiBhdXRvY29tcGxldGU9Im9mZiIgb25jaGFuZ2U9InR2U2Vhc29uTGluaygpO3R2VG1MaW5rcygpIj48L2xhYmVsPgogICAgICA8bGFiZWwgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLW11dGVkKSI+QnVkZ2V0Jm5ic3A7PGlucHV0IGlkPSJycGwtYnVkZ2V0IiBjbGFzcz0icnBsLWluIiB2YWx1ZT0iMjAwMDAiIGlucHV0bW9kZT0ibnVtZXJpYyIgYXV0b2NvbXBsZXRlPSJvZmYiPjwvbGFiZWw+CiAgICA8L2Rpdj4KICAgIDxkaXYgY2xhc3M9ImZiYXIiIHN0eWxlPSJtYXJnaW46OXB4IDAgMCI+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtcGxhbiIgb25jbGljaz0icnBsUGxhbigpIj5QbGFuPC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtaW5nZXN0IiBvbmNsaWNrPSJycGxMb29wKCdpbmdlc3QnKSI+SW5nZXN0PC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtcmVzdWx0cyIgb25jbGljaz0icnBsUmVzdWx0cygpIj5SZXN1bHRzPC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtcnVuIiBvbmNsaWNrPSJycGxMb29wKCdydW4nKSI+UnVuPC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtcmVwb3J0IiBvbmNsaWNrPSJycGxSZXBvcnQodHJ1ZSkiPlJlcG9ydDwvYnV0dG9uPgogICAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0icnBsLXN0b3AiIG9uY2xpY2s9InJwbFN0b3BGbigpIiBzdHlsZT0iZGlzcGxheTpub25lO2JvcmRlci1jb2xvcjp2YXIoLS1yZWRUZXh0KTtjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5NjMyOyBTdG9wPC9idXR0b24+CiAgICA8L2Rpdj4KICAgIDxkaXYgc3R5bGU9Im1hcmdpbi10b3A6N3B4Ij48YnV0dG9uIGNsYXNzPSJycGwtbGluayIgb25jbGljaz0icnBsVG9nZ2xlQ3N2KCkiPnBhc3RlIHJlc3VsdHMgQ1NWPC9idXR0b24+CiAgICAgIDxkaXYgaWQ9InJwbC1jc3Z3cmFwIiBzdHlsZT0iZGlzcGxheTpub25lIj48dGV4dGFyZWEgaWQ9InJwbC1jc3YiIGNsYXNzPSJycGwtdGEiIHBsYWNlaG9sZGVyPSJkYXRlLGF3YXksaG9tZSxhd2F5X3B0cyxob21lX3B0cyxuZXV0cmFsJiMxMDsyMDI2LTAxLTEwLEdvbnphZ2EsRHVrZSw3MCw4MCwiPjwvdGV4dGFyZWE+PC9kaXY+CiAgICA8L2Rpdj4KICAgIDxkaXYgaWQ9InJwbC1sb2ciPjwvZGl2PgogICAgPGRpdiBpZD0icnBsLXN0YXR1cyIgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDo4cHg7bGluZS1oZWlnaHQ6MS42Ij4maGVsbGlwOzwvZGl2PgogICAgPGRpdiBpZD0icnBsLXJlcG9ydCIgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bGluZS1oZWlnaHQ6MS42Ij48L2Rpdj4KICA8L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiPlQtUmFuayBUb3AgMjUgPHNwYW4gc3R5bGU9InRleHQtdHJhbnNmb3JtOm5vbmU7Y29sb3I6dmFyKC0tbXV0ZWQpIiBpZD0iZC15ciI+PC9zcGFuPjwvZGl2PgogIDxkaXYgY2xhc3M9ImNhcmQiIHN0eWxlPSJvdmVyZmxvdy14OmF1dG8iPjx0YWJsZSBpZD0iZC10YmwiPjx0aGVhZD48dHI+PHRoPiM8L3RoPjx0aD5UZWFtPC90aD48dGg+Q29uZjwvdGg+PHRoIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij5BZGpPRTwvdGg+PHRoIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij5BZGpERTwvdGg+PHRoIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij5BZGpUPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkJhcnRoYWc8L3RoPjwvdHI+PC90aGVhZD48dGJvZHk+PC90Ym9keT48L3RhYmxlPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPkRpYWdub3N0aWNzOjwvYj4gPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvZGVidWcvb2Rkczwvc3Bhbj4gcHJvYmVzIHRoZSBPZGRzIEFQSSBsaXZlICZtaWRkb3Q7IDxzcGFuIGNsYXNzPSJtb25vIj4vYXBpL2RlYnVnL3RvcnZpazwvc3Bhbj4gc2hvd3MgcmF3IHJvd3MgKyB0aGUgZGV0ZWN0ZWQgY29sdW1uIGxvY2sgJm1pZGRvdDsgPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvZGVidWcvdGVhbW1hcDwvc3Bhbj4gbGlzdHMgdW5tYXRjaGVkIG5hbWVzIChhZGQgZml4ZXMgdmlhIDxzcGFuIGNsYXNzPSJtb25vIj5QT1NUIC9hcGkvYWRtaW4vYWxpYXM8L3NwYW4+KS48L2Rpdj4KPC9kaXY+Cgo8ZGl2IGNsYXNzPSJmb290ZXIiPkhPT1BTQkVUIHYxLjUuMCAmbWRhc2g7IE9kZHM6IFRoZSBPZGRzIEFQSSAmbWlkZG90OyBNb2RlbDogYmFydHRvcnZpay5jb20gJmJ1bGw7ICYjOTg4ODsgRW50ZXJ0YWlubWVudCAmYW1wOyBhbmFseXNpcyBvbmx5PC9kaXY+Cgo8ZGl2IGNsYXNzPSJibmF2Ij4KPGJ1dHRvbiBjbGFzcz0iYm5hdi1idG4gb24iIG9uY2xpY2s9ImdvKCdnYW1lcycsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48Y2lyY2xlIGN4PSIxMiIgY3k9IjEyIiByPSI5Ii8+PHBhdGggZD0iTTUuNiA1LjZjNCAzIDguOCA5LjggOS44IDE1TTE4LjQgNS42Yy00IDMtOC44IDkuOC05LjggMTVNMyAxMmgxOCIvPjwvc3ZnPjwvc3Bhbj5HYW1lczwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ2V2Jyx0aGlzKSI+PHNwYW4gY2xhc3M9ImJuYXYtaWNvIj48c3ZnIHdpZHRoPSIxOSIgaGVpZ2h0PSIxOSIgdmlld0JveD0iMCAwIDI0IDI0IiBmaWxsPSJub25lIiBzdHJva2U9ImN1cnJlbnRDb2xvciIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiPjxwYXRoIGQ9Ik0xMyAyTDQgMTRoNmwtMSA4IDktMTJoLTZsMS04eiIvPjwvc3ZnPjwvc3Bhbj5FVjwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ2JldHMnLHRoaXMpIj48c3BhbiBjbGFzcz0iYm5hdi1pY28iPjxzdmcgd2lkdGg9IjE5IiBoZWlnaHQ9IjE5IiB2aWV3Qm94PSIwIDAgMjQgMjQiIGZpbGw9Im5vbmUiIHN0cm9rZT0iY3VycmVudENvbG9yIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCI+PHBhdGggZD0iTTQgN2gxNnYzYTIgMiAwIDAwMCA0djNINHYtM2EyIDIgMCAwMDAtNFY3eiIvPjxwYXRoIGQ9Ik0xMyA3djEwIiBzdHJva2UtZGFzaGFycmF5PSIyIDMiLz48L3N2Zz48L3NwYW4+QmV0czwvYnV0dG9uPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biIgb25jbGljaz0iZ28oJ3Njb3JlcycsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48Y2lyY2xlIGN4PSIxMiIgY3k9IjEyIiByPSI5Ii8+PHBhdGggZD0iTTEyIDd2NWwzIDIiLz48L3N2Zz48L3NwYW4+U2NvcmVzPC9idXR0b24+CjxidXR0b24gY2xhc3M9ImJuYXYtYnRuIiBvbmNsaWNrPSJnbygnZGF0YScsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48cGF0aCBkPSJNNCAxOVY1TTQgMTloMTZNOCAxNnYtNU0xMiAxNlY4TTE2IDE2di0zTTIwIDE2VjYiLz48L3N2Zz48L3NwYW4+RGF0YTwvYnV0dG9uPgo8L2Rpdj4KCjxzY3JpcHQ+CnZhciBTTEFURT1udWxsLEZJTFQ9e2NvbmY6IiIsdG9wOmZhbHNlLGVkZ2U6ZmFsc2UsbWluRTowfSxTSE9XPTI1LFRIPXtNTDo0LFNQUjo1LFRPVDo1LjUsQk9PS1M6M307CnZhciBFVkQ9bnVsbCxFVkY9e3N0cmljdDp0cnVlLG1pbjowfSxSQz1udWxsLEJGSUxUPSJBTEwiLEJTSE9XPTI1OwpmdW5jdGlvbiBnbyh0LGJ0bil7WyJnYW1lcyIsImV2IiwiYmV0cyIsInNjb3JlcyIsImRhdGEiXS5mb3JFYWNoKGZ1bmN0aW9uKHMpe2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJzZWMtIitzKS5jbGFzc0xpc3QudG9nZ2xlKCJvbiIscz09PXQpO30pOwogIGRvY3VtZW50LnF1ZXJ5U2VsZWN0b3JBbGwoIi5ibmF2LWJ0biIpLmZvckVhY2goZnVuY3Rpb24oYil7Yi5jbGFzc0xpc3QucmVtb3ZlKCJvbiIpO30pO2J0bi5jbGFzc0xpc3QuYWRkKCJvbiIpOwogIGlmKHQ9PT0iZXYiKWxvYWRFdigpO2lmKHQ9PT0iYmV0cyIpbG9hZEJldHMoKTtpZih0PT09InNjb3JlcyIpbG9hZFNjb3JlcygpO2lmKHQ9PT0iZGF0YSIpbG9hZERhdGEoKTt9CmZ1bmN0aW9uIHRnKGJ0bixrKXtGSUxUW2tdPSFGSUxUW2tdO2J0bi5jbGFzc0xpc3QudG9nZ2xlKCJvbiIsRklMVFtrXSk7YXBwbHlGaWx0ZXJzKCk7fQpmdW5jdGlvbiBtZSh2LGJ0bil7RklMVC5taW5FPXY7ZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbCgiI21pbmVkZ2UgLmNoaXAiKS5mb3JFYWNoKGZ1bmN0aW9uKGIpe2IuY2xhc3NMaXN0LnJlbW92ZSgib24iKTt9KTtidG4uY2xhc3NMaXN0LmFkZCgib24iKTthcHBseUZpbHRlcnMoKTt9CmZ1bmN0aW9uIGZtdEFtKHYpe2lmKHY9PT1udWxsfHx2PT09dW5kZWZpbmVkKXJldHVybiAiXHUyMDE0IjtyZXR1cm4gdj4wPyIrIit2OiIiK3Y7fQpmdW5jdGlvbiBmbXRTcHIodil7aWYodj09PW51bGx8fHY9PT11bmRlZmluZWQpcmV0dXJuICJcdTIwMTQiO3JldHVybiAodj4wPyIrIjoiIikrdjt9CmZ1bmN0aW9uIHRpcFRpbWUoaXNvKXt0cnl7dmFyIGQ9bmV3IERhdGUoaXNvKTtyZXR1cm4gZC50b0xvY2FsZVRpbWVTdHJpbmcoW10se2hvdXI6Im51bWVyaWMiLG1pbnV0ZToiMi1kaWdpdCJ9KTt9Y2F0Y2goZSl7cmV0dXJuICIiO319CmZ1bmN0aW9uIGxhc3RXb3JkKHMpe3JldHVybiBzP3Muc3BsaXQoIiAiKS5wb3AoKToiPyI7fQpmdW5jdGlvbiBzaG9ydE5hbWUocyl7aWYoIXMpcmV0dXJuICI/Ijt2YXIgdz1zLnNwbGl0KCIgIik7cmV0dXJuIHcubGVuZ3RoPjI/dy5zbGljZSgwLC0xKS5qb2luKCIgIik6czt9CgpmdW5jdGlvbiBiZXN0RWRnZShnKXt2YXIgYj0wO1siTUwiLCJTUFIiLCJUT1QiXS5mb3JFYWNoKGZ1bmN0aW9uKG0pe3ZhciBlPWcuZWRnZXMmJmcuZWRnZXNbbV07aWYoZSYmZS5vayYmZS5lZGdlKjEwMD5iKWI9ZS5lZGdlKjEwMDt9KTtyZXR1cm4gYjt9CmZ1bmN0aW9uIGhhc0hvdChnKXt2YXIgaD1mYWxzZTtbIk1MIiwiU1BSIiwiVE9UIl0uZm9yRWFjaChmdW5jdGlvbihtKXt2YXIgZT1nLmVkZ2VzJiZnLmVkZ2VzW21dO2lmKGUmJmUub2smJmUuaG90KWg9dHJ1ZTt9KTtyZXR1cm4gaDt9CgpmdW5jdGlvbiBhcHBseUZpbHRlcnMoKXsKICBpZighU0xBVEUpcmV0dXJuO1NIT1c9MjU7RklMVC5jb25mPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJmLWNvbmYiKS52YWx1ZTsKICByZW5kZXJHYW1lcygpOwp9CmZ1bmN0aW9uIHJlbmRlckdhbWVzKCl7CiAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcyIpLHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJnYW1lcy1zdGF0dXMiKTsKICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjsKICB2YXIgZ3M9KFNMQVRFLmdhbWVzfHxbXSkuc2xpY2UoKTsKICBpZihGSUxULmNvbmYpZ3M9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiBnLmFDb25mPT09RklMVC5jb25mfHxnLmhDb25mPT09RklMVC5jb25mO30pOwogIGlmKEZJTFQudG9wKWdzPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gKGcuYVJhbmsmJmcuYVJhbms8PTI1KXx8KGcuaFJhbmsmJmcuaFJhbms8PTI1KTt9KTsKICBpZihGSUxULmVkZ2UpZ3M9Z3MuZmlsdGVyKGhhc0hvdCk7CiAgaWYoRklMVC5taW5FPjApZ3M9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiBiZXN0RWRnZShnKT49RklMVC5taW5FO30pOwogIHZhciBzb3J0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJmLXNvcnQiKS52YWx1ZTsKICBpZihzb3J0PT09ImVkZ2UiKWdzLnNvcnQoZnVuY3Rpb24oYSxiKXtyZXR1cm4gYmVzdEVkZ2UoYiktYmVzdEVkZ2UoYSk7fSk7CiAgZWxzZSBncy5zb3J0KGZ1bmN0aW9uKGEsYil7cmV0dXJuIG5ldyBEYXRlKGEuY29tbWVuY2UpLW5ldyBEYXRlKGIuY29tbWVuY2UpO30pOwogIGlmKCFncy5sZW5ndGgpewogICAgdmFyIGlubmVyOwogICAgaWYoIShTTEFURS5nYW1lc3x8W10pLmxlbmd0aCl7CiAgICAgIGlubmVyPSc8Yj5ObyBOQ0FBQiBnYW1lcyBvbiB0aGUgYm9hcmQuPC9iPjxicj48YnI+JysoU0xBVEUubm90ZT9TTEFURS5ub3RlOidUaGUgc2Vhc29uIHJ1bnMgTm92ZW1iZXIgXHUyMDEzIEFwcmlsLiBUaGUgZGF0YSBsYXllciBpcyBsaXZlIGFuZCB3aWxsIHBvcHVsYXRlIHdoZW4gYm9va3MgcG9zdCB0aGUgZmlyc3Qgc2xhdGVzLicpOwogICAgfSBlbHNlIHsKICAgICAgaW5uZXI9J05vIGdhbWVzIG1hdGNoIHRoZSBjdXJyZW50IGZpbHRlcnMgXHUyMDE0ICcrKFNMQVRFLmdhbWVzLmxlbmd0aCkrJyBvbiB0aGUgc2xhdGUgdG9kYXkuIENsZWFyIGEgZmlsdGVyIHRvIHNlZSB0aGVtLic7CiAgICB9CiAgICBlbC5pbm5lckhUTUw9JzxkaXYgY2xhc3M9ImVtcHR5Ij4nK2lubmVyKyc8L2Rpdj4nO3JldHVybjsKICB9CiAgdmFyIGh0bWw9Z3Muc2xpY2UoMCxTSE9XKS5tYXAoZnVuY3Rpb24oZyl7CiAgICB2YXIgYVI9Zy5hUmFuayYmZy5hUmFuazw9MjU/JzxzcGFuIGNsYXNzPSJyayI+IycrZy5hUmFuaysnPC9zcGFuPic6Jyc7CiAgICB2YXIgaFI9Zy5oUmFuayYmZy5oUmFuazw9MjU/JzxzcGFuIGNsYXNzPSJyayI+IycrZy5oUmFuaysnPC9zcGFuPic6Jyc7CiAgICB2YXIgbWV0YT0nPHNwYW4gY2xhc3M9InRhZyB0YWctdGltZSI+Jyt0aXBUaW1lKGcuY29tbWVuY2UpKyc8L3NwYW4+JzsKICAgIGlmKGcubmV1dHJhbCltZXRhKz0nPHNwYW4gY2xhc3M9InRhZyB0YWctbiIgdGl0bGU9IicrKGcudmVudWVOYW1lfHwibmV1dHJhbCBzaXRlIikrJyI+Tjwvc3Bhbj4nOwogICAgaWYoZy5waWNrYWJsZT09PWZhbHNlKW1ldGErPSc8c3BhbiBjbGFzcz0idGFnIiBzdHlsZT0iYmFja2dyb3VuZDpyZ2JhKDIyNCwxNjgsNTgsLjEyKTtjb2xvcjojZTBhODNhO2JvcmRlcjoxcHggc29saWQgcmdiYSgyMjQsMTY4LDU4LC4zNSkiIHRpdGxlPSJubyBhdXRvLXBpY2sgdW50aWwgdGhlIHZlbnVlIGlzIHZlcmlmaWVkIj52ZW51ZSA/PC9zcGFuPic7CiAgICBtZXRhKz0nPHNwYW4gY2xhc3M9InRhZyB0YWctYmsiPicrZy5uQm9va3MrJyBiazwvc3Bhbj4nOwogICAgaWYoZy5waWNrcyYmZy5waWNrcy5sZW5ndGgpbWV0YSs9JzxzcGFuIGNsYXNzPSJ0YWciIHN0eWxlPSJiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMTIpO2NvbG9yOnZhcigtLWdyZWVuKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjQsMTg0LDEyNCwuMzUpIj5cdTI2MDUgJytnLnBpY2tzLmpvaW4oIi8iKSsnPC9zcGFuPic7CiAgICB2YXIgcHJvaixlZGdlcyxzaGFycD0iIjsKICAgIGlmKCFnLm1vZGVsZWQpewogICAgICBwcm9qPSc8ZGl2IGNsYXNzPSJnLXByb2oiPjxzcGFuIGNsYXNzPSJhd2FpdCI+JysoZy5tb2RlbFJlYXNvbnx8InVucmF0ZWQgdGVhbSIpKyc8L3NwYW4+PC9kaXY+JztlZGdlcz0iIjsKICAgIH0gZWxzZSB7CiAgICAgIHByb2o9JzxkaXYgY2xhc3M9ImctcHJvaiI+JysKICAgICAgICAnPHNwYW4+UHJvaiA8YiBjbGFzcz0ibW9ubyI+JytnLnByb2ouYVB0cy50b0ZpeGVkKDApKydcdTIwMTMnK2cucHJvai5oUHRzLnRvRml4ZWQoMCkrJzwvYj48L3NwYW4+JysKICAgICAgICAnPHNwYW4+TWFyZ2luIDxiIGNsYXNzPSJtb25vIj4nK2xhc3RXb3JkKGcuaG9tZSkuc2xpY2UoMCwzKS50b1VwcGVyQ2FzZSgpKycgJytmbXRTcHIoKygtKGcucHJvai5tYXJnaW4pKS50b0ZpeGVkKDEpKSsnPC9iPicrKGcuYm9vay5zcHJIIT09bnVsbD8nIDxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPmJvb2sgJytmbXRTcHIoZy5ib29rLnNwckgpKyc8L3NwYW4+JzonJykrJzwvc3Bhbj4nKwogICAgICAgICc8c3Bhbj5Ub3RhbCA8YiBjbGFzcz0ibW9ubyI+JytnLnByb2oudG90YWwudG9GaXhlZCgxKSsnPC9iPicrKGcuYm9vay50b3QhPT1udWxsPycgPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+Ym9vayAnK2cuYm9vay50b3QrJzwvc3Bhbj4nOicnKSsnPC9zcGFuPicrCiAgICAgICc8L2Rpdj4nOwogICAgICBlZGdlcz0nPGRpdiBjbGFzcz0iZy1lZGdlcyI+JytbIk1MIiwiU1BSIiwiVE9UIl0ubWFwKGZ1bmN0aW9uKG0pewogICAgICAgIHZhciBlPWcuZWRnZXNbbV07CiAgICAgICAgaWYoIWV8fCFlLm9rKXJldHVybiAnPHNwYW4gY2xhc3M9ImVkIj48c3BhbiBjbGFzcz0ic2QiPicrbSsnPC9zcGFuPjxzcGFuIGNsYXNzPSJhd2FpdCIgc3R5bGU9InBhZGRpbmc6MCA0cHgiPicrKGUmJmUucmVhc29uP2UucmVhc29uOiJcdTIwMTQiKSsnPC9zcGFuPjwvc3Bhbj4nOwogICAgICAgIHJldHVybiAnPHNwYW4gY2xhc3M9ImVkJysoZS5ob3Q/IiBob3QiOiIiKSsnIj48c3BhbiBjbGFzcz0ic2QiPicrbSsnICcrZS5sYWJlbCsnPC9zcGFuPisnKyhlLmVkZ2UqMTAwKS50b0ZpeGVkKDEpKyclPC9zcGFuPic7CiAgICAgIH0pLmpvaW4oIiIpKyc8L2Rpdj4nOwogICAgICBpZihnLnNoYXJwJiYoZy5zaGFycC5zcHJIIT09bnVsbHx8Zy5zaGFycC50b3QhPT1udWxsKSl7CiAgICAgICAgc2hhcnA9JzxkaXYgY2xhc3M9Imctc2hhcnAiPjxiPlBpbm5hY2xlPC9iPiAnKyhnLnNoYXJwLnNwckghPT1udWxsPygic3ByZWFkICIrZm10U3ByKGcuc2hhcnAuc3BySCkpOiIiKSsoZy5zaGFycC50b3QhPT1udWxsPygiIFx1MDBiNyB0b3RhbCAiK2cuc2hhcnAudG90KToiIikrKGcuc2hhcnAucEhvbWUhPT1udWxsPygiIFx1MDBiNyBuby12aWcgaG9tZSAiKyhnLnNoYXJwLnBIb21lKjEwMCkudG9GaXhlZCgwKSsiJSIpOiIiKSsnPC9kaXY+JzsKICAgICAgfQogICAgfQogICAgcmV0dXJuICc8ZGl2IGNsYXNzPSJnY2FyZCI+PGRpdiBjbGFzcz0iZy10b3AiPjxkaXYgY2xhc3M9ImctdGVhbXMiPicrYVIrc2hvcnROYW1lKGcuYXdheSkrJzxzcGFuIGNsYXNzPSJhdCI+QDwvc3Bhbj4nK2hSK3Nob3J0TmFtZShnLmhvbWUpKyc8L2Rpdj48ZGl2IGNsYXNzPSJnLW1ldGEiPicrbWV0YSsnPC9kaXY+PC9kaXY+Jytwcm9qK2VkZ2VzK3NoYXJwKyc8L2Rpdj4nOwogIH0pLmpvaW4oIiIpOwogIGlmKGdzLmxlbmd0aD5TSE9XKWh0bWwrPSc8YnV0dG9uIGNsYXNzPSJtb3JlIiBvbmNsaWNrPSJTSE9XKz0yNTtyZW5kZXJHYW1lcygpIj5TaG93IG1vcmUgKCcrKGdzLmxlbmd0aC1TSE9XKSsnIHJlbWFpbmluZyk8L2J1dHRvbj4nOwogIGVsLmlubmVySFRNTD1odG1sOwp9CmZ1bmN0aW9uIHJlbmRlcktwaXMoKXsKICB2YXIgYz1TTEFURS5jb3ZlcmFnZXx8e30saz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgia3BpcyIpOwogIHZhciBob3Q9KFNMQVRFLmdhbWVzfHxbXSkuZmlsdGVyKGhhc0hvdCkubGVuZ3RoOwogIGsuaW5uZXJIVE1MPQogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPkdhbWVzPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoYy5nYW1lc3x8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKGMubGluZWR8fDApKycgd2l0aCBsaW5lczwvZGl2PjwvZGl2PicrCiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+TW9kZWxlZDwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGMubW9kZWxlZHx8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPlRvcnZpay1yYXRlZCBib3RoIHNpZGVzPC9kaXY+PC9kaXY+JysKICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5FZGdlczwvZGl2PjxkaXYgY2xhc3M9InYiIHN0eWxlPSJjb2xvcjonKyhob3Q+MD8idmFyKC0tZ3JlZW4pIjoidmFyKC0tbXV0ZWQpIikrJyI+Jytob3QrJzwvZGl2PjxkaXYgY2xhc3M9InMiPk1MICcrVEguTUwrJyUgLyBTUFIgJytUSC5TUFIrJyUgLyBUT1QgJytUSC5UT1QrJyU8L2Rpdj48L2Rpdj4nOwogIHZhciBjb25mPXt9OyhTTEFURS5nYW1lc3x8W10pLmZvckVhY2goZnVuY3Rpb24oZyl7aWYoZy5hQ29uZiljb25mW2cuYUNvbmZdPTE7aWYoZy5oQ29uZiljb25mW2cuaENvbmZdPTE7fSk7CiAgdmFyIHNlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZi1jb25mIiksY3VyPXNlbC52YWx1ZTsKICBzZWwuaW5uZXJIVE1MPSc8b3B0aW9uIHZhbHVlPSIiPkFsbCBjb25mZXJlbmNlczwvb3B0aW9uPicrT2JqZWN0LmtleXMoY29uZikuc29ydCgpLm1hcChmdW5jdGlvbih4KXtyZXR1cm4gJzxvcHRpb24nKyh4PT09Y3VyPyIgc2VsZWN0ZWQiOiIiKSsnPicreCsnPC9vcHRpb24+Jzt9KS5qb2luKCIiKTsKfQpmdW5jdGlvbiBsb2FkU2xhdGUoZm9yY2UpewogIGlmKGZvcmNlKXt2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IExvYWRpbmcgc2xhdGUmaGVsbGlwOyc7fQogIHJldHVybiBmZXRjaCgiL2FwaS9zbGF0ZSIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oZCl7CiAgICBpZihkLm9rPT09ZmFsc2UpdGhyb3cgbmV3IEVycm9yKGQuZXJyb3J8fCJzbGF0ZSBmYWlsZWQiKTsKICAgIFNMQVRFPWQ7CiAgICBpZihkLnRocmVzaG9sZHMpe1RIPWQudGhyZXNob2xkcztkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidGgtbWwiKS50ZXh0Q29udGVudD1USC5NTDtkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidGgtc3ByIikudGV4dENvbnRlbnQ9VEguU1BSO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0aC10b3QiKS50ZXh0Q29udGVudD1USC5UT1Q7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInRoLWJrIikudGV4dENvbnRlbnQ9VEguQk9PS1M7fQogICAgcmVuZGVyS3BpcygpO3JlbmRlckdhbWVzKCk7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiY29ubiIpLmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWdyZWVuKSI+JiM5Njc5Ozwvc3Bhbj4gJysoZC5xdW90YSYmZC5xdW90YS5yZW1haW5pbmchPW51bGw/KCJxdW90YSAiK2QucXVvdGEucmVtYWluaW5nKToiY29ubmVjdGVkIik7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7CiAgICB2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjsKICAgIHN0LmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLXJlZFRleHQpIj4mIzk4ODg7ICcrZS5tZXNzYWdlKyc8L3NwYW4+ICZtZGFzaDsgPGJ1dHRvbiBjbGFzcz0iaGRyLWJ0biIgb25jbGljaz0ibG9hZEFsbCh0cnVlKSI+UmV0cnk8L2J1dHRvbj4nOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImNvbm4iKS5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5Njc5Ozwvc3Bhbj4gZXJyb3InOwogIH0pOwp9CmZ1bmN0aW9uIHNyb3coZyl7CiAgdmFyIGxpdmU9IWcuY29tcGxldGVkJiZnLnNjb3JlczsKICB2YXIgc2M9Zy5zY29yZXM/Zy5zY29yZXMubWFwKGZ1bmN0aW9uKHMpe3JldHVybiBzLnNjb3JlO30pLmpvaW4oIiBcdTIwMTMgIik6IiI7CiAgcmV0dXJuICc8ZGl2IGNsYXNzPSJzcm93Ij48ZGl2PjxkaXYgY2xhc3M9InQiPicrc2hvcnROYW1lKGcuYXdheV90ZWFtKSsnIEAgJytzaG9ydE5hbWUoZy5ob21lX3RlYW0pKyc8L2Rpdj48ZGl2IGNsYXNzPSJzdCI+JysoZy5jb21wbGV0ZWQ/IkZpbmFsIjoobGl2ZT8nPHNwYW4gY2xhc3M9ImxpdmUtZG90Ij4mIzk2Nzk7IGxpdmU8L3NwYW4+Jzp0aXBUaW1lKGcuY29tbWVuY2VfdGltZSkpKSsnPC9kaXY+PC9kaXY+PGRpdiBjbGFzcz0ic2MiPicrKHNjfHwiXHUyMDE0IikrJzwvZGl2PjwvZGl2Pic7Cn0KZnVuY3Rpb24gbG9hZFNjb3JlcygpewogIHZhciBzdD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2NvcmVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IExvYWRpbmcgc2NvcmVzJmhlbGxpcDsnOwogIGZldGNoKCIvYXBpL3Njb3JlcyIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oZCl7CiAgICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjsKICAgIHZhciBncz1kLmdhbWVzfHxbXTsKICAgIHZhciBsaXZlPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gIWcuY29tcGxldGVkJiZnLnNjb3Jlczt9KTsKICAgIHZhciBkb25lPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gZy5jb21wbGV0ZWQ7fSk7CiAgICB2YXIgdXA9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiAhZy5jb21wbGV0ZWQmJiFnLnNjb3Jlczt9KTsKICAgIGZ1bmN0aW9uIHB1dChpZCxoZCxhcnIpe2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKGhkKS5zdHlsZS5kaXNwbGF5PWFyci5sZW5ndGg/ImJsb2NrIjoibm9uZSI7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoaWQpLmlubmVySFRNTD1hcnIubWFwKHNyb3cpLmpvaW4oIiIpO30KICAgIHB1dCgicy1saXZlIiwic2gtbGl2ZSIsbGl2ZSk7cHV0KCJzLWRvbmUiLCJzaC1kb25lIixkb25lKTtwdXQoInMtdXAiLCJzaC11cCIsdXAuc2xpY2UoMCw0MCkpOwogICAgaWYoIWdzLmxlbmd0aCl7c3Quc3R5bGUuZGlzcGxheT0iYmxvY2siO3N0LmlubmVySFRNTD0nPGRpdiBjbGFzcz0iZW1wdHkiPjxiPk5vIGdhbWVzIGluIHRoZSBzY29yZXMgd2luZG93LjwvYj48YnI+PGJyPlNlYXNvbiBydW5zIE5vdmVtYmVyIFx1MjAxMyBBcHJpbC48L2Rpdj4nO30KICB9KS5jYXRjaChmdW5jdGlvbihlKXtzdC5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5ODg4OyAnK2UubWVzc2FnZSsnPC9zcGFuPic7fSk7Cn0KZnVuY3Rpb24gbG9hZERhdGEoKXsKICBQcm9taXNlLmFsbFNldHRsZWQoW2ZldGNoKCIvYXBpL2hlYWx0aCIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLGZldGNoKCIvYXBpL3JhdGluZ3M/dG9wPTI1IikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSksZmV0Y2goIi9hcGkvZGVidWcvdGVhbW1hcD9zdW1tYXJ5PTEiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KV0pLnRoZW4oZnVuY3Rpb24ocmVzKXsKICAgIHZhciBoPXJlc1swXS5zdGF0dXM9PT0iZnVsZmlsbGVkIj9yZXNbMF0udmFsdWU6e307CiAgICB2YXIgcnQ9cmVzWzFdLnN0YXR1cz09PSJmdWxmaWxsZWQiP3Jlc1sxXS52YWx1ZTp7fTsKICAgIHZhciB0bT1yZXNbMl0uc3RhdHVzPT09ImZ1bGZpbGxlZCI/cmVzWzJdLnZhbHVlOnt9OwogICAgdmFyIHR2PWgudG9ydmlrfHx7fTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJkLWtwaXMiKS5pbm5lckhUTUw9CiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5PZGRzIHF1b3RhPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhoLnF1b3RhJiZoLnF1b3RhLnJlbWFpbmluZyE9bnVsbD9oLnF1b3RhLnJlbWFpbmluZzoiXHUyMDE0IikrJzwvZGl2PjxkaXYgY2xhc3M9InMiPmNyZWRpdHMgcmVtYWluaW5nPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlRvcnZpazwvZGl2PjxkaXYgY2xhc3M9InYiPicrKHR2LnRlYW1zfHwwKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysodHYueWVhcnx8IiIpKycgJm1pZGRvdDsgJysodHYubW9kZXx8Im5vdCBsb2FkZWQiKSsodHYuYWdlTWluIT1udWxsPygnICZtaWRkb3Q7ICcrdHYuYWdlTWluKydtIG9sZCcpOicnKSsnPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlJlZGlzPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoaC5yZWRpcz8ib24iOiJvZmYiKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoaC5yZWRpcz8icGVyc2lzdGVuY2UgYWN0aXZlIjoic2V0IFVwc3Rhc2ggZW52IHZhcnMiKSsnPC9kaXY+PC9kaXY+JzsKICAgIChmdW5jdGlvbigpewogICAgICB2YXIgaGg9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImQtaGVhbHRoIiksaHA9W10saHNldj0ib2siOwogICAgICBpZihoLnNlYXNvbkFjdGl2ZT09PWZhbHNlKXtocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj4mIzk2Nzk7IE9mZnNlYXNvbiBcdTIwMTQgb2RkcyBwb2xsaW5nIHBhdXNlZCAoc2F2aW5nIHF1b3RhKTwvc3Bhbj4nKTt9CiAgICAgIGVsc2UgaWYoaC5vZGRzS2V5PT09ZmFsc2Upe2hzZXY9Indhcm4iO2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjojZTBhODNhIj4mIzk4ODg7IE9ERFNfQVBJX0tFWSBub3Qgc2V0PC9zcGFuPicpO30KICAgICAgZWxzZSBpZihoLmxhc3RPZGRzRXJyb3Ipe2hzZXY9ImVyciI7aHAucHVzaCgnPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLXJlZFRleHQpIj4mIzk4ODg7IE9kZHMgZmV0Y2ggRkFJTElORzogJysoaC5sYXN0T2Rkc0Vycm9yLm1zZ3x8ImVycm9yIikrJzwvc3Bhbj4nKTt9CiAgICAgIGVsc2UgaWYoaC5zbGF0ZUFnZU1pbiE9bnVsbCYmaC5zbGF0ZUFnZU1pbj42MCl7aHNldj0id2FybiI7aHAucHVzaCgnPHNwYW4gc3R5bGU9ImNvbG9yOiNlMGE4M2EiPiYjOTg4ODsgU2xhdGUgc3RhbGUgKCcraC5zbGF0ZUFnZU1pbisnbSBvbGQpIFx1MjAxNCBsYXN0IGZldGNoIGhhZCAnKyhoLmxhc3RTbGF0ZUdhbWVzIT1udWxsP2gubGFzdFNsYXRlR2FtZXM6Ij8iKSsnIGdhbWVzPC9zcGFuPicpO30KICAgICAgZWxzZXtocC5wdXNoKCc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tZ3JlZW4pIj4mIzk2Nzk7IExpdmUgb2RkcyBPSycrKGgubGFzdFNsYXRlR2FtZXMhPW51bGw/KCcgXHUyMDE0ICcraC5sYXN0U2xhdGVHYW1lcysnIGdhbWVzLCAnKyhoLnNsYXRlQWdlTWluIT1udWxsP2guc2xhdGVBZ2VNaW4rJ20gYWdvJzoianVzdCBub3ciKSk6IiIpKyc8L3NwYW4+Jyk7fQogICAgICBpZih0di5lcnJvcil7aWYoaHNldiE9PSJlcnIiKWhzZXY9Indhcm4iO2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjojZTBhODNhIj4mIzk4ODg7IFJhdGluZ3M6ICcrdHYuZXJyb3IrJzwvc3Bhbj4nKTt9CiAgICAgIGVsc2UgaWYodHYudGVhbXMpe2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1kaW0pIj5SYXRpbmdzOiAnK3R2LnRlYW1zKycgdGVhbXMgXHUwMGI3ICcrKHR2LnllYXJ8fCIiKSsnICcrKHR2Lm1vZGV8fCIiKSsodHYuYWdlTWluIT1udWxsPygnIFx1MDBiNyAnK3R2LmFnZU1pbisnbSBvbGQnKToiIikrJzwvc3Bhbj4nKTt9CiAgICAgIChoLmFsZXJ0c3x8W10pLmZvckVhY2goZnVuY3Rpb24oYSl7aWYoYS5zZXY9PT0iZXJyIiloc2V2PSJlcnIiO2Vsc2UgaWYoaHNldiE9PSJlcnIiKWhzZXY9Indhcm4iO2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjonKyhhLnNldj09PSJlcnIiPyd2YXIoLS1yZWRUZXh0KSc6JyNlMGE4M2EnKSsnO2ZvbnQtd2VpZ2h0OjcwMCI+JiM5ODg4OyAnK2EubXNnKyc8L3NwYW4+Jyk7fSk7CiAgICAgIHZhciBsdj1oLmxpdmV8fHt9O2lmKGguc2Vhc29uQWN0aXZlIT09ZmFsc2UmJmx2LmVuYWJsZWQpe2hwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1kaW0pIj5BdXRvLXJ1bjogJysobHYubGFzdFB1bGxNaW4hPW51bGw/J2xhc3Qgb2RkcyBwdWxsICcrbHYubGFzdFB1bGxNaW4rJ20gYWdvJzonbm8gcHVsbCB5ZXQnKSsnIFx1MDBiNyAnKyhsdi5wdWxsc1RvZGF5fHwwKSsnIHRvZGF5JysobHYubGFzdFJlYXNvbj8nICgnK2x2Lmxhc3RSZWFzb24rJyknOicnKSsnPC9zcGFuPicpO30KICAgICAgdmFyIHB1PWgucHVzaHx8e307aWYoaC5zZWFzb25BY3RpdmUhPT1mYWxzZSl7aHAucHVzaChwdS50b3BpY1NldD8nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWRpbSkiPlB1c2ggYWxlcnRzOiBvbicrKHB1LnNlbnQ/KCcgXHUwMGI3ICcrcHUuc2VudCsnIHNlbnQnKyhwdS5sYXN0QXRNaW4hPW51bGw/JywgbGFzdCAnK3B1Lmxhc3RBdE1pbisnbSBhZ28nOicnKSk6JycpKyc8L3NwYW4+JzonPHNwYW4gc3R5bGU9ImNvbG9yOiNlMGE4M2EiPlB1c2ggYWxlcnRzOiBvZmYgXHUyMDE0IHNldCBOVEZZX1RPUElDIGluIFJlbmRlcjwvc3Bhbj4nKTt9CiAgICAgIHZhciBvdD1oLnRyYWNrZXImJmgudHJhY2tlci5vcGVuO2lmKG90KWhwLnB1c2goJzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1kaW0pIj4nK290Kycgb3BlbiBwaWNrJysob3Q+MT8icyI6IiIpKycgYXdhaXRpbmcgZ3JhZGU8L3NwYW4+Jyk7CiAgICAgIGhoLnN0eWxlLmRpc3BsYXk9ImJsb2NrIjsKICAgICAgaGguc3R5bGUuYm9yZGVyQ29sb3I9aHNldj09PSJlcnIiPyJyZ2JhKDIyMCw4MCw4MCwuNTUpIjooaHNldj09PSJ3YXJuIj8icmdiYSgyMjQsMTY4LDU4LC41KSI6IiIpOwogICAgICBoaC5pbm5lckhUTUw9JzxiIHN0eWxlPSJmb250LXNpemU6MTJweCI+TGl2ZSBzdGF0dXM8L2I+PGRpdiBzdHlsZT0iZm9udC1zaXplOjExcHg7bWFyZ2luLXRvcDo1cHg7bGluZS1oZWlnaHQ6MS44Ij4nK2hwLmpvaW4oIjxicj4iKSsnPC9kaXY+JzsKICAgIH0pKCk7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZC1tYXAiKS5pbm5lckhUTUw9JzxiIHN0eWxlPSJmb250LXNpemU6MTJweCI+VGVhbS1uYW1lIG1hcDwvYj48ZGl2IHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbi10b3A6NHB4Ij4nKyh0bS5tYXRjaGVkIT1udWxsPyh0bS5tYXRjaGVkKyIgbWF0Y2hlZCBcdTAwYjcgIit0bS51bm1hdGNoZWQrIiB1bm1hdGNoZWQiKyh0bS51bm1hdGNoZWQ+MD8nIFx1MjAxNCByZXZpZXcgPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvZGVidWcvdGVhbW1hcDwvc3Bhbj4nOiIiKSk6InBvcHVsYXRlcyBvbmNlIGEgc2xhdGUgaGFzIGJlZW4gZmV0Y2hlZCIpKyc8L2Rpdj4nOwogICAgcnBsU3RhdHVzKCk7cnBsUmVwb3J0KGZhbHNlKTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJkLXlyIikudGV4dENvbnRlbnQ9dHYueWVhcj8oIlx1MjAxNCAiK3R2LnllYXIpOiIiOwogICAgdmFyIHRiPWRvY3VtZW50LnF1ZXJ5U2VsZWN0b3IoIiNkLXRibCB0Ym9keSIpOwogICAgdGIuaW5uZXJIVE1MPShydC50ZWFtc3x8W10pLm1hcChmdW5jdGlvbih0KXtyZXR1cm4gJzx0cj48dGQgY2xhc3M9Im1vbm8iPicrdC5yYW5rKyc8L3RkPjx0ZD4nK3QudGVhbSsnPC90ZD48dGQgc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+JysodC5jb25mfHwiIikrJzwvdGQ+PHRkIGNsYXNzPSJtb25vIiBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+Jyt0LmFkam9lLnRvRml4ZWQoMSkrJzwvdGQ+PHRkIGNsYXNzPSJtb25vIiBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+Jyt0LmFkamRlLnRvRml4ZWQoMSkrJzwvdGQ+PHRkIGNsYXNzPSJtb25vIiBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+Jyt0LmFkanQudG9GaXhlZCgxKSsnPC90ZD48dGQgY2xhc3M9Im1vbm8iIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij4nK3QuYmFydGhhZy50b0ZpeGVkKDMpKyc8L3RkPjwvdHI+Jzt9KS5qb2luKCIiKXx8Jzx0cj48dGQgY29sc3Bhbj0iNyIgc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+UmF0aW5ncyBub3QgbG9hZGVkIFx1MjAxNCBjaGVjayAvYXBpL2RlYnVnL3RvcnZpazwvdGQ+PC90cj4nOwogIH0pOwp9CmZ1bmN0aW9uIGV2U3RyaWN0KGJ0bil7RVZGLnN0cmljdD0hRVZGLnN0cmljdDtidG4uY2xhc3NMaXN0LnRvZ2dsZSgib24iLEVWRi5zdHJpY3QpO3JlbmRlckV2KCk7fQpmdW5jdGlvbiBldk1pbih2LGJ0bil7RVZGLm1pbj12O3ZhciBicz1idG4ucGFyZW50Tm9kZS5xdWVyeVNlbGVjdG9yQWxsKCIuY2hpcCIpO2Zvcih2YXIgaT0xO2k8YnMubGVuZ3RoO2krKylic1tpXS5jbGFzc0xpc3QucmVtb3ZlKCJvbiIpO2J0bi5jbGFzc0xpc3QuYWRkKCJvbiIpO3JlbmRlckV2KCk7fQpmdW5jdGlvbiBldkxhYmVsKHIpe2lmKHIubWt0PT09Ik1MIilyZXR1cm4gKHIuc2lkZT09PSJob21lIj9zaG9ydE5hbWUoci5ob21lKTpzaG9ydE5hbWUoci5hd2F5KSkrIiBNTCI7aWYoci5ta3Q9PT0iU1BSIilyZXR1cm4gKHIuc2lkZT09PSJob21lIj9zaG9ydE5hbWUoci5ob21lKTpzaG9ydE5hbWUoci5hd2F5KSkrIiAiK2ZtdFNwcihyLmxpbmUpO3JldHVybiAoci5zaWRlPT09Im92ZXIiPyJPdmVyICI6IlVuZGVyICIpK3IubGluZTt9CmZ1bmN0aW9uIGV2Um93KHIpewogIHZhciBiYWRnZT1yLnN0cm9uZz8nPHNwYW4gY2xhc3M9InRhZyIgc3R5bGU9ImJhY2tncm91bmQ6cmdiYSgyNCwxODQsMTI0LC4xMik7Y29sb3I6dmFyKC0tZ3JlZW4pO2JvcmRlcjoxcHggc29saWQgcmdiYSgyNCwxODQsMTI0LC4zNSkiPlNUUk9ORzwvc3Bhbj4nOic8c3BhbiBjbGFzcz0idGFnIHRhZy1iayI+V0VBSzwvc3Bhbj4nOwogIHZhciBtZGw9ci5tb2RlbD8oci5tb2RlbC5hZ3JlZT8nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWdyZWVuKSI+JiMxMDAwMzsgbW9kZWwgJysoci5tb2RlbC5wKjEwMCkudG9GaXhlZCgwKSsnJTwvc3Bhbj4nOic8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj4mIzEwMDA3OyBtb2RlbCAnKyhyLm1vZGVsLnAqMTAwKS50b0ZpeGVkKDApKyclPC9zcGFuPicpOic8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj4mbWRhc2g7IHVubW9kZWxlZDwvc3Bhbj4nOwogIHJldHVybiAnPGRpdiBjbGFzcz0iZ2NhcmQiPjxkaXYgY2xhc3M9ImctdG9wIj48ZGl2IGNsYXNzPSJnLXRlYW1zIj4nK3Nob3J0TmFtZShyLmF3YXkpKyc8c3BhbiBjbGFzcz0iYXQiPkA8L3NwYW4+JytzaG9ydE5hbWUoci5ob21lKSsnPC9kaXY+PGRpdiBjbGFzcz0iZy1tZXRhIj48c3BhbiBjbGFzcz0idGFnIHRhZy10aW1lIj4nK3RpcFRpbWUoci5jb21tZW5jZSkrJzwvc3Bhbj4nK2JhZGdlKyc8L2Rpdj48L2Rpdj4nKwogICc8ZGl2IGNsYXNzPSJnLXByb2oiPjxzcGFuPjxiPicrZXZMYWJlbChyKSsnPC9iPiAnK2ZtdEFtKHIub2RkcykrJyBAICcrci5ib29rKyc8L3NwYW4+PHNwYW4+RVYgPGIgY2xhc3M9Im1vbm8iIHN0eWxlPSJjb2xvcjp2YXIoLS1ncmVlbikiPisnK3IuZXZQY3QudG9GaXhlZCgxKSsnJTwvYj48L3NwYW4+PHNwYW4+ZmFpciA8YiBjbGFzcz0ibW9ubyI+Jysoci5wRmFpcioxMDApLnRvRml4ZWQoMSkrJyU8L2I+PC9zcGFuPicrKHIuZ2FwIT1udWxsPyc8c3Bhbj5nYXAgPGIgY2xhc3M9Im1vbm8iPicrci5nYXAudG9GaXhlZCgxKSsnPC9iPjwvc3Bhbj4nOicnKSsnPC9kaXY+JysKICAnPGRpdiBjbGFzcz0iZy1zaGFycCI+JyttZGwrJyAmbWlkZG90OyAnK3IubkJvb2tzKycgYm9vaycrKHIubkJvb2tzPjE/InMiOiIiKSsnIGF0IHRoaXMgbGluZTwvZGl2PjwvZGl2Pic7Cn0KZnVuY3Rpb24gcmVuZGVyRXYoKXsKICBpZighRVZEKXJldHVybjsKICB2YXIgYz1FVkQuY292ZXJhZ2V8fHt9OwogIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1rcGlzIikuaW5uZXJIVE1MPQogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPkNhbmRpZGF0ZXM8L2Rpdj48ZGl2IGNsYXNzPSJ2Ij4nKyhjLmNhbmRpZGF0ZXN8fDApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhjLnN0cm9uZ3x8MCkrJyBzdHJvbmc8L2Rpdj48L2Rpdj4nKwogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPkFuY2hvcjwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGMud2l0aFNoYXJwfHwwKSsnLycrKGMubGluZWR8fDApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj5nYW1lcyB3LyBQaW5uYWNsZTwvZGl2PjwvZGl2PicrCiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+QXJiczwvZGl2PjxkaXYgY2xhc3M9InYiIHN0eWxlPSJjb2xvcjonKygoRVZELmFyYnN8fFtdKS5sZW5ndGg/InZhcigtLWdyZWVuKSI6InZhcigtLW11dGVkKSIpKyciPicrKChFVkQuYXJic3x8W10pLmxlbmd0aCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPnR3by13YXkgTUw8L2Rpdj48L2Rpdj4nOwogIGlmKEVWRC5jZmcpe2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1mbG9vciIpLnRleHRDb250ZW50PUVWRC5jZmcubWluO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1nYXAiKS50ZXh0Q29udGVudD1FVkQuY2ZnLnN0cm9uZ0dhcDt9CiAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LWFyYnMiKS5pbm5lckhUTUw9KEVWRC5hcmJzfHxbXSkubWFwKGZ1bmN0aW9uKGEpewogICAgcmV0dXJuICc8ZGl2IGNsYXNzPSJjYXJkIiBzdHlsZT0iYm9yZGVyOjFweCBzb2xpZCByZ2JhKDI0LDE4NCwxMjQsLjQpIj48YiBzdHlsZT0iZm9udC1zaXplOjEycHg7Y29sb3I6dmFyKC0tZ3JlZW4pIj5BUkIgKycrYS5hcmJQY3QudG9GaXhlZCgyKSsnJTwvYj48ZGl2IHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1kaW0pO21hcmdpbi10b3A6M3B4Ij4nK3Nob3J0TmFtZShhLmF3YXkpKycgJytmbXRBbShhLmxlZ0Eub2RkcykrJyBAICcrYS5sZWdBLmJvb2srJyAmbmJzcDsvJm5ic3A7ICcrc2hvcnROYW1lKGEuaG9tZSkrJyAnK2ZtdEFtKGEubGVnSC5vZGRzKSsnIEAgJythLmxlZ0guYm9vaysnPC9kaXY+PC9kaXY+JzsKICB9KS5qb2luKCIiKTsKICB2YXIgcm93cz0oRVZELnJvd3N8fFtdKS5maWx0ZXIoZnVuY3Rpb24ocil7aWYoRVZGLnN0cmljdCYmIXIuc3Ryb25nKXJldHVybiBmYWxzZTtpZihyLmV2UGN0PEVWRi5taW4pcmV0dXJuIGZhbHNlO3JldHVybiB0cnVlO30pOwogIHZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYtcm93cyIpOwogIGlmKCFyb3dzLmxlbmd0aCl7CiAgICB2YXIgaW5uZXI7CiAgICBpZighKEVWRC5yb3dzfHxbXSkubGVuZ3RoKXtpbm5lcj1FVkQubm90ZT8oJzxiPk5vIGNhbmRpZGF0ZXMuPC9iPjxicj48YnI+JytFVkQubm90ZSk6KCFjLmxpbmVkPyc8Yj5ObyBsaW5lZCBnYW1lcyBvbiB0aGUgYm9hcmQuPC9iPjxicj48YnI+VGhlIHNjcmVlbiBwb3B1bGF0ZXMgd2hlbiBib29rcyBwb3N0IHNsYXRlcy4nOighYy53aXRoU2hhcnA/JzxiPk5vIFBpbm5hY2xlIGFuY2hvcnMgeWV0LjwvYj48YnI+PGJyPlBpbm5hY2xlIHR5cGljYWxseSBwb3N0cyBjbG9zZXIgdG8gdGlwOyB0aGUgc2NyZWVuIG5lZWRzIGl0cyBuby12aWcgbGluZSBhcyB0aGUgZmFpciBiYXNlbGluZS4nOic8Yj5ObyArRVYgZm91bmQgYWJvdmUgdGhlICcrKEVWRC5jZmc/RVZELmNmZy5taW46MikrJyUgZmxvb3IuPC9iPjxicj48YnI+UmV0YWlsIGlzIGluIGxpbmUgd2l0aCBQaW5uYWNsZSByaWdodCBub3cuJykpO30KICAgIGVsc2UgaW5uZXI9KEVWRC5yb3dzLmxlbmd0aCkrJyBjYW5kaWRhdGUnKyhFVkQucm93cy5sZW5ndGg+MT8icyI6IiIpKycgaGlkZGVuIGJ5IGZpbHRlcnMg4oCUIHRvZ2dsZSBTdHJvbmcgb25seSBvciBsb3dlciBtaW4gRVYuJzsKICAgIGVsLmlubmVySFRNTD0nPGRpdiBjbGFzcz0iZW1wdHkiPicraW5uZXIrJzwvZGl2Pic7cmV0dXJuOwogIH0KICBlbC5pbm5lckhUTUw9cm93cy5tYXAoZXZSb3cpLmpvaW4oIiIpOwp9CmZ1bmN0aW9uIGxvYWRFdigpewogIHZhciBzdD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYtc3RhdHVzIik7c3Quc3R5bGUuZGlzcGxheT0iYmxvY2siO3N0LmlubmVySFRNTD0nPHNwYW4gY2xhc3M9InNwaW4iPjwvc3Bhbj4gU2Nhbm5pbmcgdnMgUGlubmFjbGXigKYnOwogIGZldGNoKCIvYXBpL2V2IikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSkudGhlbihmdW5jdGlvbihkKXsKICAgIGlmKGQub2s9PT1mYWxzZSl0aHJvdyBuZXcgRXJyb3IoZC5lcnJvcnx8ImV2IGZhaWxlZCIpOwogICAgc3Quc3R5bGUuZGlzcGxheT0ibm9uZSI7RVZEPWQ7cmVuZGVyRXYoKTsKICB9KS5jYXRjaChmdW5jdGlvbihlKXtzdC5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+4pqgICcrZS5tZXNzYWdlKyc8L3NwYW4+Jzt9KTsKfQpmdW5jdGlvbiBzcGFya1N2ZyhkYWlseSl7CiAgdmFyIHc9MzAwLGg9NjQscGFkPTUsdmFscz1kYWlseS5tYXAoZnVuY3Rpb24oeCl7cmV0dXJuIHguY3VtO30pOwogIHZhciBtbj1NYXRoLm1pbigwLE1hdGgubWluLmFwcGx5KG51bGwsdmFscykpLG14PU1hdGgubWF4KDAsTWF0aC5tYXguYXBwbHkobnVsbCx2YWxzKSk7CiAgaWYobXg9PT1tbilteD1tbisxOwogIGZ1bmN0aW9uIFgoaSl7cmV0dXJuIHBhZCtpKih3LTIqcGFkKS8oZGFpbHkubGVuZ3RoLTEpO30KICBmdW5jdGlvbiBZKHYpe3JldHVybiBoLXBhZC0odi1tbikqKGgtMipwYWQpLyhteC1tbik7fQogIHZhciBkPWRhaWx5Lm1hcChmdW5jdGlvbih4LGkpe3JldHVybiAoaT8iTCI6Ik0iKStYKGkpLnRvRml4ZWQoMSkrIiAiK1koeC5jdW0pLnRvRml4ZWQoMSk7fSkuam9pbigiICIpOwogIHZhciBjb2w9dmFsc1t2YWxzLmxlbmd0aC0xXT49MD8idmFyKC0tZ3JlZW4pIjoidmFyKC0tcmVkVGV4dCkiOwogIHJldHVybiAnPHN2ZyB2aWV3Qm94PSIwIDAgJyt3KycgJytoKyciIHN0eWxlPSJ3aWR0aDoxMDAlO2hlaWdodDo2NHB4O2Rpc3BsYXk6YmxvY2s7bWFyZ2luLXRvcDo2cHgiPjxsaW5lIHgxPSIwIiB5MT0iJytZKDApLnRvRml4ZWQoMSkrJyIgeDI9IicrdysnIiB5Mj0iJytZKDApLnRvRml4ZWQoMSkrJyIgc3Ryb2tlPSJ2YXIoLS1ib3JkZXIpIiBzdHJva2Utd2lkdGg9IjEiLz48cGF0aCBkPSInK2QrJyIgZmlsbD0ibm9uZSIgc3Ryb2tlPSInK2NvbCsnIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lam9pbj0icm91bmQiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIvPjwvc3ZnPic7Cn0KZnVuY3Rpb24gYmYobSxidG4pe0JGSUxUPW07QlNIT1c9MjU7ZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbCgiI2ItZmlsdCAuY2hpcCIpLmZvckVhY2goZnVuY3Rpb24oYil7Yi5jbGFzc0xpc3QucmVtb3ZlKCJvbiIpO30pO2J0bi5jbGFzc0xpc3QuYWRkKCJvbiIpO3JlbmRlclJlY2VudCgpO30KZnVuY3Rpb24gcmVuZGVyUmVjZW50KCl7CiAgaWYoIVJDKXJldHVybjsKICB2YXIgbGlzdD1SQy5yZWNlbnR8fFtdOwogIGlmKEJGSUxUIT09IkFMTCIpbGlzdD1saXN0LmZpbHRlcihmdW5jdGlvbihwKXtyZXR1cm4gcC5ta3Q9PT1CRklMVDt9KTsKICB2YXIgZWw9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItcmVjZW50Iik7CiAgaWYoIWxpc3QubGVuZ3RoKXtlbC5pbm5lckhUTUw9JzxkaXYgY2xhc3M9ImVtcHR5Ij5Ob3RoaW5nIGdyYWRlZCcrKEJGSUxUIT09IkFMTCI/IiBmb3IgIitCRklMVDoiIikrJyB5ZXQg4oCUIHJlc3VsdHMgbGFuZCB+MmggYWZ0ZXIgZmluYWwuPC9kaXY+JztyZXR1cm47fQogIHZhciBodG1sPWxpc3Quc2xpY2UoMCxCU0hPVykubWFwKGdyYWRlZFJvdykuam9pbigiIik7CiAgaWYobGlzdC5sZW5ndGg+QlNIT1cpaHRtbCs9JzxidXR0b24gY2xhc3M9Im1vcmUiIG9uY2xpY2s9IkJTSE9XKz0yNTtyZW5kZXJSZWNlbnQoKSI+U2hvdyBtb3JlICgnKyhsaXN0Lmxlbmd0aC1CU0hPVykrJyk8L2J1dHRvbj4nOwogIGVsLmlubmVySFRNTD1odG1sOwp9CmZ1bmN0aW9uIGNsdlN0cihwKXtpZighcC5jbHYpcmV0dXJuICJcdTIwMTQiO3ZhciB2PXAuY2x2LnB0cyE9bnVsbD9wLmNsdi5wdHM6cC5jbHYucHA7cmV0dXJuICh2PjA/IisiOiIiKSt2KyhwLmNsdi5wdHMhPW51bGw/IiBwdHMiOiIgcHAiKTt9CmZ1bmN0aW9uIHBpY2tDYXJkKHApewogIHJldHVybiAnPGRpdiBjbGFzcz0iZ2NhcmQiPjxkaXYgY2xhc3M9ImctdG9wIj48ZGl2IGNsYXNzPSJnLXRlYW1zIj4nK3Nob3J0TmFtZShwLmF3YXkpKyc8c3BhbiBjbGFzcz0iYXQiPkA8L3NwYW4+JytzaG9ydE5hbWUocC5ob21lKSsnPC9kaXY+PGRpdiBjbGFzcz0iZy1tZXRhIj48c3BhbiBjbGFzcz0idGFnIHRhZy10aW1lIj4nK3RpcFRpbWUocC5jb21tZW5jZSkrJzwvc3Bhbj48c3BhbiBjbGFzcz0idGFnIHRhZy1iayI+JytwLmJvb2srJzwvc3Bhbj48L2Rpdj48L2Rpdj4nKwogICc8ZGl2IGNsYXNzPSJnLXByb2oiPjxzcGFuPjxiPicrcC5ta3QrJyAnK3AubGFiZWwrJzwvYj4nKyhwLnNyYz09PSJldiI/JyA8c3BhbiBjbGFzcz0idGFnIHRhZy1iayI+JysocC5zdHJvbmc/J0VWIFNUUk9ORyc6J0VWJykrJzwvc3Bhbj4nOicnKSsnPC9zcGFuPjxzcGFuPicrKHAuZXZQY3QhPW51bGw/J0VWIDxiIGNsYXNzPSJtb25vIj4nKyhwLmV2UGN0PjA/JysnOicnKStwLmV2UGN0KyclPC9iPic6J2VkZ2UgPGIgY2xhc3M9Im1vbm8iPicrKHAuZWRnZSoxMDApLnRvRml4ZWQoMSkrJyU8L2I+JykrJzwvc3Bhbj48c3Bhbj5zdGFrZSA8YiBjbGFzcz0ibW9ubyI+JytwLnN0YWtlVSsndTwvYj48L3NwYW4+PHNwYW4+bW9kZWwgPGIgY2xhc3M9Im1vbm8iPicrKHAucE1vZGVsKjEwMCkudG9GaXhlZCgwKSsnJTwvYj48L3NwYW4+PC9kaXY+PC9kaXY+JzsKfQpmdW5jdGlvbiBncmFkZWRSb3cocCl7CiAgdmFyIGNvbD1wLnN0YXR1cz09PSJ3b24iPyJ2YXIoLS1ncmVlbikiOnAuc3RhdHVzPT09Imxvc3QiPyJ2YXIoLS1yZWRUZXh0KSI6InZhcigtLWRpbSkiOwogIHZhciB1PXAucmVzdWx0PygocC5yZXN1bHQudW5pdHM+MD8iKyI6IiIpK3AucmVzdWx0LnVuaXRzLnRvRml4ZWQoMikrInUiKToiIjsKICByZXR1cm4gJzxkaXYgY2xhc3M9InNyb3ciPjxkaXY+PGRpdiBjbGFzcz0idCI+JytwLm1rdCsnICcrcC5sYWJlbCsnIDxzcGFuIHN0eWxlPSJjb2xvcjonK2NvbCsnO2ZvbnQtd2VpZ2h0OjgwMCI+JytwLnN0YXR1cy50b1VwcGVyQ2FzZSgpKyc8L3NwYW4+PC9kaXY+PGRpdiBjbGFzcz0ic3QiPicrc2hvcnROYW1lKHAuYXdheSkrJyBAICcrc2hvcnROYW1lKHAuaG9tZSkrJyBcdTAwYjcgQ0xWICcrY2x2U3RyKHApKyc8L2Rpdj48L2Rpdj48ZGl2IGNsYXNzPSJzYyIgc3R5bGU9ImNvbG9yOicrY29sKyciPicrdSsnPC9kaXY+PC9kaXY+JzsKfQp2YXIgQlNFQVNPTj0iY3VyIjsgLy8gdjEuNC4wIHNlYXNvbi1zcGxpdCByZWNvcmQKdmFyIEJTUkM9Im1vZGVsIjsgLy8gdjEuNS4wIG1vZGVsIHZzIFBpbm5hY2xlLUVWIGxlZGdlcgpmdW5jdGlvbiBzZXRCU3JjKHMsYnRuKXtCU1JDPXM7QXJyYXkucHJvdG90eXBlLmZvckVhY2guY2FsbChkb2N1bWVudC5xdWVyeVNlbGVjdG9yQWxsKCIjYi1zcmMgLmNoaXAiKSxmdW5jdGlvbihiKXtiLmNsYXNzTGlzdC5yZW1vdmUoIm9uIik7fSk7aWYoYnRuKWJ0bi5jbGFzc0xpc3QuYWRkKCJvbiIpO2xvYWRCZXRzKCk7fQpmdW5jdGlvbiBzZXRCU2Vhc29uKHMsYnRuKXtCU0VBU09OPXM7QXJyYXkucHJvdG90eXBlLmZvckVhY2guY2FsbChkb2N1bWVudC5xdWVyeVNlbGVjdG9yQWxsKCIjYi1zZWFzb24gLmNoaXAiKSxmdW5jdGlvbihiKXtiLmNsYXNzTGlzdC5yZW1vdmUoIm9uIik7fSk7aWYoYnRuKWJ0bi5jbGFzc0xpc3QuYWRkKCJvbiIpO2xvYWRCZXRzKCk7fQpmdW5jdGlvbiBsb2FkQmV0cygpewogIHZhciBzdD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYmV0cy1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBHcmFkaW5nICYgbG9hZGluZ1x1MjAyNic7CiAgZmV0Y2goIi9hcGkvdHJhY2svZ3JhZGUiLHttZXRob2Q6IlBPU1QifSkuY2F0Y2goZnVuY3Rpb24oKXtyZXR1cm4gbnVsbDt9KS50aGVuKGZ1bmN0aW9uKCl7CiAgICByZXR1cm4gUHJvbWlzZS5hbGwoW2ZldGNoKCIvYXBpL3BpY2tzIikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSksZmV0Y2goIi9hcGkvdHJhY2svcmVjb3JkP249MTAwJnNlYXNvbj0iK0JTRUFTT04rIiZzcmM9IitCU1JDKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KV0pOwogIH0pLnRoZW4oZnVuY3Rpb24ocmVzKXsKICAgIHN0LnN0eWxlLmRpc3BsYXk9Im5vbmUiOwogICAgdmFyIHBrPXJlc1swXSxyYz1yZXNbMV0sUj0ocmMucmVjb3JkJiZyYy5yZWNvcmQuQUxMKXx8e307CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1zbGFiZWwiKS50ZXh0Q29udGVudD0ocmMuc2Vhc29uTGFiZWx8fCIiKSsocmMudG90YWxQaWNrcyE9bnVsbD8iIFx1MDBiNyAiK3JjLnRvdGFsUGlja3MrIiBwaWNrcyI6IiIpOwogICAgaWYocGsua2VsbHkpZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItbWF4dSIpLnRleHRDb250ZW50PXBrLmtlbGx5Lm1heFU7CiAgICB2YXIgbmV0Q29sPVIubmV0PjA/InZhcigtLWdyZWVuKSI6KFIubmV0PDA/InZhcigtLXJlZFRleHQpIjoidmFyKC0tdGV4dCkiKTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLWtwaXMiKS5pbm5lckhUTUw9CiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5OZXQgdW5pdHM8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iIHN0eWxlPSJjb2xvcjonK25ldENvbCsnIj4nKyhSLm5ldD4wPyIrIjoiIikrKFIubmV0IT1udWxsP1IubmV0OjApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhSLnN0YWtlZHx8MCkrJ3Ugc3Rha2VkPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlJlY29yZDwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyI+JysoUi53fHwwKSsnLScrKFIubHx8MCkrKFIucD8nLScrUi5wOicnKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoUi5vcGVufHwwKSsnIG9wZW4nKyhyYy5wZW5kaW5nR3JhZGU/JyBcdTAwYjcgJytyYy5wZW5kaW5nR3JhZGUrJyBhd2FpdGluZyBncmFkZSc6JycpKyc8L2Rpdj48L2Rpdj4nKwogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+Uk9JPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhSLnJvaSE9bnVsbD8oUi5yb2kqMTAwKS50b0ZpeGVkKDEpKyclJzonXHUyMDE0JykrJzwvZGl2PjxkaXYgY2xhc3M9InMiPmdyYWRlZCBzdGFrZXM8L2Rpdj48L2Rpdj4nKwogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+Q0xWIGJlYXQ8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iPicrKFIuYmVhdCE9bnVsbD8oUi5iZWF0KjEwMCkudG9GaXhlZCgwKSsnJSc6J1x1MjAxNCcpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhSLmNsdk58fDApKycgd2l0aCBDTFY8L2Rpdj48L2Rpdj4nOwogICAgdmFyIG9wZW5TPShway5vcGVufHxbXSkuZmlsdGVyKGZ1bmN0aW9uKHApe3JldHVybiAocC5zcmN8fCJtb2RlbCIpPT09QlNSQzt9KTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLW9wZW4iKS5pbm5lckhUTUw9b3BlblMubGVuZ3RoP29wZW5TLm1hcChwaWNrQ2FyZCkuam9pbigiIik6JzxkaXYgY2xhc3M9ImVtcHR5Ij48Yj5ObyBvcGVuIHBpY2tzLjwvYj48YnI+PGJyPlBpY2tzIGF1dG8tbG9nIHdoZW4gYSBtb2RlbGVkIG1hcmtldCBjbGVhcnMgaXRzIGZsb29yIChNTCAnK1RILk1MKyclIC8gU1BSICcrVEguU1BSKyclIC8gVE9UICcrVEguVE9UKyclKS48L2Rpdj4nOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItbWt0cyIpLmlubmVySFRNTD1bIk1MIiwiU1BSIiwiVE9UIl0ubWFwKGZ1bmN0aW9uKG0pewogICAgICB2YXIgcj0ocmMucmVjb3JkJiZyYy5yZWNvcmRbbV0pfHx7fTsKICAgICAgcmV0dXJuICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj4nK20rJzwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyI+Jysoci53fHwwKSsnLScrKHIubHx8MCkrKHIucD8nLScrci5wOicnKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoKHIubmV0PjA/IisiOiIiKSsoci5uZXQhPW51bGw/ci5uZXQ6MCkpKyd1IFx1MDBiNyBDTFYgJysoci5hdmdDbHYhPW51bGw/KChyLmF2Z0Nsdj4wPyIrIjoiIikrci5hdmdDbHYrKG09PT0iTUwiPyIgcHAiOiIgcHRzIikpOiJcdTIwMTQiKSsnPC9kaXY+PC9kaXY+JzsKICAgIH0pLmpvaW4oIiIpOwogICAgUkM9cmM7QlNIT1c9MjU7cmVuZGVyUmVjZW50KCk7CiAgICB2YXIgY3Y9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItY3VydmUiKTsKICAgIGlmKHJjLmRhaWx5JiZyYy5kYWlseS5sZW5ndGg+PTIpe2N2LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtjdi5pbm5lckhUTUw9JzxiIHN0eWxlPSJmb250LXNpemU6MTJweCI+Q3VtdWxhdGl2ZSB1bml0czwvYj48c3BhbiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpIj4gXHUwMGI3ICcrcmMuZGFpbHkubGVuZ3RoKycgZGF5czwvc3Bhbj4nK3NwYXJrU3ZnKHJjLmRhaWx5KTt9CiAgICBlbHNlIGN2LnN0eWxlLmRpc3BsYXk9Im5vbmUiOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+XHUyNmEwICcrZS5tZXNzYWdlKyc8L3NwYW4+Jzt9KTsKfQp2YXIgUlBMcnVubmluZz1mYWxzZSxSUExzdG9wPWZhbHNlOwpmdW5jdGlvbiBycGxZZWFyKCl7cmV0dXJuIHBhcnNlSW50KGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwteWVhciIpLnZhbHVlKXx8bmV3IERhdGUoKS5nZXRGdWxsWWVhcigpO30KZnVuY3Rpb24gcnBsQnVkZ2V0KCl7cmV0dXJuIE1hdGgubWF4KDEscGFyc2VJbnQoZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC1idWRnZXQiKS52YWx1ZSl8fDIwMDAwKTt9CmZ1bmN0aW9uIHJwbExvZyhzLGFwcGVuZCl7dmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtbG9nIik7ZWwuc3R5bGUuZGlzcGxheT0iYmxvY2siO2lmKGFwcGVuZCllbC50ZXh0Q29udGVudCs9IlxuIitzO2Vsc2UgZWwudGV4dENvbnRlbnQ9cztlbC5zY3JvbGxUb3A9ZWwuc2Nyb2xsSGVpZ2h0O30KZnVuY3Rpb24gcnBsQnVzeShvbil7UlBMcnVubmluZz1vbjtbInJwbC1wbGFuIiwicnBsLWluZ2VzdCIsInJwbC1yZXN1bHRzIiwicnBsLXJ1biIsInJwbC1yZXBvcnQiXS5mb3JFYWNoKGZ1bmN0aW9uKGlkKXtkb2N1bWVudC5nZXRFbGVtZW50QnlJZChpZCkuZGlzYWJsZWQ9b247fSk7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC1zdG9wIikuc3R5bGUuZGlzcGxheT1vbj8iaW5saW5lLWZsZXgiOiJub25lIjt9CmZ1bmN0aW9uIHJwbFN0b3BGbigpe1JQTHN0b3A9dHJ1ZTtycGxMb2coIlN0b3BwaW5nIGFmdGVyIGN1cnJlbnQgcmVxdWVzdFx1MjAyNiIsdHJ1ZSk7fQpmdW5jdGlvbiBycGxUb2dnbGVDc3YoKXt2YXIgdz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLWNzdndyYXAiKTt3LnN0eWxlLmRpc3BsYXk9dy5zdHlsZS5kaXNwbGF5PT09Im5vbmUiPyJibG9jayI6Im5vbmUiO30KZnVuY3Rpb24gcnBsUGxhbigpewogIHZhciB5PXJwbFllYXIoKSxidWQ9cnBsQnVkZ2V0KCk7cnBsTG9nKCJQbGFubmluZyAiK3krIlx1MjAyNiIpOwogIGZldGNoKCIvYXBpL3JlcGxheS9wbGFuP3llYXI9Iit5KyImYnVkZ2V0PSIrYnVkKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGopewogICAgaWYoIWoub2spcmV0dXJuIHJwbExvZygiUGxhbiBlcnJvcjogIisoai5lcnJvcnx8Ij8iKSk7CiAgICB2YXIgZml0cz1qLmZpdHM9PT10cnVlPyJcdTI3MTMgZml0cyI6KGouZml0cz09PWZhbHNlPyJcdTI3MTcgZXhjZWVkcyBxdW90YSI6InF1b3RhIHVua25vd24gXHUyMDE0IG9wZW4gR2FtZXMgb25jZSB0byByZWFkIGl0Iik7CiAgICBycGxMb2coeSsiOiAgIitqLmZyb20rIiBcdTIxOTIgIitqLnRvKyJcbiIrai5kYXlzKyIgZGF5cyBcdTAwZDcgIitqLnNuYXBzUGVyRGF5KyIgc25hcHMgXHUwMGQ3ICIrai5jb3N0UGVyQ2FsbCsiL2NhbGwgPSAiK2ouY3JlZGl0c05lZWRlZCsiIGNyIChmdWxsIHNlYXNvbilcbnF1b3RhICIrKGoucXVvdGFSZW1haW5pbmchPW51bGw/ai5xdW90YVJlbWFpbmluZzoiPyIpKyIgKHNhZmV0eSAiK2ouc2FmZXR5KyIpICBcdTAwYjcgICIrZml0cysiXG5idWRnZXQgIitidWQrIiBjciBcdTIxOTIgfiIrKGouZGF5c0FmZm9yZGFibGUhPW51bGw/ai5kYXlzQWZmb3JkYWJsZToiPyIpKyIgZGF5cyBwZXIgcnVuIik7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7cnBsTG9nKCJQbGFuIGZhaWxlZDogIitlLm1lc3NhZ2UpO30pOwp9CmZ1bmN0aW9uIHJwbFJlc3VsdHMoKXsKICB2YXIgeT1ycGxZZWFyKCksY3N2PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtY3N2IikudmFsdWUudHJpbSgpOwogIHJwbExvZyhjc3Y/IkxvYWRpbmcgbWFudWFsIENTVlx1MjAyNiI6IkZldGNoaW5nIFRvcnZpayByZXN1bHRzXHUyMDI2Iik7CiAgZmV0Y2goIi9hcGkvcmVwbGF5L3Jlc3VsdHMiLHttZXRob2Q6IlBPU1QiLGhlYWRlcnM6eyJDb250ZW50LVR5cGUiOiJhcHBsaWNhdGlvbi9qc29uIn0sYm9keTpKU09OLnN0cmluZ2lmeShjc3Y/e3llYXI6eSxjc3Y6Y3N2fTp7eWVhcjp5fSl9KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGopewogICAgaWYoIWoub2spcmV0dXJuIHJwbExvZygiUmVzdWx0cyBlcnJvcjogIisoai5lcnJvcnx8Ij8iKSx0cnVlKTsKICAgIHJwbExvZygiXHUyNzEzIFJlc3VsdHMgbG9hZGVkOiAiK2ouZ2FtZXMrIiBnYW1lcyAoIisoai5kZXR8fGoubW9kZSkrIikiKyhqLnNhbXBsZT8iIFx1MjAxNCBlLmcuICIrai5zYW1wbGUuaG9tZSsiICIrai5zYW1wbGUuaFB0cysiLCAiK2ouc2FtcGxlLmF3YXkrIiAiK2ouc2FtcGxlLmFQdHM6IiIpLHRydWUpO3JwbFN0YXR1cygpOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3JwbExvZygiUmVzdWx0cyBmYWlsZWQ6ICIrZS5tZXNzYWdlLHRydWUpO30pOwp9CmZ1bmN0aW9uIHJwbExvb3Aoa2luZCl7CiAgaWYoUlBMcnVubmluZylyZXR1cm47CiAgdmFyIHk9cnBsWWVhcigpO1JQTHN0b3A9ZmFsc2U7cnBsQnVzeSh0cnVlKTsKICB2YXIgZXA9Ii9hcGkvcmVwbGF5LyIra2luZCxpdGVyPTAsdDA9RGF0ZS5ub3coKSxwcmV2TmV4dD1udWxsOwogIHZhciBidWRnZXQ9a2luZD09PSJpbmdlc3QiP3JwbEJ1ZGdldCgpOjAsc2Vzc1N0YXJ0PW51bGwsc2Vzc1NwZW50PTA7CiAgcnBsTG9nKChraW5kPT09ImluZ2VzdCI/IkluZ2VzdGluZyAiOiJTaW11bGF0aW5nICIpK3krKGJ1ZGdldD8oIiBcdTAwYjcgYnVkZ2V0ICIrYnVkZ2V0KyIgY3IiKToiIikrIlx1MjAyNiIpOwogIGZ1bmN0aW9uIHN0ZXAoKXsKICAgIGlmKFJQTHN0b3Ape3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNWEwIFN0b3BwZWQgYWZ0ZXIgIitpdGVyKyIgYmF0Y2goZXMpIisoa2luZD09PSJpbmdlc3QiPygiLCB+IitzZXNzU3BlbnQrIiBjciBzcGVudCIpOiIiKSsiLiIsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgIGl0ZXIrKzsKICAgIHZhciBib2R5PWtpbmQ9PT0iaW5nZXN0Ij97eWVhcjp5LGRheXM6MTUsbWF4Q3JlZGl0czpNYXRoLm1heCgxLGJ1ZGdldC1zZXNzU3BlbnQpfTp7eWVhcjp5LGRheXM6MzAscmVzdGFydDppdGVyPT09MX07CiAgICBmZXRjaChlcCx7bWV0aG9kOiJQT1NUIixoZWFkZXJzOnsiQ29udGVudC1UeXBlIjoiYXBwbGljYXRpb24vanNvbiJ9LGJvZHk6SlNPTi5zdHJpbmdpZnkoYm9keSl9KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGopewogICAgICBpZighai5vayYmai5wcm9jZXNzZWREYXlzPT1udWxsKXtycGxCdXN5KGZhbHNlKTtycGxMb2coIkVycm9yOiAiKyhqLmVycm9yfHwiPyIpLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICAgIHZhciBzZWNzPU1hdGgucm91bmQoKERhdGUubm93KCktdDApLzEwMDApOwogICAgICBpZihraW5kPT09ImluZ2VzdCImJmoucXVvdGEpewogICAgICAgIGlmKHNlc3NTdGFydD09bnVsbCYmai5xdW90YS5yZW1haW5pbmchPW51bGwpc2Vzc1N0YXJ0PWoucXVvdGEucmVtYWluaW5nKyhqLnJlYWxTcGVudCE9bnVsbD9qLnJlYWxTcGVudDooai5jcmVkaXRzVXNlZHx8MCkpOwogICAgICAgIHNlc3NTcGVudD0oc2Vzc1N0YXJ0IT1udWxsJiZqLnF1b3RhLnJlbWFpbmluZyE9bnVsbCk/KHNlc3NTdGFydC1qLnF1b3RhLnJlbWFpbmluZyk6KHNlc3NTcGVudCsoai5jcmVkaXRzVXNlZHx8MCkpOwogICAgICB9CiAgICAgIGlmKCFqLmRvbmUmJnByZXZOZXh0IT09bnVsbCYmai5uZXh0RGF0ZT09PXByZXZOZXh0KXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjZhMCBTdG9wcGVkOiBubyBmb3J3YXJkIHByb2dyZXNzIGF0ICIrai5uZXh0RGF0ZSsiIChjdXJzb3Igbm90IGFkdmFuY2luZyBcdTIwMTQgY2hlY2sgUmVkaXMpLiIsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgICAgcHJldk5leHQ9ai5uZXh0RGF0ZTsKICAgICAgaWYoa2luZD09PSJpbmdlc3QiKXsKICAgICAgICBycGxMb2coIlx1MDBiNyAiK2oubmV4dERhdGUrIiAgICh+IitzZXNzU3BlbnQrIiBjciB0aGlzIHJ1biwgIisoai50b3RhbENyZWRpdHMhPW51bGw/ai50b3RhbENyZWRpdHMrIiB0b3RhbCI6Ij8iKSsiLCBiYXRjaCAiK2l0ZXIrIikiLHRydWUpOwogICAgICAgIGlmKGouaGFsdGVkKXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjZhMCBIYWx0ZWQ6ICIrai5oYWx0ZWQsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgICAgICBpZihqLmRvbmUpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNzEzIEluZ2VzdCBjb21wbGV0ZSB0aHJvdWdoICIrai5uZXh0RGF0ZSsiICBcdTIwMTQgICIrc2VjcysicywgfiIrc2Vzc1NwZW50KyIgY3IiLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICAgICAgaWYoc2Vzc1NwZW50Pj1idWRnZXQpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNWEwIEJ1ZGdldCByZWFjaGVkICh+IitzZXNzU3BlbnQrIi8iK2J1ZGdldCsiIGNyKS4gVGFwIEluZ2VzdCBhZ2FpbiB0byByZXN1bWUgZnJvbSAiK2oubmV4dERhdGUrIi4iLHRydWUpO3JwbFN0YXR1cygpO3JldHVybjt9CiAgICAgIH1lbHNlewogICAgICAgIHJwbExvZygiXHUwMGI3ICIrai5uZXh0RGF0ZSsiICAgKCIrai5zaW1tZWQrIiBzaW1tZWQsIGJhdGNoICIraXRlcisiKSIsdHJ1ZSk7CiAgICAgICAgaWYoai5kb25lKXtycGxCdXN5KGZhbHNlKTt2YXIgc21zZz0iXHUyNzEzIFNpbSBjb21wbGV0ZSB0aHJvdWdoICIrai5uZXh0RGF0ZSsiICgiK2ouc2ltbWVkKyIgZ2FtZXMiKyhqLnJlc3VsdERhdGVTaGlmdD8iLCAiK2oucmVzdWx0RGF0ZVNoaWZ0KyIgZGF0ZS1hbGlnbmVkIjoiIikrIikgIFx1MjAxNCAgIitzZWNzKyJzIjtpZihqLnNpbW1lZD09PTApe3Ntc2crPSJcbiAgIGRpYWc6ICIrKGoubGluZUdhbWVzfHwwKSsiIGxpbmUtZ2FtZXMgXHUwMGI3ICIrKGoucmF0aW5nc01pc3NpbmdEYXlzfHwwKSsiIGRheXMgdy9vIHJhdGluZ3MgXHUwMGI3ICIrKGoudW5tYXRjaGVkUmF0aW5nc3x8MCkrIiBvZGRzLXRlYW1zIHVubWF0Y2hlZCBcdTAwYjcgIisoai51bm1hdGNoZWRSZXN1bHRzfHwwKSsiIHJlc3VsdHMgdW5tYXRjaGVkIFx1MDBiNyAiKyhqLnJlc3VsdERhdGVTaGlmdHx8MCkrIiBkYXRlLXNoaWZ0ZWQiO2lmKGoudW5tYXRjaGVkU2FtcGxlJiZqLnVubWF0Y2hlZFNhbXBsZVswXSlzbXNnKz0iXG4gICBlLmcuIHdhbnQgWyIrai51bm1hdGNoZWRTYW1wbGVbMF0ud2FudCsiXSBcdTIwMTQgcmVzdWx0cyBuZWFyYnk6IFsiKyhqLnVubWF0Y2hlZFNhbXBsZVswXS5oYXZlfHxbXSkuam9pbigiXSBbIikrIl0iO31ycGxMb2coc21zZyx0cnVlKTtycGxTdGF0dXMoKTtycGxSZXBvcnQoZmFsc2UpO3JldHVybjt9CiAgICAgIH0KICAgICAgc3RlcCgpOwogICAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7cnBsQnVzeShmYWxzZSk7cnBsTG9nKCJSZXF1ZXN0IGZhaWxlZDogIitlLm1lc3NhZ2UsdHJ1ZSk7fSk7CiAgfQogIHN0ZXAoKTsKfQpmdW5jdGlvbiBycGxTdGF0dXMoKXsKICB2YXIgeT1ycGxZZWFyKCk7CiAgZmV0Y2goIi9hcGkvcmVwbGF5L3N0YXR1cz95ZWFyPSIreSkudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSkudGhlbihmdW5jdGlvbihycyl7CiAgICB2YXIgZWw9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC1zdGF0dXMiKTsKICAgIGlmKHJzJiZycy5jdXJzb3IpewogICAgICBlbC5pbm5lckhUTUw9J0luZ2VzdCA8c3BhbiBjbGFzcz0ibW9ubyI+JysocnMuY3Vyc29yLmluZ2VzdE5leHR8fHJzLmN1cnNvci5mcm9tKSsnPC9zcGFuPicrKHJzLmN1cnNvci5kb25lPycgKGRvbmUpJzonJykrKHJzLmN1cnNvci5jcmVkaXRzPygnIFx1MDBiNyAnK3JzLmN1cnNvci5jcmVkaXRzKycgY3IgdXNlZCcpOicnKSsocnMucmVzdWx0cz8oJyBcdTAwYjcgcmVzdWx0cyAnK3JzLnJlc3VsdHMuZ2FtZXMrJyAoJytycy5yZXN1bHRzLm1vZGUrJyknKTonIFx1MDBiNyA8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tYW1iZXIpIj5yZXN1bHRzIG5vdCBsb2FkZWQ8L3NwYW4+JykrJyBcdTAwYjcgc2ltICcrKHJzLmN1cnNvci5zaW1OZXh0Pyc8c3BhbiBjbGFzcz0ibW9ubyI+Jytycy5jdXJzb3Iuc2ltTmV4dCsnPC9zcGFuPic6J25vdCBzdGFydGVkJyk7CiAgICB9IGVsc2UgZWwuaW5uZXJIVE1MPSc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj5Ob3Qgc3RhcnRlZCBcdTIwMTQgUGxhbiB0byBzaXplIHRoZSBzcGVuZCwgdGhlbiBJbmdlc3QgXHUyMTkyIFJlc3VsdHMgXHUyMTkyIFJ1bi48L3NwYW4+JzsKICB9KS5jYXRjaChmdW5jdGlvbigpe30pOwp9CmZ1bmN0aW9uIHJwbFJlcG9ydCh0b0xvZyl7CiAgdmFyIHk9cnBsWWVhcigpOwogIGZldGNoKCIvYXBpL3JlcGxheS9yZXBvcnQ/eWVhcj0iK3kpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24ocnApewogICAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtcmVwb3J0Iik7CiAgICBpZihycCYmcnAub2spewogICAgICB2YXIgQT1ycC5waWNrcy5BTEwscmVjPXJwLnJlY29tbWVuZHx8e307CiAgICAgIGVsLmlubmVySFRNTD0nPGRpdiBzdHlsZT0iYm9yZGVyLXRvcDoxcHggc29saWQgdmFyKC0tYm9yZGVyKTttYXJnaW4tdG9wOjdweDtwYWRkaW5nLXRvcDo3cHgiPicrcnAueWVhcisnIFx1MDBiNyAnK3JwLmNvdmVyYWdlLnNpbW1lZCsnIHNpbW1lZCBcdTAwYjcgcGlja3MgPGI+JytBLnJlY29yZCsnPC9iPiAoJysoQS51bml0cz4wPyIrIjoiIikrQS51bml0cysndSwgUk9JICcrKEEucm9pIT1udWxsPyhBLnJvaSoxMDApLnRvRml4ZWQoMSkrJyUnOidcdTIwMTQnKSsnKSBcdTAwYjcgQ0xWIGJlYXQgJysoQS5jbHZCZWF0IT1udWxsPyhBLmNsdkJlYXQqMTAwKS50b0ZpeGVkKDApKyclJzonXHUyMDE0JykrCiAgICAgICAgJzxicj5tYXJnaW4gU0QgPGI+JysocnAucmVzaWR1YWxzLm1hcmdpbj9ycC5yZXNpZHVhbHMubWFyZ2luLnNkOidcdTIwMTQnKSsnPC9iPiBcdTAwYjcgdG90YWxzIGJpYXMgPGI+JysocmVjLnRvdGFsc0JpYXMhPW51bGw/KChyZWMudG90YWxzQmlhcz4wPyIrIjoiIikrcmVjLnRvdGFsc0JpYXMpOidcdTIwMTQnKSsnPC9iPiBcdTAwYjcgSENBIGltcGxpZWQgPGI+JysocmVjLkhDQV9pbXBsaWVkIT1udWxsP3JlYy5IQ0FfaW1wbGllZDonXHUyMDE0JykrJzwvYj4nKwogICAgICAgIChycC5ibGVuZEZpdCYmcnAuYmxlbmRGaXQuc3ByZWFkPyc8YnI+YmxlbmQgZml0IChUb3J2aWsgd2VpZ2h0IHRoZSBjbG9zZSBhZG9wdHMpOiBzcHJlYWQgPGI+JysocnAuYmxlbmRGaXQuc3ByZWFkLnchPW51bGw/cnAuYmxlbmRGaXQuc3ByZWFkLnc6J1x1MjAxNCcpKyc8L2I+IFx1MDBiNyB0b3RhbCA8Yj4nKyhycC5ibGVuZEZpdC50b3RhbC53IT1udWxsP3JwLmJsZW5kRml0LnRvdGFsLnc6J1x1MjAxNCcpKyc8L2I+IFx1MDBiNyBsaXZlIHNldHRpbmcgJytycC5ibGVuZEZpdC5jdXJyZW50OicnKSsKICAgICAgICAnPGJyPjxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPkZ1bGwgSlNPTjogPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvcmVwbGF5L3JlcG9ydD95ZWFyPScrcnAueWVhcisnPC9zcGFuPiBcdTAwYjcgcmVjb21tZW5kYXRpb25zIGRpc3BsYXktb25seTwvc3Bhbj48L2Rpdj4nOwogICAgICBpZih0b0xvZyl7CiAgICAgICAgdmFyIHN3PXJwLnN3ZWVwfHx7fTsKICAgICAgICBycGxMb2coIlJlcG9ydCAiK3JwLnllYXIrIjpcbiAgcGlja3MgIitBLnJlY29yZCsiICAiKyhBLnVuaXRzPjA/IisiOiIiKStBLnVuaXRzKyJ1ICBST0kgIisoQS5yb2khPW51bGw/KEEucm9pKjEwMCkudG9GaXhlZCgxKSsiJSI6Ilx1MjAxNCIpKyIgIENMViBiZWF0ICIrKEEuY2x2QmVhdCE9bnVsbD8oQS5jbHZCZWF0KjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKwogICAgICAgICAgIlxuICBieSBlZGdlOiAiK1siMi00IiwiNC02IiwiNi04IiwiOCsiXS5tYXAoZnVuY3Rpb24oayl7dmFyIHM9c3dba118fHt9O3JldHVybiBrKyIgIisocy5yb2khPW51bGw/KHMucm9pKjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKyIoIisocy5ufHwwKSsiKSI7fSkuam9pbigiICAiKSsKICAgICAgICAgICJcbiAgcmVzaWQgU0QgbWFyZ2luICIrKHJwLnJlc2lkdWFscy5tYXJnaW4/cnAucmVzaWR1YWxzLm1hcmdpbi5zZDoiXHUyMDE0IikrIiB0b3RhbCAiKyhycC5yZXNpZHVhbHMudG90YWw/cnAucmVzaWR1YWxzLnRvdGFsLnNkOiJcdTIwMTQiKSsiICBCcmllciAiKyhycC5jYWxpYnJhdGlvbj9ycC5jYWxpYnJhdGlvbi5icmllcjoiXHUyMDE0IikrCiAgICAgICAgICAiXG4gIHJlYzogU0QgIityZWMuU0QrIiAgVE9UX1NEICIrcmVjLlRPVF9TRCsiICB0b3RhbHNCaWFzICIrcmVjLnRvdGFsc0JpYXMrIiAgSENBICIrcmVjLkhDQV9pbXBsaWVkKwogICAgICAgICAgKHJwLmJsZW5kRml0PyJcbiAgYmxlbmQgZml0OiBzcHJlYWQgdyAiK3JwLmJsZW5kRml0LnNwcmVhZC53KyIgKCIrcnAuYmxlbmRGaXQuc3ByZWFkLm4rIikgIHRvdGFsIHcgIitycC5ibGVuZEZpdC50b3RhbC53KyIgKCIrcnAuYmxlbmRGaXQudG90YWwubisiKSAgbGl2ZSAiK3JwLmJsZW5kRml0LmN1cnJlbnQ6IiIpKTsKICAgICAgfQogICAgfSBlbHNlIHsgZWwuaW5uZXJIVE1MPScnOyBpZih0b0xvZylycGxMb2coIk5vIHJlcG9ydCB5ZXQgXHUyMDE0IGluZ2VzdCwgbG9hZCByZXN1bHRzLCB0aGVuIHJ1bi4iLHRydWUpOyB9CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7aWYodG9Mb2cpcnBsTG9nKCJSZXBvcnQgZmFpbGVkOiAiK2UubWVzc2FnZSx0cnVlKTt9KTsKfQpmdW5jdGlvbiBsb2FkQWxsKGZvcmNlKXtsb2FkU2xhdGUoZm9yY2UpO30KbG9hZEFsbCh0cnVlKTsKc2V0SW50ZXJ2YWwoZnVuY3Rpb24oKXtsb2FkU2xhdGUoZmFsc2UpO30sMTgwMDAwKTsKZnVuY3Rpb24gdHZUb2dnbGVJbXBvcnQoKXt2YXIgdz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0d3JhcCIpO2lmKHcpe3ZhciBvcGVuPXcuc3R5bGUuZGlzcGxheT09PSJub25lIjt3LnN0eWxlLmRpc3BsYXk9b3Blbj8iYmxvY2siOiJub25lIjtpZihvcGVuKXt0dlNlYXNvbkxpbmsoKTt0dlRtTGlua3MoKTt0dlRtQ292ZXJhZ2UoKTt9fX0KZnVuY3Rpb24gdHZTZWFzb25MaW5rKCl7dmFyIGE9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LWxpbmstc2Vhc29uIik7aWYoYSlhLmhyZWY9Imh0dHBzOi8vYmFydHRvcnZpay5jb20vIitycGxZZWFyKCkrIl90ZWFtX3Jlc3VsdHMuanNvbiI7fQpmdW5jdGlvbiB0dlRtTGlua3MoKXt2YXIgeT1ycGxZZWFyKCksd3JhcD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1saW5rcyIpO2lmKCF3cmFwKXJldHVybjt2YXIgb3V0PVtdLGQ9bmV3IERhdGUoRGF0ZS5VVEMoeS0xLDEwLDgpKSxlbmQ9bmV3IERhdGUoRGF0ZS5VVEMoeSwyLDIyKSk7d2hpbGUoZDw9ZW5kKXt2YXIgZHM9ZC50b0lTT1N0cmluZygpLnNsaWNlKDAsMTApLHltZD1kcy5yZXBsYWNlKC8tL2csIiIpO291dC5wdXNoKCc8YSBocmVmPSJodHRwczovL2JhcnR0b3J2aWsuY29tL3RpbWVtYWNoaW5lL3RlYW1fcmVzdWx0cy8nK3ltZCsnX3RlYW1fcmVzdWx0cy5qc29uLmd6IiB0YXJnZXQ9Il9ibGFuayIgcmVsPSJub29wZW5lciIgY2xhc3M9ImNoaXAiIHN0eWxlPSJ0ZXh0LWRlY29yYXRpb246bm9uZTtmb250LXNpemU6MTFweDtwYWRkaW5nOjRweCA4cHgiPicrZHMuc2xpY2UoNSkrJzwvYT4nKTtkPW5ldyBEYXRlKGQuZ2V0VGltZSgpKzE0Kjg2NGU1KTt9d3JhcC5pbm5lckhUTUw9b3V0LmpvaW4oIiIpO30KZnVuY3Rpb24gdHZVcGxvYWQoKXsKICB2YXIgaW5wPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1maWxlcyIpLGxvZz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0bG9nIiksYnRuPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di11cGJ0biIpOwogIHZhciBmaWxlcz1pbnAmJmlucC5maWxlcz9pbnAuZmlsZXM6W107CiAgaWYoIWZpbGVzLmxlbmd0aCl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iUGljayB0aGUgZG93bmxvYWRlZCAuZ3ogZmlsZXMgZmlyc3QuIjtyZXR1cm47fQogIGlmKGJ0bilidG4uZGlzYWJsZWQ9dHJ1ZTtpZihsb2cpbG9nLnRleHRDb250ZW50PSJSZWFkaW5nICIrZmlsZXMubGVuZ3RoKyIgZmlsZShzKVx1MjAyNiI7CiAgdmFyIGFycj1bXSxkb25lPTAsdG90YWw9ZmlsZXMubGVuZ3RoOwogIGZ1bmN0aW9uIGZpbigpe2RvbmUrKztpZihkb25lIT09dG90YWwpcmV0dXJuO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlVwbG9hZGluZyAiK2Fyci5sZW5ndGgrIiBmaWxlKHMpXHUyMDI2IjsKICAgIGZldGNoKCIvYXBpL2FkbWluL3RvcnZpay90bXVwbG9hZCIse21ldGhvZDoiUE9TVCIsaGVhZGVyczp7IkNvbnRlbnQtVHlwZSI6ImFwcGxpY2F0aW9uL2pzb24ifSxib2R5OkpTT04uc3RyaW5naWZ5KHt5ZWFyOnJwbFllYXIoKSxmaWxlczphcnJ9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICAgIGlmKGJ0bilidG4uZGlzYWJsZWQ9ZmFsc2U7CiAgICAgIGlmKGxvZyl7bG9nLnRleHRDb250ZW50PShqLm9rPyJcdTI3MTMgU3RvcmVkICIrai5zdG9yZWQrIiBzbmFwc2hvdChzKSI6Ilx1MjcxNyAwIHN0b3JlZCIpKyhqLmZhaWxlZD8iLCAiK2ouZmFpbGVkKyIgZmFpbGVkIjoiIikrIi4gQ292ZXJhZ2U6ICIrKGouY292ZXJhZ2U/ai5jb3ZlcmFnZS5jb3VudDowKSsiICgiKygoai5jb3ZlcmFnZSYmai5jb3ZlcmFnZS5mcm9tKXx8IiIpKyJcdTIwMTMiKygoai5jb3ZlcmFnZSYmai5jb3ZlcmFnZS50byl8fCIiKSsiKS4iO3ZhciB0cD1qLnN0b3JlZERldGFpbCYmai5zdG9yZWREZXRhaWxbMF0mJmouc3RvcmVkRGV0YWlsWzBdLnRvcDtpZih0cClsb2cudGV4dENvbnRlbnQrPSJcbnBhcnNlZCBlLmcuICIrdHAudGVhbSsiIFx1MjAxNCBPRSAiKygrdHAuYWRqb2UpLnRvRml4ZWQoMSkrIiAvIERFICIrKCt0cC5hZGpkZSkudG9GaXhlZCgxKSsiIC8gdGVtcG8gIisoK3RwLmFkanQpLnRvRml4ZWQoMSk7aWYoai5mYWlsZWQmJmouZmFpbGVkRGV0YWlsJiZqLmZhaWxlZERldGFpbFswXSlsb2cudGV4dENvbnRlbnQrPSJcbiIrai5mYWlsZWREZXRhaWxbMF0ubmFtZSsiOiAiK2ouZmFpbGVkRGV0YWlsWzBdLmVycm9yO30KICAgICAgdHZUbUNvdmVyYWdlKCk7CiAgICB9KS5jYXRjaChmdW5jdGlvbihlKXtpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9Ilx1MjcxNyAiK2UubWVzc2FnZTt9KTt9CiAgZm9yKHZhciBpPTA7aTxmaWxlcy5sZW5ndGg7aSsrKXsoZnVuY3Rpb24oZmlsZSl7dmFyIHJkPW5ldyBGaWxlUmVhZGVyKCk7cmQub25sb2FkPWZ1bmN0aW9uKCl7dmFyIHM9U3RyaW5nKHJkLnJlc3VsdCk7YXJyLnB1c2goe25hbWU6ZmlsZS5uYW1lLGI2NDpzLmluZGV4T2YoIiwiKT49MD9zLnNwbGl0KCIsIilbMV06c30pO2ZpbigpO307cmQub25lcnJvcj1mdW5jdGlvbigpe2ZpbigpO307cmQucmVhZEFzRGF0YVVSTChmaWxlKTt9KShmaWxlc1tpXSk7fQp9CmZ1bmN0aW9uIHR2VG1Db3ZlcmFnZSgpe3ZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1jb3YiKTtpZighZWwpcmV0dXJuO2ZldGNoKCIvYXBpL3JlcGxheS90bT95ZWFyPSIrcnBsWWVhcigpKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGope2VsLnRleHRDb250ZW50PShqLm9rJiZqLmNvdW50KT8oIlN0b3JlZDogIitqLmNvdW50KyIgc25hcHNob3RzLCAiKyhqLmZyb218fCIiKSsiXHUyMDEzIisoai50b3x8IiIpKyIuIik6Ik5vIGRhdGVkIHNuYXBzaG90cyB5ZXQuIjt9KS5jYXRjaChmdW5jdGlvbigpe30pO30KZnVuY3Rpb24gdHZJbXBvcnRUbSgpewogIHZhciB0YT1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0IiksbG9nPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1pbXBvcnRsb2ciKSxidG49ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LXRtYnRuIik7CiAgdmFyIGRhdGE9dGE/dGEudmFsdWUudHJpbSgpOiIiLGR0PShkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtdG1kYXRlIil8fHt9KS52YWx1ZSx5PXJwbFllYXIoKTsKICBpZighZGF0YSl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iUGFzdGUgdGhlIHJhdGluZ3MgYWJvdmUgZmlyc3QuIjtyZXR1cm47fQogIGlmKCFkdCl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iRW50ZXIgdGhlIGRhdGUgdGhlc2UgcmF0aW5ncyByZWZsZWN0IChZWVlZLU1NLUREKS4iO3JldHVybjt9CiAgaWYoYnRuKWJ0bi5kaXNhYmxlZD10cnVlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlN0b3JpbmcgZGF0ZWQgc25hcHNob3RcdTIwMjYiOwogIGZldGNoKCIvYXBpL2FkbWluL3RvcnZpay90bSIse21ldGhvZDoiUE9TVCIsaGVhZGVyczp7IkNvbnRlbnQtVHlwZSI6ImFwcGxpY2F0aW9uL2pzb24ifSxib2R5OkpTT04uc3RyaW5naWZ5KHt5ZWFyOnksZGF0ZTpkdCxkYXRhOmRhdGF9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICBpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlOwogICAgaWYoai5vayl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzEzIFN0b3JlZCAiKyhqLnN0b3JlZERldGFpbFswXT9qLnN0b3JlZERldGFpbFswXS50ZWFtczoiPyIpKyIgdGVhbXMgYXQgIitkdCsiLiBDb3ZlcmFnZTogIitqLmNvdmVyYWdlLmNvdW50KyIgc25hcHNob3RzICgiKyhqLmNvdmVyYWdlLmZyb218fCIiKSsiXHUyMDEzIisoai5jb3ZlcmFnZS50b3x8IiIpKyIpLiI7dHZUbUNvdmVyYWdlKCk7fQogICAgZWxzZSBpZihsb2cpbG9nLnRleHRDb250ZW50PSJcdTI3MTcgIisoai5lcnJvcnx8KGouZmFpbGVkRGV0YWlsJiZqLmZhaWxlZERldGFpbFswXSYmai5mYWlsZWREZXRhaWxbMF0uZXJyb3IpfHwic3RvcmUgZmFpbGVkIik7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7aWYoYnRuKWJ0bi5kaXNhYmxlZD1mYWxzZTtpZihsb2cpbG9nLnRleHRDb250ZW50PSJcdTI3MTcgIitlLm1lc3NhZ2U7fSk7Cn0KZnVuY3Rpb24gdHZJbXBvcnQoKXsKICB2YXIgdGE9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInR2LWltcG9ydCIpLGxvZz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidHYtaW1wb3J0bG9nIiksYnRuPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0di1pbXBvcnRidG4iKTsKICB2YXIgZGF0YT10YT90YS52YWx1ZS50cmltKCk6IiIseT1ycGxZZWFyKCk7CiAgaWYoIWRhdGEpe2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IlBhc3RlIHRoZSBDU1Ygb3IgSlNPTiBmaXJzdC4iO3JldHVybjt9CiAgaWYoYnRuKWJ0bi5kaXNhYmxlZD10cnVlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9IkltcG9ydGluZ1x1MjAyNiI7CiAgZmV0Y2goIi9hcGkvYWRtaW4vdG9ydmlrIix7bWV0aG9kOiJQT1NUIixoZWFkZXJzOnsiQ29udGVudC1UeXBlIjoiYXBwbGljYXRpb24vanNvbiJ9LGJvZHk6SlNPTi5zdHJpbmdpZnkoe2RhdGE6ZGF0YSx5ZWFyOnl9KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICBpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlOwogICAgaWYoai5vayl7aWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzEzIExvYWRlZCAiK2oudGVhbXMrIiB0ZWFtcyAoIitqLm1vZGUrIiwgIitqLnllYXIrIikuIFRvcDogIisoai50b3AzfHxbXSkubWFwKGZ1bmN0aW9uKHQpe3JldHVybiB0LnRlYW07fSkuam9pbigiLCAiKTtsb2FkRGF0YSgpO30KICAgIGVsc2UgaWYobG9nKWxvZy50ZXh0Q29udGVudD0iXHUyNzE3ICIrKGouZXJyb3J8fCJpbXBvcnQgZmFpbGVkIikrKGouc2FtcGxlPyJcbnNhbXBsZSByb3c6ICIrSlNPTi5zdHJpbmdpZnkoai5zYW1wbGVbMF0pOiIiKTsKICB9KS5jYXRjaChmdW5jdGlvbihlKXtpZihidG4pYnRuLmRpc2FibGVkPWZhbHNlO2lmKGxvZylsb2cudGV4dENvbnRlbnQ9Ilx1MjcxNyAiK2UubWVzc2FnZTt9KTsKfQo8L3NjcmlwdD4KPC9ib2R5Pgo8L2h0bWw+Cg==", "base64").toString("utf8");
// v1.4.1 home-screen icon (orange #e85d2f, white H) + web-app manifest for "Add to Home Screen"
const ICON_180 = Buffer.from("iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAD+ElEQVR42u3dP4/bdBzA4e/Xdi7J5e6KurEhxIjoUrExAGIDJhi7IDbExotghhfBwIKEmBBIINgqMdCVSmwdUMVV1+aixP4x5DoVJJw6ukvueXSrYyf5+Gc75z/54M6tgH9T+QgQB+JAHIgDcSAOxIE4EAfiAHEgDsSBOBAH4kAciANxIA4QB+JAHIgDcSAOxIE4EAfiAHEgDsSBOBAH4kAciANxIA7EAeJAHIgDcXApmt1YzLqOyE0mLF103dbWrCpys7WrRNuKYwildKcPI0rPyTKi5Gick8MoZfilyizzx2W5WM+o78TV7HjTsMTx9AuIrs3J7Pj9j7MZ9U0qMpf3753f/SEPplG6YceMsphPbr89euW19Yz6Ldpq+eT7r8qTs6jrrYR7XUaOrsvx9OjDTzebev7zN/Nfv8vxYZShh43F+fj2W9M3P9hwwX75tjs7zbo2cjzvZqWcPcrpYb91tG2jrsv8cd/VutdmJdrVeka9xrNyPh94JLvuO6R103MAz6jrqLa5Xa+qqJuLGfWJI672gOFQFnEgDsSBOBAH4kAciANxgDgQB+JAHIgDcSAOxIE4EAfiAHEgDsSBOLgczf6/xcyLv8FfUxy7rXSxWsZqFd1q0JctsVruxPWu4vjvNXw0qU5u5tEL0Q16s5S6riLyYCKO3VTXETF5473x6+/kFjYBpZSLOHbkqmhxPDNyNAfZHGzlle2Q7sVux9ZunbPv+6TX42iFjfidA3EgDsSBOBAH4kAciANxcH3t/fkcZYtnXWS137/N73scmZG1MUAcz4wZmasHfy7/+D2b0cD/m80sq+Xo5VebF1/a4Hkr4rhsXRd1vfjtp9MvPqtObg58mmDddKcPb3zyefPuR+sZiWMHtyqjgzy6kbOTwU8TzLbN0cF+f3rXYIe0ay/+howuomuv8hO4HMoiDsSBOBAH4kAciAPEgTgQB+JAHIgDcSAOxIE4QByIA3EgDsSBOBAH4kAcXAc7cq1s20a76nezg7aNKNFt83k5XRft6mJG/9P6LbStOAaSmUcnvaeqm4jI6WxblzuXktNZ1M16Rv3e0Ow4shLH82/3qrKYn339ZTajvl9eZC7v38vxZPg+SsnxZHH3x+7vvza4eUtZLcv8LKurflePfHDn1lXvo5Tu8aMeQ/fTtxZRcjTOyeFWBo/Mcv6kLBfrGfWduNqFwWM3NivVjZsbPhupdNva7Sglp7M8PN5s4p3Y7didHdIrqOsi9vkBkQ5lEQfiQByIA3EgDsSBOBAH4gBxIA7EgTgQB+JAHIgDcSAOEAfiQByIA3EgDsSBOBAH4gBxIA7EgTgQB+JAHIgDcSAOxAHiQByIA3FwOf4BX30EXfECwHwAAAAASUVORK5CYII=", "base64");
const ICON_192 = Buffer.from("iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAD+0lEQVR42u3dy4ocVRzA4f+pS3cGMahhTMiEgOLGVVa6N0R8AAVBzVuISze+gsuAG925cqUvk0VgcEhwYHSuXZfjokdwmeqZGrq6v4/Zds3pPr+uCzTnpIOnjwJWVfgIEBACQkAICASEgBAQAgIBISAEhIBAQAgIASEgEBACQkAICAGBgBAQAkJAICAEhIAQEAgIASEgBAQCQkAICAEhIBAQAkJACAgEhIAQEAICASEg1lM1sfGmFCmt/vKcI+dtH+H2BpRSbhbRLFY/Ql2nej7iDKWUFxfRNqsfYDaPqp5QQ9WU6mmb6t0H5b2HkSPS8G92St2r/fbgRRpphpYjfPBBeefuSiOMSNHuP+8PX0ZVTaWh6QRUFPn8ZP7xp29+9e3Kxzj97dnRTz+kt3aja0cIqMjnJ2989vXOky9XPsbRs+/Pfv851W9H7gR0/VMUbRN9H30XRTnspX0bRZWbxZVuUF5jhLlZrDrCLooy2nb4uUtAg25RiyIiRzHw+TEXURQj1/O/EebhI1y+qZSmNSEe4xEQAkJACAgEhIAQEAICASEgBISAQEAICAEhIBAQAkJACAgBgYAQEAJCQCAgBMS6q7br7S5XPkjF8JUPXufLWExxdQQBDdEs8ulxnu2Msj5QUebT46ssTyagdb5WlxFx65PP6w8/GmsNuRTRteX99y7PRgLatItXRLm7V+7u3di/E9DGyTlyP+YSYDnSdt0Gbd9NdCoDj/EICAEhIB8BAkJACAgBgYAQEAJiK1Rb945vYMtLAW2yLZtgAV3r2adtorkYsaEcUc9SVQto43RtlNXZH7/88+uPxe13RvpJa398dPub73YefxFdF2UpoI07A52ddH/9mbt2rID+Psznpy5hG/zQWablJWaMq1hRpnq2Pb+G3s6b6Bz5v78xnu+ms9/7tX1rPEcgIASEgBAQCAgBISAEBAJCQAgIAYGAEBACQkAgIASEgBAQAgIBISAEhIBAQAgIAbHJprY6R87R99EP3zQu99H3N7F6xnKEuY9+4AiXb2pq63tMK6AcVX25OfLgU+0sIlI9G3mG8uUSQauMsIiIqKqIKTWUDp4+mshIU26banevvPcw8vBdK3OOlLpX++3BizTWprspt011//3yzt2VRhiRot1/3h++jKqayqloOgEtZ6hZRLNY/Qh1ner5iHOTUl5cXGXn7zSbj7WptEtY5JzqWczmV7pBGXVuck6zecxvre8I3USv++e7ZQvdeYxHQAgIASEgEBACQkAICASEgBAQAgIBISAEhIBAQAgIASEgBAQCQkAICAGBgBAQAkJAICAEhIAQEAgIASEgBISAQEAICAEhIBAQAkJACAgEhIBYU/8CPYYLC36XwxYAAAAASUVORK5CYII=", "base64");
const ICON_512 = Buffer.from("iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAIAAAB7GkOtAAAIM0lEQVR42u3bvYpkRRiA4e8753RPT8+MjLqBBpoomLmRiUaCmCyYiImwmamBd+IFeANuIhi7grmRipGKwQrLIC4O87c9faoMZkTDxUXmdNfz0Bdwuqq63qqennx493YA0J7OEAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAT2owBNuY9S5yE9I+jhHVdEXfR+TUH7LWKKO5EgCmLbOendT1KiInvr12y4PohtYbUGv5849pD0JG1OxnudyPKtgCwHQ/ql2sLhZv3Zm9/FrUGjnpc+XZ/Xvl0VEMs0a3lcwoYy72Dt77KIfZpM/+mePRg/NvvojZXAMEgAkf/1ePF2/eWbzxzvQf9uLbr8fff8th3uwloJbSLZb7H3w8/Ue9/Pn7s68+z/mOAAgA027A2UmM6yhjdP2kz5VlvQHfff//41BPj3OxnO6NrYzR9fX0eOIXSgSAiIjouuiHyJx6AOz+V/o++mG6AbhaSFNeS/znrcIQAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAADdjMATcqPz75b2DANCOWqOW61ebAWj3vSMAtL76ZjnMcpg1uglmXg2ChYAA0Nz2d/jJp3G5iuwiaqt3oIi+z53lPz0AAaAF/fMvGgQQANo8/9Z2z/7/ugo5+yMANLj1+Q0M3CT/BwAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAADy1wRBwY8oYtTY/Chl9by0gALR2/7TxgQDQpPP798ZHRznMGr0HZNYydou95bsfxjCzHhAAmlHr6ZefrX76Lhd7UcdGA7C+7J97Yfft968rmGldIAC0sQHuH3aHt3JnGbU0G4DumWft+wgA7SljjOsY180GIMZ1jKOFwE3xM1AAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAAATAEAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgDA0xoMwRaqNUqJUiJy0g/J9VCUKCVqjZzkfF0tJPMlAGzEdpLznei66CZ/vUsX0IjMXOxNeii6LiJyvjBXW7j6Ht69bRS2aTeJ9Xp46dXu8FbUSV8AosblLz/U89Po+ohWT5e15mw+e+X16LvpzleNyCgnx+tff4x+cBUQACbdgLq6iPV6A550sesSELXWx2cbUMC+z/luu6neUr4C2sZD5Xw3djbhUUsxXZGZy4NNWFcR1XwJABvwWS0OaptECLkh/goHIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAIACGAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQDgif0FTJTwnlTsqiMAAAAASUVORK5CYII=", "base64");
const sendPng = buf => (q, r) => { r.set("Cache-Control", "public, max-age=604800"); r.type("png").send(buf); };
app.get(["/apple-touch-icon.png", "/apple-touch-icon-precomposed.png"], sendPng(ICON_180));
app.get("/icon-192.png", sendPng(ICON_192));
app.get(["/icon-512.png", "/favicon.ico"], sendPng(ICON_512));
app.get("/manifest.webmanifest", (q, r) => r.type("application/manifest+json").send(JSON.stringify({
  name: "HOOPSBET", short_name: "HOOPSBET", start_url: "/", display: "standalone",
  background_color: "#0a1430", theme_color: "#0a1430",
  icons: [{ src: "/icon-192.png", sizes: "192x192", type: "image/png" }, { src: "/icon-512.png", sizes: "512x512", type: "image/png" }]
})));
app.get("/", (q, r) => r.type("html").send(DASH));

// ═══ BOOT ═════════════════════════════════════════════════════════════════════
(async () => {
  try {
    const [al, nu, mc, lk, tk, ls] = await Promise.all([rGet("hb:aliases"), rGet("hb:neutral"), rGet("hb:model"), rGet("hb:torvik:lock"), rGet("hb:tracker"), rGet("hb:lastseen")]);
    const J = v => { try { return typeof v === "string" ? JSON.parse(v) : v; } catch (e) { return null; } };
    if (al) ALIASES = Object.assign({}, ALIAS_SEED, J(al) || {});
    if (nu) NEUTRAL = J(nu) || {};
    if (mc) { const c = J(mc); if (c && c.thresholds) {
      if (!c.blend) { delete c.thresholds; console.log("v1.5.0: saved pre-1.5 thresholds dropped (edges are now market-anchored)"); }
      ["blend", "mlBand", "neutral", "evTrack", "alerts", "live", "earlySeason"].forEach(k => { if (c[k] && CFG[k] && typeof c[k] === "object") c[k] = Object.assign({}, CFG[k], c[k]); });
      CFG = Object.assign(CFG, c); } }
    if (lk) TORVIK_LOCK = J(lk);
    if (tk) { const t = J(tk); if (t && Array.isArray(t.picks)) TRACKER = t; }
    if (ls) { const l = J(ls); if (l && typeof l === "object") LASTSEEN = l; }
    if (!CFG.live) CFG.live = { enabled: true, baseMin: 30, preTipMin: 12, discoverMin: 180, gradeMin: 30 }; // saved config predates v1.4.0
  } catch (e) {}
  // v1.4.0: the scheduler — first tick a minute after boot, then every 5 minutes
  setTimeout(() => { liveCycle().catch(() => {}); }, 60e3);
  setInterval(() => { liveCycle().catch(() => {}); }, 5 * 60e3);
  fetchTorvik().catch(() => {});
  app.listen(PORT, "0.0.0.0", () => console.log("HOOPSBET v" + VERSION + " listening on " + PORT + " | season year " + seasonYear()));
})();
