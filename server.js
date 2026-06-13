// ═══════════════════════════════════════════════════════════════════════════
// HOOPSBET v1.3 (REWIND) — NCAA Basketball sides & totals analytics
// S1: chassis + market layer (The Odds API, sole odds source)
// S2: Torvik-fed efficiency model (AdjOE/AdjDE/AdjT) + Models surface
// S3: picks engine · fractional Kelly · Redis tracker · CLV grading
// S4: Pinnacle-anchored +EV screen (line-match gated) · record polish
// S5: lookahead-free replay — Odds API historical snapshots + Torvik Time
//     Machine ratings-as-of-date; picks sim at open, CLV vs close;
//     calibration report (residual SDs, HCA, totals bias) — recommend only
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
app.use(express.json());

const PORT = process.env.PORT || 3000;
const ODDS_KEY = process.env.ODDS_API_KEY || "";
const REDIS_URL = process.env.UPSTASH_REDIS_URL || "";
const REDIS_TOKEN = process.env.UPSTASH_REDIS_TOKEN || "";

const VERSION = "1.3.1";
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
    lagDays: 0, safetyCredits: 500, fetchDelayMs: 250 },
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
    const r = await fetch(REDIS_URL + "/" + cmd.map(encodeURIComponent).join("/"), { headers: { Authorization: "Bearer " + REDIS_TOKEN } });
    if (!r.ok) return null;
    return (await r.json()).result;
  } catch (e) { return null; }
}
const rGet = k => rCmd(["GET", k]);
const rSet = (k, v) => rCmd(["SET", k, typeof v === "string" ? v : JSON.stringify(v)]);

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
let OPENS = {}; let opensDirty = false;
function slateTtlMs() { const h = new Date().getUTCHours(); return (h >= 14 || h <= 5) ? 10 * 60e3 : 30 * 60e3; } // ~10am–1am ET active

async function getSlate(force) {
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
  ["csv", "json"].forEach(m => { if (!strategies.includes(m)) strategies.push(m); });
  for (const mode of strategies) {
    try {
      const url = "https://barttorvik.com/trank.php?year=" + year + (mode === "csv" ? "&csv=1" : "&json=1");
      const r = await fetch(url, { headers: { "User-Agent": "hoopsbet/1.0 (personal analytics)" } });
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
function replayCostFor(days, snaps) { return days * snaps * 30; }
function quotaAllows(cost) { return QUOTA.remaining == null || QUOTA.remaining >= cost + (CFG.replay.safetyCredits || 0); }

async function fetchHistoricalSnap(iso) {
  if (!quotaAllows(30)) throw new Error("quota guard: " + QUOTA.remaining + " remaining < 30 + safety " + CFG.replay.safetyCredits);
  const url = ODDS_HOST + "/v4/historical/sports/" + SPORT + "/odds?apiKey=" + ODDS_KEY +
    "&bookmakers=" + BOOKS.join(",") + "&markets=" + MARKETS + "&oddsFormat=american&dateFormat=iso&date=" + encodeURIComponent(iso);
  const r = await fetch(url);
  captureQuota(r);
  if (!r.ok) { let m = "historical HTTP " + r.status; try { const j = await r.json(); if (j.message) m += " — " + j.message; } catch (e) {} throw new Error(m); }
  const j = await r.json();
  return { ts: j.timestamp || iso, events: j.data || [] };
}

const monthKey = (y, d) => "hb:replay:lines:" + y + ":" + d.slice(5, 7);
async function ingestDays(body) {
  const year = +body.year;
  let cur = await rGetJ("hb:replay:cursor:" + year) || {};
  const from = body.from || cur.from || (year - 1) + "-11-04";
  const to = body.to || cur.to || year + "-04-08";
  const times = (body.snapTimes && Array.isArray(body.snapTimes)) ? body.snapTimes : (cur.snapTimes || CFG.replay.snapTimes);
  let d = cur.ingestNext || from;
  const maxDays = Math.min(15, Math.max(1, body.days || 5));
  const months = {}; let processed = 0, credits = 0, halted = null;
  while (d <= to && processed < maxDays) {
    for (const iso of snapIsosFor(d, times)) {
      if (!quotaAllows(30)) { halted = "quota guard at " + QUOTA.remaining; break; }
      let snap;
      try { snap = await fetchHistoricalSnap(iso); } catch (e) { halted = e.message; break; }
      credits += 30;
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
      await sleep(CFG.replay.fetchDelayMs || 250);
    }
    if (halted) break;
    processed++; d = addDaysStr(d, 1);
  }
  for (const mk of Object.keys(months)) await rSet(mk, months[mk]);
  cur = Object.assign(cur, { year, from, to, snapTimes: times, ingestNext: d, ingestedDays: (cur.ingestedDays || 0) + processed, credits: (cur.credits || 0) + credits });
  await rSet("hb:replay:cursor:" + year, cur);
  return { ok: !halted || processed > 0, processedDays: processed, nextDate: d, done: d > to, halted, creditsUsed: credits, totalCredits: cur.credits, quota: QUOTA };
}

const TM_CACHE = new Map();
async function timeMachineRatings(dateStr, year) {
  const eff = addDaysStr(dateStr, -(CFG.replay.lagDays || 0));
  if (TM_CACHE.has(eff)) return TM_CACHE.get(eff);
  const ymd = eff.replace(/-/g, "");
  let out = null;
  for (const url of ["https://barttorvik.com/timemachine/team_results/" + ymd + "_team_results.json.gz",
                     "https://barttorvik.com/timemachine/team_results/" + ymd + "_team_results.json"]) {
    try {
      const r = await fetch(url, { headers: { "User-Agent": "hoopsbet/1.3 (personal analytics)" } });
      if (!r.ok) continue;
      const buf = await r.buffer();
      const payload = /\.gz$/.test(url) ? gunzipJson(buf) : JSON.parse(buf.toString("utf8"));
      const arr = Array.isArray(payload) ? payload : (payload.data || []);
      if (!arr.length) continue;
      const pa = ratingsFromArray(arr, null);
      if (!pa.colmap) continue;
      const built = buildTorvik(pa.rows, pa.colmap, year, "tm:" + eff);
      if (built) { out = built; break; }
    } catch (e) {}
  }
  if (TM_CACHE.size > 4) TM_CACHE.delete(TM_CACHE.keys().next().value);
  TM_CACHE.set(eff, out);
  await sleep(CFG.replay.fetchDelayMs || 250);
  return out;
}

// ── results adapters ──
function parseResultsCsvManual(text) {
  const rows = parseCsv(text);
  if (!rows.length) return null;
  const hd = rows[0].map(x => String(x).toLowerCase().replace(/[^a-z_]/g, ""));
  const ix = n => hd.indexOf(n);
  const m = { d: ix("date"), away: ix("away"), home: ix("home"), aPts: ix("away_pts") >= 0 ? ix("away_pts") : ix("awaypts"), hPts: ix("home_pts") >= 0 ? ix("home_pts") : ix("homepts"), neutral: ix("neutral") };
  if (m.d < 0 || m.away < 0 || m.home < 0 || m.aPts < 0 || m.hPts < 0) return null;
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
async function fetchTorvikGames(year) {
  for (const mode of ["csv", "json"]) {
    try {
      const url = "https://barttorvik.com/getgamestats.php?year=" + year + (mode === "csv" ? "&csv=1" : "&json=1");
      const r = await fetch(url, { headers: { "User-Agent": "hoopsbet/1.3 (personal analytics)" } });
      if (!r.ok) continue;
      let rows;
      if (mode === "csv") rows = parseCsv(await r.text());
      else { const j = await r.json(); const arr = Array.isArray(j) ? j : (j.data || []); rows = arr.length && !Array.isArray(arr[0]) ? arr.map(o => Object.values(o)) : arr; }
      if (!rows || rows.length < 100) continue;
      let det = detectGamesColumns(rows), data = rows;
      if (!det) { det = detectGamesColumns(rows.slice(1)); data = rows.slice(1); }
      if (!det) continue;
      const games = normalizeGameRows(data, det);
      if (games.length < 100) continue;
      await rSet("hb:replay:games:" + year, { games, det, mode, fetchedAt: Date.now(), sample: rows.slice(0, 2) });
      return { ok: true, games: games.length, mode, det };
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
    days: 0, lineGames: 0, simmed: 0, unmatchedRatings: {}, unmatchedResults: 0, ratingsMissingDays: 0, noPreTip: 0, sameSnap: 0,
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
function simDate(dateStr, tm, resultRows, dayLines, agg) {
  agg.days++;
  const resMap = {};
  (resultRows || []).forEach(g => { resMap[normName(g.home) + "|" + normName(g.away)] = g; });
  Object.keys(dayLines || {}).forEach(id => {
    const rec = dayLines[id]; rec.id = id;
    agg.lineGames++;
    const rH = resolveTeam(rec.h, tm.byTeam), rA = resolveTeam(rec.a, tm.byTeam);
    if (!rH || !rA) { agg.unmatchedRatings[!rH ? rec.h : rec.a] = 1; return; }
    let res = resMap[normName(rH.team) + "|" + normName(rA.team)], swapped = false;
    if (!res) { res = resMap[normName(rA.team) + "|" + normName(rH.team)]; swapped = !!res; }
    if (!res) { agg.unmatchedResults++; return; }
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
  let agg = await rGetJ("hb:replay:agg:" + year) || newAgg(year);
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
      else simDate(d, tm, byDate[d], dayLines, agg);
    }
    processed++; d = addDaysStr(d, 1);
    if (processed % 5 === 0) { await rSet("hb:replay:agg:" + year, agg); cur.simNext = d; await rSet("hb:replay:cursor:" + year, cur); }
  }
  cur.simNext = d;
  await rSet("hb:replay:agg:" + year, agg);
  await rSet("hb:replay:cursor:" + year, cur);
  return { ok: true, processedDays: processed, nextDate: d, done: d > end, simmed: agg.simmed, days: agg.days };
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
  r.json({
    ok: true, app: "hoopsbet", version: VERSION,
    quota: QUOTA, oddsKey: !!ODDS_KEY, lastOddsError: LAST_ODDS_ERR,
    slateAgeMin: slateCache.t ? Math.round((Date.now() - slateCache.t) / 60e3) : null,
    torvik: TORVIK ? { year: TORVIK.year, teams: TORVIK.teams, mode: TORVIK.mode, ageMin: Math.round((Date.now() - TORVIK.fetchedAt) / 60e3) } : { error: TORVIK_ERR || "not loaded" },
    tracker: { picks: TRACKER.picks.length, open: TRACKER.picks.filter(p => p.status === "open").length },
    redis: !!(REDIS_URL && REDIS_TOKEN)
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
    r.json(Object.assign({ ok: true, generatedAt: slateCache.t, thresholds: CFG.thresholds, quota: QUOTA, note: (!games.length && (month() >= 5 && month() <= 9)) ? OFFSEASON_NOTE : undefined }, asm));
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
    ["lagDays", "safetyCredits", "fetchDelayMs"].forEach(k => { if (typeof b.replay[k] === "number") CFG.replay[k] = b.replay[k]; });
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
      note: (!games.length && (month() >= 5 && month() <= 9)) ? OFFSEASON_NOTE : undefined }, computeEv(games, asm)));
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
  r.json({ ok: true, year, from, to, days, snapsPerDay: snaps, creditsNeeded: credits,
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
      return r.json({ ok: true, games: games.length, mode: "manual" });
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

const DASH = Buffer.from("PCFET0NUWVBFIGh0bWw+CjxodG1sIGxhbmc9ImVuIj4KPGhlYWQ+CjxtZXRhIGNoYXJzZXQ9IlVURi04Ij4KPG1ldGEgbmFtZT0idmlld3BvcnQiIGNvbnRlbnQ9IndpZHRoPWRldmljZS13aWR0aCwgaW5pdGlhbC1zY2FsZT0xLjAsIG1heGltdW0tc2NhbGU9MS4wLCB1c2VyLXNjYWxhYmxlPW5vIj4KPHRpdGxlPkhPT1BTQkVUIOKAlCBOQ0FBIEJhc2tldGJhbGw8L3RpdGxlPgo8bGluayBocmVmPSJodHRwczovL2ZvbnRzLmdvb2dsZWFwaXMuY29tL2NzczI/ZmFtaWx5PU91dGZpdDp3Z2h0QDMwMDs0MDA7NTAwOzYwMDs3MDA7ODAwOzkwMCZmYW1pbHk9SmV0QnJhaW5zK01vbm86d2dodEA0MDA7NTAwOzYwMDs3MDA7ODAwJmRpc3BsYXk9c3dhcCIgcmVsPSJzdHlsZXNoZWV0Ij4KPHN0eWxlPgo6cm9vdHstLWJnOiMwYTE0MzA7LS1jYXJkOiMwZjIxNDc7LS1ib3JkZXI6IzIyNDI3ZjstLXRleHQ6I2Y1ZjhmZDstLWRpbTojYWViZmRhOy0tbXV0ZWQ6IzdhOTBiNTstLWFjY2VudDojMmY2ZmUwOy0tYWNjZW50VGV4dDojNmI5N2VlOy0tZ3JlZW46IzE4Yjg3YzstLXJlZDojZTEyZTQ0Oy0tcmVkVGV4dDojZjA1NTZiOy0tYW1iZXI6I2UwYTIzYTstLXB1cnBsZTojNmY5ZWZmOy0tY2FyZDI6IzBjMWEzYX0KKnttYXJnaW46MDtwYWRkaW5nOjA7Ym94LXNpemluZzpib3JkZXItYm94Oy13ZWJraXQtdGFwLWhpZ2hsaWdodC1jb2xvcjp0cmFuc3BhcmVudH0KaHRtbHstd2Via2l0LXRleHQtc2l6ZS1hZGp1c3Q6MTAwJX0KYm9keXtiYWNrZ3JvdW5kOnZhcigtLWJnKTtjb2xvcjp2YXIoLS10ZXh0KTtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3BhZGRpbmc6MTJweCAxNHB4IDEyMHB4O21heC13aWR0aDoxMTAwcHg7bWFyZ2luOjAgYXV0b30KLm1vbm97Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9CmJ1dHRvbjpmb2N1cy12aXNpYmxlLHNlbGVjdDpmb2N1cy12aXNpYmxlLGlucHV0OmZvY3VzLXZpc2libGUsYTpmb2N1cy12aXNpYmxle291dGxpbmU6MnB4IHNvbGlkIHZhcigtLWFjY2VudFRleHQpO291dGxpbmUtb2Zmc2V0OjJweH0KLmhkcntkaXNwbGF5OmZsZXg7YWxpZ24taXRlbXM6Y2VudGVyO2p1c3RpZnktY29udGVudDpzcGFjZS1iZXR3ZWVuO2dhcDo4cHg7bWFyZ2luLWJvdHRvbToxMnB4fQouYnJhbmR7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtnYXA6OXB4fQoubG9nb3t3aWR0aDozNHB4O2hlaWdodDozNHB4O2JvcmRlci1yYWRpdXM6OXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDEzNWRlZywjZTg1ZDJmLHZhcigtLWFjY2VudCkpO2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OmNlbnRlcjtmb250LXdlaWdodDo5MDA7Zm9udC1zaXplOjE2cHh9Ci5idHtmb250LXNpemU6MTVweDtmb250LXdlaWdodDo4MDB9LmJ0IHNwYW57Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ic3Vie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKX0KLmhkci1idG57cGFkZGluZzo4cHggMTRweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo4cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1hY2NlbnQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xKTtjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZn0KLmNhcmR7YmFja2dyb3VuZDpsaW5lYXItZ3JhZGllbnQoMTgwZGVnLHZhcigtLWNhcmQpLHZhcigtLWNhcmQyKSk7Ym9yZGVyOjFweCBzb2xpZCB0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjEwcHg7Ym94LXNoYWRvdzppbnNldCAwIDFweCAwIHJnYmEoMjU1LDI1NSwyNTUsLjA0KSwwIDRweCAxMnB4IHJnYmEoMCwwLDAsLjMyKTtwYWRkaW5nOjExcHggMTJweDttYXJnaW4tYm90dG9tOjhweH0KLnN0cmlwe2Rpc3BsYXk6ZmxleDtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwO21hcmdpbi1ib3R0b206MTBweH0KLmtwaXtmbGV4OjE7bWluLXdpZHRoOjEwNXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO3BhZGRpbmc6OXB4IDExcHh9Ci5rcGkgLmxie2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLW11dGVkKTt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bGV0dGVyLXNwYWNpbmc6LjRweDtmb250LXdlaWdodDo3MDB9Ci5rcGkgLnZ7Zm9udC1zaXplOjE3cHg7Zm9udC13ZWlnaHQ6ODAwO21hcmdpbi10b3A6MnB4fQoua3BpIC5ze2ZvbnQtc2l6ZToxMHB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDoxcHh9Ci5mYmFye2Rpc3BsYXk6ZmxleDtnYXA6NnB4O2ZsZXgtd3JhcDp3cmFwO2FsaWduLWl0ZW1zOmNlbnRlcjttYXJnaW4tYm90dG9tOjEwcHh9Ci5jaGlwe3BhZGRpbmc6NnB4IDEzcHg7bWluLWhlaWdodDo0NHB4O2JvcmRlci1yYWRpdXM6OHB4O2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtiYWNrZ3JvdW5kOnRyYW5zcGFyZW50O2NvbG9yOnZhcigtLW11dGVkKTtmb250LXNpemU6MTFweDtmb250LXdlaWdodDo3MDA7Y3Vyc29yOnBvaW50ZXI7Zm9udC1mYW1pbHk6J091dGZpdCcsc2Fucy1zZXJpZjtkaXNwbGF5OmlubGluZS1mbGV4O2FsaWduLWl0ZW1zOmNlbnRlcn0KLmNoaXAub257Ym9yZGVyLWNvbG9yOnZhcigtLWFjY2VudFRleHQpO2JhY2tncm91bmQ6cmdiYSg0NywxMTEsMjI0LC4xMik7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9CnNlbGVjdC5jaGlwe2FwcGVhcmFuY2U6bm9uZTtwYWRkaW5nLXJpZ2h0OjI2cHg7YmFja2dyb3VuZC1pbWFnZTpsaW5lYXItZ3JhZGllbnQoNDVkZWcsdHJhbnNwYXJlbnQgNTAlLHZhcigtLW11dGVkKSA1MCUpLGxpbmVhci1ncmFkaWVudCgxMzVkZWcsdmFyKC0tbXV0ZWQpIDUwJSx0cmFuc3BhcmVudCA1MCUpO2JhY2tncm91bmQtcG9zaXRpb246Y2FsYygxMDAlIC0gMTRweCkgNTAlLGNhbGMoMTAwJSAtIDlweCkgNTAlO2JhY2tncm91bmQtc2l6ZTo1cHggNXB4O2JhY2tncm91bmQtcmVwZWF0Om5vLXJlcGVhdH0KLmdjYXJke2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6MTBweDtib3gtc2hhZG93Omluc2V0IDAgMXB4IDAgcmdiYSgyNTUsMjU1LDI1NSwuMDQpLDAgNHB4IDEycHggcmdiYSgwLDAsMCwuMzIpO21hcmdpbi1ib3R0b206OHB4O3BhZGRpbmc6MTFweCAxMnB4fQouZy10b3B7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwfQouZy10ZWFtc3tmb250LXNpemU6MTNweDtmb250LXdlaWdodDo4MDA7bWluLXdpZHRoOjB9Ci5nLXRlYW1zIC5ya3tjb2xvcjp2YXIoLS1hY2NlbnRUZXh0KTtmb250LXNpemU6MTBweDtmb250LXdlaWdodDo4MDA7bWFyZ2luLXJpZ2h0OjJweH0KLmctdGVhbXMgLmF0e2NvbG9yOnZhcigtLW11dGVkKTtmb250LXdlaWdodDo2MDA7bWFyZ2luOjAgNXB4fQouZy1tZXRhe2Rpc3BsYXk6ZmxleDtnYXA6NXB4O2FsaWduLWl0ZW1zOmNlbnRlcjtmbGV4LXdyYXA6d3JhcH0KLnRhZ3twYWRkaW5nOjJweCA3cHg7Ym9yZGVyLXJhZGl1czo1cHg7Zm9udC1zaXplOjEwcHg7Zm9udC13ZWlnaHQ6ODAwO2xldHRlci1zcGFjaW5nOi4zcHh9Ci50YWctdGltZXtiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA1KTtjb2xvcjp2YXIoLS1kaW0pO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKX0KLnRhZy1ue2JhY2tncm91bmQ6cmdiYSgxMTEsMTU4LDI1NSwuMTIpO2NvbG9yOnZhcigtLXB1cnBsZSk7Ym9yZGVyOjFweCBzb2xpZCByZ2JhKDExMSwxNTgsMjU1LC4zKX0KLnRhZy1ia3tiYWNrZ3JvdW5kOnJnYmEoMjU1LDI1NSwyNTUsLjA0KTtjb2xvcjp2YXIoLS1tdXRlZCk7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQouYXdhaXR7ZGlzcGxheTppbmxpbmUtYmxvY2s7cGFkZGluZzoycHggOHB4O2JvcmRlci1yYWRpdXM6NXB4O2JhY2tncm91bmQ6cmdiYSgyMjQsMTYyLDU4LC4xKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjI0LDE2Miw1OCwuMyk7Y29sb3I6dmFyKC0tYW1iZXIpO2ZvbnQtc2l6ZToxMHB4O2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvantkaXNwbGF5OmZsZXg7Z2FwOjE0cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKX0KLmctcHJvaiBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjcwMH0KLmctcHJvaiAubW9ub3tmb250LXNpemU6MTJweH0KLmctZWRnZXN7ZGlzcGxheTpmbGV4O2dhcDo2cHg7ZmxleC13cmFwOndyYXA7bWFyZ2luLXRvcDo5cHh9Ci5lZHtwYWRkaW5nOjVweCAxMHB4O2JvcmRlci1yYWRpdXM6N3B4O2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjgwMDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtib3JkZXI6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7Y29sb3I6dmFyKC0tbXV0ZWQpO2JhY2tncm91bmQ6cmdiYSgyNTUsMjU1LDI1NSwuMDIpfQouZWQuaG90e2JvcmRlci1jb2xvcjpyZ2JhKDI0LDE4NCwxMjQsLjQ1KTtiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMSk7Y29sb3I6dmFyKC0tZ3JlZW4pfQouZWQgLnNke2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7Zm9udC13ZWlnaHQ6NzAwO2ZvbnQtc2l6ZToxMHB4O21hcmdpbi1yaWdodDo0cHg7Y29sb3I6aW5oZXJpdDtvcGFjaXR5Oi44NX0KLmctc2hhcnB7bWFyZ2luLXRvcDo4cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQouZy1zaGFycCBie2NvbG9yOnZhcigtLXB1cnBsZSk7Zm9udC13ZWlnaHQ6NzAwfQouZW1wdHl7cGFkZGluZzoyNnB4IDE4cHg7Ym9yZGVyOjFweCBkYXNoZWQgdmFyKC0tYm9yZGVyKTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEycHg7bGluZS1oZWlnaHQ6MS42NTt0ZXh0LWFsaWduOmNlbnRlcjtjb2xvcjp2YXIoLS1tdXRlZCl9Ci5lbXB0eSBie2NvbG9yOnZhcigtLXRleHQpfQoubW9yZXt3aWR0aDoxMDAlO3BhZGRpbmc6MTFweDttaW4taGVpZ2h0OjQ0cHg7Ym9yZGVyLXJhZGl1czo5cHg7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2JhY2tncm91bmQ6dHJhbnNwYXJlbnQ7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO2ZvbnQtZmFtaWx5OidPdXRmaXQnLHNhbnMtc2VyaWY7bWFyZ2luOjJweCAwIDEwcHh9Ci5zZWMtaGR7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2NvbG9yOnZhcigtLWRpbSk7bGV0dGVyLXNwYWNpbmc6LjNweDt0ZXh0LXRyYW5zZm9ybTp1cHBlcmNhc2U7bWFyZ2luOjE0cHggMCA4cHh9Ci5zcm93e2Rpc3BsYXk6ZmxleDthbGlnbi1pdGVtczpjZW50ZXI7anVzdGlmeS1jb250ZW50OnNwYWNlLWJldHdlZW47Z2FwOjhweDtwYWRkaW5nOjlweCAxMXB4O2JhY2tncm91bmQ6bGluZWFyLWdyYWRpZW50KDE4MGRlZyx2YXIoLS1jYXJkKSx2YXIoLS1jYXJkMikpO2JvcmRlci1yYWRpdXM6OXB4O2JveC1zaGFkb3c6aW5zZXQgMCAxcHggMCByZ2JhKDI1NSwyNTUsMjU1LC4wNCksMCAzcHggMTBweCByZ2JhKDAsMCwwLC4zKTttYXJnaW4tYm90dG9tOjZweH0KLnNyb3cgLnR7Zm9udC1zaXplOjEycHg7Zm9udC13ZWlnaHQ6NzAwfQouc3JvdyAuc2N7Zm9udC1zaXplOjEzcHg7Zm9udC13ZWlnaHQ6ODAwO2ZvbnQtZmFtaWx5OidKZXRCcmFpbnMgTW9ubycsbW9ub3NwYWNlfQouc3JvdyAuc3R7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpfQoubGl2ZS1kb3R7Y29sb3I6dmFyKC0tZ3JlZW4pO2ZvbnQtd2VpZ2h0OjgwMH0KdGFibGV7d2lkdGg6MTAwJTtib3JkZXItY29sbGFwc2U6Y29sbGFwc2U7Zm9udC1zaXplOjExcHh9CnRoe3RleHQtYWxpZ246bGVmdDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC1zaXplOjEwcHg7dGV4dC10cmFuc2Zvcm06dXBwZXJjYXNlO2xldHRlci1zcGFjaW5nOi40cHg7Zm9udC13ZWlnaHQ6NzAwO3BhZGRpbmc6NXB4IDZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpfQp0ZHtwYWRkaW5nOjZweDtib3JkZXItYm90dG9tOjFweCBzb2xpZCByZ2JhKDM0LDY2LDEyNywuMzUpfQp0ZC5tb25ve2ZvbnQtc2l6ZToxMXB4fQouc3RhdHVze3BhZGRpbmc6MTZweDt0ZXh0LWFsaWduOmNlbnRlcjtmb250LXNpemU6MTJweDtjb2xvcjp2YXIoLS1hbWJlcil9Ci5zcGlue2Rpc3BsYXk6aW5saW5lLWJsb2NrO3dpZHRoOjEzcHg7aGVpZ2h0OjEzcHg7Ym9yZGVyOjJweCBzb2xpZCB2YXIoLS1hbWJlcik7Ym9yZGVyLXRvcC1jb2xvcjp0cmFuc3BhcmVudDtib3JkZXItcmFkaXVzOjUwJTthbmltYXRpb246c3AgLjhzIGxpbmVhciBpbmZpbml0ZTt2ZXJ0aWNhbC1hbGlnbjptaWRkbGU7bWFyZ2luLXJpZ2h0OjVweH0KQGtleWZyYW1lcyBzcHt0b3t0cmFuc2Zvcm06cm90YXRlKDM2MGRlZyl9fQoubm90ZXttYXJnaW4tdG9wOjE0cHg7cGFkZGluZzoxMHB4IDEycHg7YmFja2dyb3VuZDpyZ2JhKDQ3LDExMSwyMjQsLjA0KTtib3JkZXItcmFkaXVzOjEwcHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tZGltKTtsaW5lLWhlaWdodDoxLjU1fQoubm90ZSBie2NvbG9yOnZhcigtLXRleHQpO2ZvbnQtd2VpZ2h0OjYwMH0KLmZvb3Rlcntib3JkZXItdG9wOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO3BhZGRpbmc6MTBweCA0cHggMDttYXJnaW4tdG9wOjE0cHg7Zm9udC1zaXplOjEwcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO3RleHQtYWxpZ246Y2VudGVyfQouc2VjdGlvbntkaXNwbGF5Om5vbmV9LnNlY3Rpb24ub257ZGlzcGxheTpibG9ja30KLmJuYXZ7cG9zaXRpb246Zml4ZWQ7bGVmdDowO3JpZ2h0OjA7Ym90dG9tOjA7ZGlzcGxheTpmbGV4O2JhY2tncm91bmQ6cmdiYSgxMCwxNCwyMywuOTYpO2JhY2tkcm9wLWZpbHRlcjpibHVyKDEwcHgpOy13ZWJraXQtYmFja2Ryb3AtZmlsdGVyOmJsdXIoMTBweCk7Ym9yZGVyLXRvcDoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtwYWRkaW5nOjhweCA0cHggY2FsYyg2cHggKyBlbnYoc2FmZS1hcmVhLWluc2V0LWJvdHRvbSkpO3otaW5kZXg6MTAwfQouYm5hdi1idG57ZmxleDoxO2Rpc3BsYXk6ZmxleDtmbGV4LWRpcmVjdGlvbjpjb2x1bW47YWxpZ24taXRlbXM6Y2VudGVyO2dhcDoycHg7cGFkZGluZzo4cHggNHB4IDZweDtib3JkZXI6bm9uZTtiYWNrZ3JvdW5kOm5vbmU7Y29sb3I6dmFyKC0tbXV0ZWQpO2ZvbnQtc2l6ZToxMXB4O2ZvbnQtd2VpZ2h0OjYwMDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO2N1cnNvcjpwb2ludGVyO21pbi1oZWlnaHQ6NDRweDtqdXN0aWZ5LWNvbnRlbnQ6Y2VudGVyfQouYm5hdi1idG4ub257Y29sb3I6dmFyKC0tYWNjZW50VGV4dCl9Ci5ibmF2LWljbyBzdmd7ZGlzcGxheTpibG9ja30KLnJwbC1pbnt3aWR0aDo2NHB4O2JhY2tncm91bmQ6dmFyKC0tY2FyZDIpO2JvcmRlcjoxcHggc29saWQgdmFyKC0tYm9yZGVyKTtjb2xvcjp2YXIoLS10ZXh0KTtib3JkZXItcmFkaXVzOjZweDtwYWRkaW5nOjZweCA4cHg7Zm9udC1zaXplOjEycHg7Zm9udC1mYW1pbHk6J0pldEJyYWlucyBNb25vJyxtb25vc3BhY2V9Ci5ycGwtdGF7d2lkdGg6MTAwJTttaW4taGVpZ2h0Ojc2cHg7YmFja2dyb3VuZDp2YXIoLS1jYXJkMik7Ym9yZGVyOjFweCBzb2xpZCB2YXIoLS1ib3JkZXIpO2NvbG9yOnZhcigtLXRleHQpO2JvcmRlci1yYWRpdXM6N3B4O3BhZGRpbmc6N3B4IDlweDtmb250LXNpemU6MTFweDtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtyZXNpemU6dmVydGljYWw7bWFyZ2luLXRvcDo2cHh9Ci5ycGwtbGlua3tiYWNrZ3JvdW5kOm5vbmU7Ym9yZGVyOm5vbmU7Y29sb3I6dmFyKC0tYWNjZW50VGV4dCk7Zm9udC1zaXplOjExcHg7Zm9udC13ZWlnaHQ6NzAwO2N1cnNvcjpwb2ludGVyO3BhZGRpbmc6MDtmb250LWZhbWlseTonT3V0Zml0JyxzYW5zLXNlcmlmO3RleHQtZGVjb3JhdGlvbjp1bmRlcmxpbmV9Ci5jaGlwOmRpc2FibGVke29wYWNpdHk6LjQ7Y3Vyc29yOmRlZmF1bHR9CiNycGwtbG9ne2Rpc3BsYXk6bm9uZTtmb250LWZhbWlseTonSmV0QnJhaW5zIE1vbm8nLG1vbm9zcGFjZTtmb250LXNpemU6MTFweDttYXJnaW4tdG9wOjhweDtwYWRkaW5nOjhweCAxMHB4O2JhY2tncm91bmQ6cmdiYSgwLDAsMCwuMjgpO2JvcmRlci1yYWRpdXM6N3B4O2NvbG9yOnZhcigtLWRpbSk7d2hpdGUtc3BhY2U6cHJlLXdyYXA7d29yZC1icmVhazpicmVhay13b3JkO2xpbmUtaGVpZ2h0OjEuNTttYXgtaGVpZ2h0OjIwMHB4O292ZXJmbG93LXk6YXV0b30KPC9zdHlsZT4KPC9oZWFkPgo8Ym9keT4KCjxkaXYgY2xhc3M9ImhkciI+CiAgPGRpdiBjbGFzcz0iYnJhbmQiPgogICAgPGRpdiBjbGFzcz0ibG9nbyI+SDwvZGl2PgogICAgPGRpdj48ZGl2IGNsYXNzPSJidCI+SE9PUFM8c3Bhbj5CRVQ8L3NwYW4+IDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTBweDtjb2xvcjp2YXIoLS1tdXRlZCk7Zm9udC13ZWlnaHQ6NjAwIj52MTwvc3Bhbj48L2Rpdj4KICAgIDxkaXYgY2xhc3M9ImJzdWIiIGlkPSJjb25uIj4mIzk2Nzk7IGNvbm5lY3RpbmcmaGVsbGlwOzwvZGl2PjwvZGl2PgogIDwvZGl2PgogIDxidXR0b24gY2xhc3M9Imhkci1idG4iIG9uY2xpY2s9ImxvYWRBbGwodHJ1ZSkiPiYjODYzNTsgUmVmcmVzaDwvYnV0dG9uPgo8L2Rpdj4KCjwhLS0gR0FNRVMgLS0+CjxkaXYgaWQ9InNlYy1nYW1lcyIgY2xhc3M9InNlY3Rpb24gb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0ia3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8c2VsZWN0IGNsYXNzPSJjaGlwIiBpZD0iZi1jb25mIiBvbmNoYW5nZT0iYXBwbHlGaWx0ZXJzKCkiPjxvcHRpb24gdmFsdWU9IiI+QWxsIGNvbmZlcmVuY2VzPC9vcHRpb24+PC9zZWxlY3Q+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBpZD0iZi10b3AiIG9uY2xpY2s9InRnKHRoaXMsJ3RvcCcpIj5Ub3AgMjU8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJmLWVkZ2UiIG9uY2xpY2s9InRnKHRoaXMsJ2VkZ2UnKSI+RWRnZXMgb25seTwvYnV0dG9uPgogICAgPHNlbGVjdCBjbGFzcz0iY2hpcCIgaWQ9ImYtc29ydCIgb25jaGFuZ2U9ImFwcGx5RmlsdGVycygpIj48b3B0aW9uIHZhbHVlPSJlZGdlIj5Tb3J0OiBFZGdlPC9vcHRpb24+PG9wdGlvbiB2YWx1ZT0idGltZSI+U29ydDogVGlwIHRpbWU8L29wdGlvbj48L3NlbGVjdD4KICA8L2Rpdj4KICA8ZGl2IGNsYXNzPSJmYmFyIiBpZD0ibWluZWRnZSI+CiAgICA8c3BhbiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpO21hcmdpbi1yaWdodDoycHgiPk1pbiBlZGdlPC9zcGFuPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCBvbiIgb25jbGljaz0ibWUoMCx0aGlzKSI+QWxsPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJtZSgyLHRoaXMpIj4yJSs8L2J1dHRvbj4KICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIG9uY2xpY2s9Im1lKDQsdGhpcykiPjQlKzwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0ibWUoNix0aGlzKSI+NiUrPC9idXR0b24+CiAgPC9kaXY+CiAgPGRpdiBpZD0iZ2FtZXMtc3RhdHVzIiBjbGFzcz0ic3RhdHVzIj48c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBMb2FkaW5nIHNsYXRlJmhlbGxpcDs8L2Rpdj4KICA8ZGl2IGlkPSJnYW1lcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ibm90ZSI+PGI+SG93IHRvIHJlYWQ6PC9iPiBwcm9qZWN0aW9ucyBjb21lIGZyb20gdGhlIFRvcnZpay1mZWQgZWZmaWNpZW5jeSBtb2RlbCAoQWRqT0UgJnRpbWVzOyBBZGpERSAmdGltZXM7IHRlbXBvLCBIQ0EtYWRqdXN0ZWQsIHplcm9lZCBvbiBuZXV0cmFsIGZsb29ycykuIEVkZ2UgY2hpcHMgbGlnaHQgdXAgYXQgdGhlIGZsb29yczogTUwgJmdlOyA8YiBpZD0idGgtbWwiPjQ8L2I+JSAmbWlkZG90OyBTUFIgJmdlOyA8YiBpZD0idGgtc3ByIj41PC9iPiUgJm1pZGRvdDsgVE9UICZnZTsgPGIgaWQ9InRoLXRvdCI+NS41PC9iPiUsIGFuZCByZXF1aXJlICZnZTs8YiBpZD0idGgtYmsiPjM8L2I+IGJvb2tzIHBvc3RpbmcgdGhlIG1hcmtldC4gUGlja3MsIHNpemluZywgYW5kIHRyYWNraW5nIGFycml2ZSBpbiBTMyAmbWRhc2g7IHRoaXMgc3VyZmFjZSBpcyBvYnNlcnZhdGlvbmFsLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gRVYgLS0+CjxkaXYgaWQ9InNlYy1ldiIgY2xhc3M9InNlY3Rpb24iPgogIDxkaXYgY2xhc3M9InN0cmlwIiBpZD0iZXYta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iZmJhciI+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBpZD0iZXYtc3RyaWN0IiBvbmNsaWNrPSJldlN0cmljdCh0aGlzKSI+U3Ryb25nIG9ubHk8L2J1dHRvbj4KICAgIDxzcGFuIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1tdXRlZCk7bWFyZ2luLWxlZnQ6NHB4Ij5NaW4gRVY8L3NwYW4+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIG9uIiBvbmNsaWNrPSJldk1pbigwLHRoaXMpIj5GbG9vcjwvYnV0dG9uPgogICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgb25jbGljaz0iZXZNaW4oMyx0aGlzKSI+MyUrPC9idXR0b24+CiAgICA8YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJldk1pbig1LHRoaXMpIj41JSs8L2J1dHRvbj4KICA8L2Rpdj4KICA8ZGl2IGlkPSJldi1hcmJzIj48L2Rpdj4KICA8ZGl2IGlkPSJldi1zdGF0dXMiIGNsYXNzPSJzdGF0dXMiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjwvZGl2PgogIDxkaXYgaWQ9ImV2LXJvd3MiPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPk1ldGhvZDo8L2I+IGZhaXIgcHJvYmFiaWxpdHkgPSBQaW5uYWNsZSBuby12aWcuIEVWJSA9IGZhaXIgJnRpbWVzOyBkZWNpbWFsIG9kZHMgJm1pbnVzOyAxLCBmbG9vciA8YiBpZD0iZXYtZmxvb3IiPjI8L2I+JS4gU3ByZWFkcyBhbmQgdG90YWxzIGFyZSBzY3JlZW5lZCA8Yj5vbmx5IHdoZXJlIGEgcmV0YWlsIGJvb2sgcG9zdHMgdGhlIGV4YWN0IFBpbm5hY2xlIGxpbmU8L2I+ICZtZGFzaDsgbWlzbWF0Y2hlZCBsaW5lcyBhcmUgc2tpcHBlZCwgbmV2ZXIgYXBwcm94aW1hdGVkLiA8Yj5TVFJPTkc8L2I+ID0gdGhlIHByaWNlZCBib29rIGlzICZnZTs8YiBpZD0iZXYtZ2FwIj4yPC9iPiBpbXBsaWVkIHBvaW50cyBiZXR0ZXIgdGhhbiB0aGUgcmVzdCBvZiByZXRhaWwgKHN0YWxlLWxpbmUgc2lnbmFsKTsgPGI+V0VBSzwvYj4gPSBhbGwgb2YgcmV0YWlsIGRpc2FncmVlcyB3aXRoIFBpbm5hY2xlLCB3aGljaCBjYW4gbWVhbiBhbmNob3IgbGFnLiBNb2RlbCBjaGlwcyBhcmUgaW5mb3JtYXRpb25hbCBvbmx5LiBUaGlzIGlzIGEgc2NyZWVuLCBub3QgcGlja3MgJm1kYXNoOyBub3RoaW5nIGhlcmUgZW50ZXJzIHRoZSB0cmFja2VyLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gQkVUUyAtLT4KPGRpdiBpZD0ic2VjLWJldHMiIGNsYXNzPSJzZWN0aW9uIj4KICA8ZGl2IGNsYXNzPSJzdHJpcCIgaWQ9ImIta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgaWQ9ImItY3VydmUiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjwvZGl2PgogIDxkaXYgaWQ9ImJldHMtc3RhdHVzIiBjbGFzcz0ic3RhdHVzIiBzdHlsZT0iZGlzcGxheTpub25lIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJzZWMtaGQiPk9wZW4gcGlja3M8L2Rpdj48ZGl2IGlkPSJiLW9wZW4iPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+QnkgbWFya2V0PC9kaXY+PGRpdiBjbGFzcz0ic3RyaXAiIGlkPSJiLW1rdHMiPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+UmVjZW50IGdyYWRlZDwvZGl2PgogIDxkaXYgY2xhc3M9ImZiYXIiIGlkPSJiLWZpbHQiPjxidXR0b24gY2xhc3M9ImNoaXAgb24iIG9uY2xpY2s9ImJmKCdBTEwnLHRoaXMpIj5BbGw8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJiZignTUwnLHRoaXMpIj5NTDwvYnV0dG9uPjxidXR0b24gY2xhc3M9ImNoaXAiIG9uY2xpY2s9ImJmKCdTUFInLHRoaXMpIj5TUFI8L2J1dHRvbj48YnV0dG9uIGNsYXNzPSJjaGlwIiBvbmNsaWNrPSJiZignVE9UJyx0aGlzKSI+VE9UPC9idXR0b24+PC9kaXY+CiAgPGRpdiBpZD0iYi1yZWNlbnQiPjwvZGl2PgogIDxkaXYgY2xhc3M9Im5vdGUiPjxiPkhvdyBwaWNrcyB3b3JrOjwvYj4gYSBwaWNrIGF1dG8tbG9ncyB0aGUgZmlyc3QgdGltZSBhIG1hcmtldCBjbGVhcnMgaXRzIGVkZ2UgZmxvb3IgKG9uZSBwZXIgZ2FtZSBwZXIgbWFya2V0KSwgc2l6ZWQgYnkgcXVhcnRlci1LZWxseSAoMXUgPSAxJSBiYW5rcm9sbCwgY2FwcGVkIGF0IDxzcGFuIGlkPSJiLW1heHUiPjI8L3NwYW4+dSkuIENsb3NpbmcgbGluZXMgZnJlZXplIGF0IHRoZSBsYXN0IHJlZnJlc2ggYmVmb3JlIHRpcDsgQ0xWIGlzIGdyYWRlZCBhZ2FpbnN0IFBpbm5hY2xlIHdoZW4gYXZhaWxhYmxlLCBlbHNlIHJldGFpbCBjb25zZW5zdXMuIFBvc2l0aXZlIENMViA9IHRoZSBwaWNrIGJlYXQgdGhlIGNsb3NlLjwvZGl2Pgo8L2Rpdj4KCjwhLS0gU0NPUkVTIC0tPgo8ZGl2IGlkPSJzZWMtc2NvcmVzIiBjbGFzcz0ic2VjdGlvbiI+CiAgPGRpdiBpZD0ic2NvcmVzLXN0YXR1cyIgY2xhc3M9InN0YXR1cyI+PHNwYW4gY2xhc3M9InNwaW4iPjwvc3Bhbj4gTG9hZGluZyBzY29yZXMmaGVsbGlwOzwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCIgaWQ9InNoLWxpdmUiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPiYjOTY3OTsgTGl2ZTwvZGl2PjxkaXYgaWQ9InMtbGl2ZSI+PC9kaXY+CiAgPGRpdiBjbGFzcz0ic2VjLWhkIiBpZD0ic2gtZG9uZSIgc3R5bGU9ImRpc3BsYXk6bm9uZSI+RmluYWw8L2Rpdj48ZGl2IGlkPSJzLWRvbmUiPjwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCIgaWQ9InNoLXVwIiBzdHlsZT0iZGlzcGxheTpub25lIj5VcGNvbWluZzwvZGl2PjxkaXYgaWQ9InMtdXAiPjwvZGl2Pgo8L2Rpdj4KCjwhLS0gREFUQSAtLT4KPGRpdiBpZD0ic2VjLWRhdGEiIGNsYXNzPSJzZWN0aW9uIj4KICA8ZGl2IGNsYXNzPSJzdHJpcCIgaWQ9ImQta3BpcyI+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgaWQ9ImQtbWFwIj48L2Rpdj4KICA8ZGl2IGNsYXNzPSJjYXJkIiBpZD0iZC1yZXBsYXkiPgogICAgPGRpdiBzdHlsZT0iZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtnYXA6OHB4O2ZsZXgtd3JhcDp3cmFwIj4KICAgICAgPGIgc3R5bGU9ImZvbnQtc2l6ZToxMnB4Ij5SZXBsYXkgY2FsaWJyYXRpb248L2I+CiAgICAgIDxsYWJlbCBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tbXV0ZWQpIj5TZWFzb24mbmJzcDs8aW5wdXQgaWQ9InJwbC15ZWFyIiBjbGFzcz0icnBsLWluIiB2YWx1ZT0iMjAyNiIgaW5wdXRtb2RlPSJudW1lcmljIiBhdXRvY29tcGxldGU9Im9mZiI+PC9sYWJlbD4KICAgIDwvZGl2PgogICAgPGRpdiBjbGFzcz0iZmJhciIgc3R5bGU9Im1hcmdpbjo5cHggMCAwIj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1wbGFuIiBvbmNsaWNrPSJycGxQbGFuKCkiPlBsYW48L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1pbmdlc3QiIG9uY2xpY2s9InJwbExvb3AoJ2luZ2VzdCcpIj5Jbmdlc3Q8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1yZXN1bHRzIiBvbmNsaWNrPSJycGxSZXN1bHRzKCkiPlJlc3VsdHM8L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1ydW4iIG9uY2xpY2s9InJwbExvb3AoJ3J1bicpIj5SdW48L2J1dHRvbj4KICAgICAgPGJ1dHRvbiBjbGFzcz0iY2hpcCIgaWQ9InJwbC1yZXBvcnQiIG9uY2xpY2s9InJwbFJlcG9ydCh0cnVlKSI+UmVwb3J0PC9idXR0b24+CiAgICAgIDxidXR0b24gY2xhc3M9ImNoaXAiIGlkPSJycGwtc3RvcCIgb25jbGljaz0icnBsU3RvcEZuKCkiIHN0eWxlPSJkaXNwbGF5Om5vbmU7Ym9yZGVyLWNvbG9yOnZhcigtLXJlZFRleHQpO2NvbG9yOnZhcigtLXJlZFRleHQpIj4mIzk2MzI7IFN0b3A8L2J1dHRvbj4KICAgIDwvZGl2PgogICAgPGRpdiBzdHlsZT0ibWFyZ2luLXRvcDo3cHgiPjxidXR0b24gY2xhc3M9InJwbC1saW5rIiBvbmNsaWNrPSJycGxUb2dnbGVDc3YoKSI+cGFzdGUgcmVzdWx0cyBDU1Y8L2J1dHRvbj4KICAgICAgPGRpdiBpZD0icnBsLWNzdndyYXAiIHN0eWxlPSJkaXNwbGF5Om5vbmUiPjx0ZXh0YXJlYSBpZD0icnBsLWNzdiIgY2xhc3M9InJwbC10YSIgcGxhY2Vob2xkZXI9ImRhdGUsYXdheSxob21lLGF3YXlfcHRzLGhvbWVfcHRzLG5ldXRyYWwmIzEwOzIwMjYtMDEtMTAsR29uemFnYSxEdWtlLDcwLDgwLCI+PC90ZXh0YXJlYT48L2Rpdj4KICAgIDwvZGl2PgogICAgPGRpdiBpZD0icnBsLWxvZyI+PC9kaXY+CiAgICA8ZGl2IGlkPSJycGwtc3RhdHVzIiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTttYXJnaW4tdG9wOjhweDtsaW5lLWhlaWdodDoxLjYiPiZoZWxsaXA7PC9kaXY+CiAgICA8ZGl2IGlkPSJycGwtcmVwb3J0IiBzdHlsZT0iZm9udC1zaXplOjExcHg7Y29sb3I6dmFyKC0tZGltKTtsaW5lLWhlaWdodDoxLjYiPjwvZGl2PgogIDwvZGl2PgogIDxkaXYgY2xhc3M9InNlYy1oZCI+VC1SYW5rIFRvcCAyNSA8c3BhbiBzdHlsZT0idGV4dC10cmFuc2Zvcm06bm9uZTtjb2xvcjp2YXIoLS1tdXRlZCkiIGlkPSJkLXlyIj48L3NwYW4+PC9kaXY+CiAgPGRpdiBjbGFzcz0iY2FyZCIgc3R5bGU9Im92ZXJmbG93LXg6YXV0byI+PHRhYmxlIGlkPSJkLXRibCI+PHRoZWFkPjx0cj48dGg+IzwvdGg+PHRoPlRlYW08L3RoPjx0aD5Db25mPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkak9FPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkakRFPC90aD48dGggc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPkFkalQ8L3RoPjx0aCBzdHlsZT0idGV4dC1hbGlnbjpyaWdodCI+QmFydGhhZzwvdGg+PC90cj48L3RoZWFkPjx0Ym9keT48L3Rib2R5PjwvdGFibGU+PC9kaXY+CiAgPGRpdiBjbGFzcz0ibm90ZSI+PGI+RGlhZ25vc3RpY3M6PC9iPiA8c3BhbiBjbGFzcz0ibW9ubyI+L2FwaS9kZWJ1Zy9vZGRzPC9zcGFuPiBwcm9iZXMgdGhlIE9kZHMgQVBJIGxpdmUgJm1pZGRvdDsgPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvZGVidWcvdG9ydmlrPC9zcGFuPiBzaG93cyByYXcgcm93cyArIHRoZSBkZXRlY3RlZCBjb2x1bW4gbG9jayAmbWlkZG90OyA8c3BhbiBjbGFzcz0ibW9ubyI+L2FwaS9kZWJ1Zy90ZWFtbWFwPC9zcGFuPiBsaXN0cyB1bm1hdGNoZWQgbmFtZXMgKGFkZCBmaXhlcyB2aWEgPHNwYW4gY2xhc3M9Im1vbm8iPlBPU1QgL2FwaS9hZG1pbi9hbGlhczwvc3Bhbj4pLjwvZGl2Pgo8L2Rpdj4KCjxkaXYgY2xhc3M9ImZvb3RlciI+SE9PUFNCRVQgdjEuMy4xICZtZGFzaDsgT2RkczogVGhlIE9kZHMgQVBJICZtaWRkb3Q7IE1vZGVsOiBiYXJ0dG9ydmlrLmNvbSAmYnVsbDsgJiM5ODg4OyBFbnRlcnRhaW5tZW50ICZhbXA7IGFuYWx5c2lzIG9ubHk8L2Rpdj4KCjxkaXYgY2xhc3M9ImJuYXYiPgo8YnV0dG9uIGNsYXNzPSJibmF2LWJ0biBvbiIgb25jbGljaz0iZ28oJ2dhbWVzJyx0aGlzKSI+PHNwYW4gY2xhc3M9ImJuYXYtaWNvIj48c3ZnIHdpZHRoPSIxOSIgaGVpZ2h0PSIxOSIgdmlld0JveD0iMCAwIDI0IDI0IiBmaWxsPSJub25lIiBzdHJva2U9ImN1cnJlbnRDb2xvciIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiPjxjaXJjbGUgY3g9IjEyIiBjeT0iMTIiIHI9IjkiLz48cGF0aCBkPSJNNS42IDUuNmM0IDMgOC44IDkuOCA5LjggMTVNMTguNCA1LjZjLTQgMy04LjggOS44LTkuOCAxNU0zIDEyaDE4Ii8+PC9zdmc+PC9zcGFuPkdhbWVzPC9idXR0b24+CjxidXR0b24gY2xhc3M9ImJuYXYtYnRuIiBvbmNsaWNrPSJnbygnZXYnLHRoaXMpIj48c3BhbiBjbGFzcz0iYm5hdi1pY28iPjxzdmcgd2lkdGg9IjE5IiBoZWlnaHQ9IjE5IiB2aWV3Qm94PSIwIDAgMjQgMjQiIGZpbGw9Im5vbmUiIHN0cm9rZT0iY3VycmVudENvbG9yIiBzdHJva2Utd2lkdGg9IjIiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCI+PHBhdGggZD0iTTEzIDJMNCAxNGg2bC0xIDggOS0xMmgtNmwxLTh6Ii8+PC9zdmc+PC9zcGFuPkVWPC9idXR0b24+CjxidXR0b24gY2xhc3M9ImJuYXYtYnRuIiBvbmNsaWNrPSJnbygnYmV0cycsdGhpcykiPjxzcGFuIGNsYXNzPSJibmF2LWljbyI+PHN2ZyB3aWR0aD0iMTkiIGhlaWdodD0iMTkiIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0ibm9uZSIgc3Ryb2tlPSJjdXJyZW50Q29sb3IiIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBzdHJva2UtbGluZWpvaW49InJvdW5kIj48cGF0aCBkPSJNNCA3aDE2djNhMiAyIDAgMDAwIDR2M0g0di0zYTIgMiAwIDAwMC00Vjd6Ii8+PHBhdGggZD0iTTEzIDd2MTAiIHN0cm9rZS1kYXNoYXJyYXk9IjIgMyIvPjwvc3ZnPjwvc3Bhbj5CZXRzPC9idXR0b24+CjxidXR0b24gY2xhc3M9ImJuYXYtYnRuIiBvbmNsaWNrPSJnbygnc2NvcmVzJyx0aGlzKSI+PHNwYW4gY2xhc3M9ImJuYXYtaWNvIj48c3ZnIHdpZHRoPSIxOSIgaGVpZ2h0PSIxOSIgdmlld0JveD0iMCAwIDI0IDI0IiBmaWxsPSJub25lIiBzdHJva2U9ImN1cnJlbnRDb2xvciIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiPjxjaXJjbGUgY3g9IjEyIiBjeT0iMTIiIHI9IjkiLz48cGF0aCBkPSJNMTIgN3Y1bDMgMiIvPjwvc3ZnPjwvc3Bhbj5TY29yZXM8L2J1dHRvbj4KPGJ1dHRvbiBjbGFzcz0iYm5hdi1idG4iIG9uY2xpY2s9ImdvKCdkYXRhJyx0aGlzKSI+PHNwYW4gY2xhc3M9ImJuYXYtaWNvIj48c3ZnIHdpZHRoPSIxOSIgaGVpZ2h0PSIxOSIgdmlld0JveD0iMCAwIDI0IDI0IiBmaWxsPSJub25lIiBzdHJva2U9ImN1cnJlbnRDb2xvciIgc3Ryb2tlLXdpZHRoPSIyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiPjxwYXRoIGQ9Ik00IDE5VjVNNCAxOWgxNk04IDE2di01TTEyIDE2VjhNMTYgMTZ2LTNNMjAgMTZWNiIvPjwvc3ZnPjwvc3Bhbj5EYXRhPC9idXR0b24+CjwvZGl2PgoKPHNjcmlwdD4KdmFyIFNMQVRFPW51bGwsRklMVD17Y29uZjoiIix0b3A6ZmFsc2UsZWRnZTpmYWxzZSxtaW5FOjB9LFNIT1c9MjUsVEg9e01MOjQsU1BSOjUsVE9UOjUuNSxCT09LUzozfTsKdmFyIEVWRD1udWxsLEVWRj17c3RyaWN0OnRydWUsbWluOjB9LFJDPW51bGwsQkZJTFQ9IkFMTCIsQlNIT1c9MjU7CmZ1bmN0aW9uIGdvKHQsYnRuKXtbImdhbWVzIiwiZXYiLCJiZXRzIiwic2NvcmVzIiwiZGF0YSJdLmZvckVhY2goZnVuY3Rpb24ocyl7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInNlYy0iK3MpLmNsYXNzTGlzdC50b2dnbGUoIm9uIixzPT09dCk7fSk7CiAgZG9jdW1lbnQucXVlcnlTZWxlY3RvckFsbCgiLmJuYXYtYnRuIikuZm9yRWFjaChmdW5jdGlvbihiKXtiLmNsYXNzTGlzdC5yZW1vdmUoIm9uIik7fSk7YnRuLmNsYXNzTGlzdC5hZGQoIm9uIik7CiAgaWYodD09PSJldiIpbG9hZEV2KCk7aWYodD09PSJiZXRzIilsb2FkQmV0cygpO2lmKHQ9PT0ic2NvcmVzIilsb2FkU2NvcmVzKCk7aWYodD09PSJkYXRhIilsb2FkRGF0YSgpO30KZnVuY3Rpb24gdGcoYnRuLGspe0ZJTFRba109IUZJTFRba107YnRuLmNsYXNzTGlzdC50b2dnbGUoIm9uIixGSUxUW2tdKTthcHBseUZpbHRlcnMoKTt9CmZ1bmN0aW9uIG1lKHYsYnRuKXtGSUxULm1pbkU9djtkb2N1bWVudC5xdWVyeVNlbGVjdG9yQWxsKCIjbWluZWRnZSAuY2hpcCIpLmZvckVhY2goZnVuY3Rpb24oYil7Yi5jbGFzc0xpc3QucmVtb3ZlKCJvbiIpO30pO2J0bi5jbGFzc0xpc3QuYWRkKCJvbiIpO2FwcGx5RmlsdGVycygpO30KZnVuY3Rpb24gZm10QW0odil7aWYodj09PW51bGx8fHY9PT11bmRlZmluZWQpcmV0dXJuICJcdTIwMTQiO3JldHVybiB2PjA/IisiK3Y6IiIrdjt9CmZ1bmN0aW9uIGZtdFNwcih2KXtpZih2PT09bnVsbHx8dj09PXVuZGVmaW5lZClyZXR1cm4gIlx1MjAxNCI7cmV0dXJuICh2PjA/IisiOiIiKSt2O30KZnVuY3Rpb24gdGlwVGltZShpc28pe3RyeXt2YXIgZD1uZXcgRGF0ZShpc28pO3JldHVybiBkLnRvTG9jYWxlVGltZVN0cmluZyhbXSx7aG91cjoibnVtZXJpYyIsbWludXRlOiIyLWRpZ2l0In0pO31jYXRjaChlKXtyZXR1cm4gIiI7fX0KZnVuY3Rpb24gbGFzdFdvcmQocyl7cmV0dXJuIHM/cy5zcGxpdCgiICIpLnBvcCgpOiI/Ijt9CmZ1bmN0aW9uIHNob3J0TmFtZShzKXtpZighcylyZXR1cm4gIj8iO3ZhciB3PXMuc3BsaXQoIiAiKTtyZXR1cm4gdy5sZW5ndGg+Mj93LnNsaWNlKDAsLTEpLmpvaW4oIiAiKTpzO30KCmZ1bmN0aW9uIGJlc3RFZGdlKGcpe3ZhciBiPTA7WyJNTCIsIlNQUiIsIlRPVCJdLmZvckVhY2goZnVuY3Rpb24obSl7dmFyIGU9Zy5lZGdlcyYmZy5lZGdlc1ttXTtpZihlJiZlLm9rJiZlLmVkZ2UqMTAwPmIpYj1lLmVkZ2UqMTAwO30pO3JldHVybiBiO30KZnVuY3Rpb24gaGFzSG90KGcpe3ZhciBoPWZhbHNlO1siTUwiLCJTUFIiLCJUT1QiXS5mb3JFYWNoKGZ1bmN0aW9uKG0pe3ZhciBlPWcuZWRnZXMmJmcuZWRnZXNbbV07aWYoZSYmZS5vayYmZS5ob3QpaD10cnVlO30pO3JldHVybiBoO30KCmZ1bmN0aW9uIGFwcGx5RmlsdGVycygpewogIGlmKCFTTEFURSlyZXR1cm47U0hPVz0yNTtGSUxULmNvbmY9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImYtY29uZiIpLnZhbHVlOwogIHJlbmRlckdhbWVzKCk7Cn0KZnVuY3Rpb24gcmVuZGVyR2FtZXMoKXsKICB2YXIgZWw9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzIiksc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzLXN0YXR1cyIpOwogIHN0LnN0eWxlLmRpc3BsYXk9Im5vbmUiOwogIHZhciBncz0oU0xBVEUuZ2FtZXN8fFtdKS5zbGljZSgpOwogIGlmKEZJTFQuY29uZilncz1ncy5maWx0ZXIoZnVuY3Rpb24oZyl7cmV0dXJuIGcuYUNvbmY9PT1GSUxULmNvbmZ8fGcuaENvbmY9PT1GSUxULmNvbmY7fSk7CiAgaWYoRklMVC50b3ApZ3M9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiAoZy5hUmFuayYmZy5hUmFuazw9MjUpfHwoZy5oUmFuayYmZy5oUmFuazw9MjUpO30pOwogIGlmKEZJTFQuZWRnZSlncz1ncy5maWx0ZXIoaGFzSG90KTsKICBpZihGSUxULm1pbkU+MClncz1ncy5maWx0ZXIoZnVuY3Rpb24oZyl7cmV0dXJuIGJlc3RFZGdlKGcpPj1GSUxULm1pbkU7fSk7CiAgdmFyIHNvcnQ9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImYtc29ydCIpLnZhbHVlOwogIGlmKHNvcnQ9PT0iZWRnZSIpZ3Muc29ydChmdW5jdGlvbihhLGIpe3JldHVybiBiZXN0RWRnZShiKS1iZXN0RWRnZShhKTt9KTsKICBlbHNlIGdzLnNvcnQoZnVuY3Rpb24oYSxiKXtyZXR1cm4gbmV3IERhdGUoYS5jb21tZW5jZSktbmV3IERhdGUoYi5jb21tZW5jZSk7fSk7CiAgaWYoIWdzLmxlbmd0aCl7CiAgICB2YXIgaW5uZXI7CiAgICBpZighKFNMQVRFLmdhbWVzfHxbXSkubGVuZ3RoKXsKICAgICAgaW5uZXI9JzxiPk5vIE5DQUFCIGdhbWVzIG9uIHRoZSBib2FyZC48L2I+PGJyPjxicj4nKyhTTEFURS5ub3RlP1NMQVRFLm5vdGU6J1RoZSBzZWFzb24gcnVucyBOb3ZlbWJlciBcdTIwMTMgQXByaWwuIFRoZSBkYXRhIGxheWVyIGlzIGxpdmUgYW5kIHdpbGwgcG9wdWxhdGUgd2hlbiBib29rcyBwb3N0IHRoZSBmaXJzdCBzbGF0ZXMuJyk7CiAgICB9IGVsc2UgewogICAgICBpbm5lcj0nTm8gZ2FtZXMgbWF0Y2ggdGhlIGN1cnJlbnQgZmlsdGVycyBcdTIwMTQgJysoU0xBVEUuZ2FtZXMubGVuZ3RoKSsnIG9uIHRoZSBzbGF0ZSB0b2RheS4gQ2xlYXIgYSBmaWx0ZXIgdG8gc2VlIHRoZW0uJzsKICAgIH0KICAgIGVsLmlubmVySFRNTD0nPGRpdiBjbGFzcz0iZW1wdHkiPicraW5uZXIrJzwvZGl2Pic7cmV0dXJuOwogIH0KICB2YXIgaHRtbD1ncy5zbGljZSgwLFNIT1cpLm1hcChmdW5jdGlvbihnKXsKICAgIHZhciBhUj1nLmFSYW5rJiZnLmFSYW5rPD0yNT8nPHNwYW4gY2xhc3M9InJrIj4jJytnLmFSYW5rKyc8L3NwYW4+JzonJzsKICAgIHZhciBoUj1nLmhSYW5rJiZnLmhSYW5rPD0yNT8nPHNwYW4gY2xhc3M9InJrIj4jJytnLmhSYW5rKyc8L3NwYW4+JzonJzsKICAgIHZhciBtZXRhPSc8c3BhbiBjbGFzcz0idGFnIHRhZy10aW1lIj4nK3RpcFRpbWUoZy5jb21tZW5jZSkrJzwvc3Bhbj4nOwogICAgaWYoZy5uZXV0cmFsKW1ldGErPSc8c3BhbiBjbGFzcz0idGFnIHRhZy1uIj5OPC9zcGFuPic7CiAgICBtZXRhKz0nPHNwYW4gY2xhc3M9InRhZyB0YWctYmsiPicrZy5uQm9va3MrJyBiazwvc3Bhbj4nOwogICAgaWYoZy5waWNrcyYmZy5waWNrcy5sZW5ndGgpbWV0YSs9JzxzcGFuIGNsYXNzPSJ0YWciIHN0eWxlPSJiYWNrZ3JvdW5kOnJnYmEoMjQsMTg0LDEyNCwuMTIpO2NvbG9yOnZhcigtLWdyZWVuKTtib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjQsMTg0LDEyNCwuMzUpIj5cdTI2MDUgJytnLnBpY2tzLmpvaW4oIi8iKSsnPC9zcGFuPic7CiAgICB2YXIgcHJvaixlZGdlcyxzaGFycD0iIjsKICAgIGlmKCFnLm1vZGVsZWQpewogICAgICBwcm9qPSc8ZGl2IGNsYXNzPSJnLXByb2oiPjxzcGFuIGNsYXNzPSJhd2FpdCI+JysoZy5tb2RlbFJlYXNvbnx8InVucmF0ZWQgdGVhbSIpKyc8L3NwYW4+PC9kaXY+JztlZGdlcz0iIjsKICAgIH0gZWxzZSB7CiAgICAgIHByb2o9JzxkaXYgY2xhc3M9ImctcHJvaiI+JysKICAgICAgICAnPHNwYW4+UHJvaiA8YiBjbGFzcz0ibW9ubyI+JytnLnByb2ouYVB0cy50b0ZpeGVkKDApKydcdTIwMTMnK2cucHJvai5oUHRzLnRvRml4ZWQoMCkrJzwvYj48L3NwYW4+JysKICAgICAgICAnPHNwYW4+TWFyZ2luIDxiIGNsYXNzPSJtb25vIj4nK2xhc3RXb3JkKGcuaG9tZSkuc2xpY2UoMCwzKS50b1VwcGVyQ2FzZSgpKycgJytmbXRTcHIoKygtKGcucHJvai5tYXJnaW4pKS50b0ZpeGVkKDEpKSsnPC9iPicrKGcuYm9vay5zcHJIIT09bnVsbD8nIDxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPmJvb2sgJytmbXRTcHIoZy5ib29rLnNwckgpKyc8L3NwYW4+JzonJykrJzwvc3Bhbj4nKwogICAgICAgICc8c3Bhbj5Ub3RhbCA8YiBjbGFzcz0ibW9ubyI+JytnLnByb2oudG90YWwudG9GaXhlZCgxKSsnPC9iPicrKGcuYm9vay50b3QhPT1udWxsPycgPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+Ym9vayAnK2cuYm9vay50b3QrJzwvc3Bhbj4nOicnKSsnPC9zcGFuPicrCiAgICAgICc8L2Rpdj4nOwogICAgICBlZGdlcz0nPGRpdiBjbGFzcz0iZy1lZGdlcyI+JytbIk1MIiwiU1BSIiwiVE9UIl0ubWFwKGZ1bmN0aW9uKG0pewogICAgICAgIHZhciBlPWcuZWRnZXNbbV07CiAgICAgICAgaWYoIWV8fCFlLm9rKXJldHVybiAnPHNwYW4gY2xhc3M9ImVkIj48c3BhbiBjbGFzcz0ic2QiPicrbSsnPC9zcGFuPjxzcGFuIGNsYXNzPSJhd2FpdCIgc3R5bGU9InBhZGRpbmc6MCA0cHgiPicrKGUmJmUucmVhc29uP2UucmVhc29uOiJcdTIwMTQiKSsnPC9zcGFuPjwvc3Bhbj4nOwogICAgICAgIHJldHVybiAnPHNwYW4gY2xhc3M9ImVkJysoZS5ob3Q/IiBob3QiOiIiKSsnIj48c3BhbiBjbGFzcz0ic2QiPicrbSsnICcrZS5sYWJlbCsnPC9zcGFuPisnKyhlLmVkZ2UqMTAwKS50b0ZpeGVkKDEpKyclPC9zcGFuPic7CiAgICAgIH0pLmpvaW4oIiIpKyc8L2Rpdj4nOwogICAgICBpZihnLnNoYXJwJiYoZy5zaGFycC5zcHJIIT09bnVsbHx8Zy5zaGFycC50b3QhPT1udWxsKSl7CiAgICAgICAgc2hhcnA9JzxkaXYgY2xhc3M9Imctc2hhcnAiPjxiPlBpbm5hY2xlPC9iPiAnKyhnLnNoYXJwLnNwckghPT1udWxsPygic3ByZWFkICIrZm10U3ByKGcuc2hhcnAuc3BySCkpOiIiKSsoZy5zaGFycC50b3QhPT1udWxsPygiIFx1MDBiNyB0b3RhbCAiK2cuc2hhcnAudG90KToiIikrKGcuc2hhcnAucEhvbWUhPT1udWxsPygiIFx1MDBiNyBuby12aWcgaG9tZSAiKyhnLnNoYXJwLnBIb21lKjEwMCkudG9GaXhlZCgwKSsiJSIpOiIiKSsnPC9kaXY+JzsKICAgICAgfQogICAgfQogICAgcmV0dXJuICc8ZGl2IGNsYXNzPSJnY2FyZCI+PGRpdiBjbGFzcz0iZy10b3AiPjxkaXYgY2xhc3M9ImctdGVhbXMiPicrYVIrc2hvcnROYW1lKGcuYXdheSkrJzxzcGFuIGNsYXNzPSJhdCI+QDwvc3Bhbj4nK2hSK3Nob3J0TmFtZShnLmhvbWUpKyc8L2Rpdj48ZGl2IGNsYXNzPSJnLW1ldGEiPicrbWV0YSsnPC9kaXY+PC9kaXY+Jytwcm9qK2VkZ2VzK3NoYXJwKyc8L2Rpdj4nOwogIH0pLmpvaW4oIiIpOwogIGlmKGdzLmxlbmd0aD5TSE9XKWh0bWwrPSc8YnV0dG9uIGNsYXNzPSJtb3JlIiBvbmNsaWNrPSJTSE9XKz0yNTtyZW5kZXJHYW1lcygpIj5TaG93IG1vcmUgKCcrKGdzLmxlbmd0aC1TSE9XKSsnIHJlbWFpbmluZyk8L2J1dHRvbj4nOwogIGVsLmlubmVySFRNTD1odG1sOwp9CmZ1bmN0aW9uIHJlbmRlcktwaXMoKXsKICB2YXIgYz1TTEFURS5jb3ZlcmFnZXx8e30saz1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgia3BpcyIpOwogIHZhciBob3Q9KFNMQVRFLmdhbWVzfHxbXSkuZmlsdGVyKGhhc0hvdCkubGVuZ3RoOwogIGsuaW5uZXJIVE1MPQogICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPkdhbWVzPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoYy5nYW1lc3x8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKGMubGluZWR8fDApKycgd2l0aCBsaW5lczwvZGl2PjwvZGl2PicrCiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+TW9kZWxlZDwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGMubW9kZWxlZHx8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPlRvcnZpay1yYXRlZCBib3RoIHNpZGVzPC9kaXY+PC9kaXY+JysKICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5FZGdlczwvZGl2PjxkaXYgY2xhc3M9InYiIHN0eWxlPSJjb2xvcjonKyhob3Q+MD8idmFyKC0tZ3JlZW4pIjoidmFyKC0tbXV0ZWQpIikrJyI+Jytob3QrJzwvZGl2PjxkaXYgY2xhc3M9InMiPk1MICcrVEguTUwrJyUgLyBTUFIgJytUSC5TUFIrJyUgLyBUT1QgJytUSC5UT1QrJyU8L2Rpdj48L2Rpdj4nOwogIHZhciBjb25mPXt9OyhTTEFURS5nYW1lc3x8W10pLmZvckVhY2goZnVuY3Rpb24oZyl7aWYoZy5hQ29uZiljb25mW2cuYUNvbmZdPTE7aWYoZy5oQ29uZiljb25mW2cuaENvbmZdPTE7fSk7CiAgdmFyIHNlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZi1jb25mIiksY3VyPXNlbC52YWx1ZTsKICBzZWwuaW5uZXJIVE1MPSc8b3B0aW9uIHZhbHVlPSIiPkFsbCBjb25mZXJlbmNlczwvb3B0aW9uPicrT2JqZWN0LmtleXMoY29uZikuc29ydCgpLm1hcChmdW5jdGlvbih4KXtyZXR1cm4gJzxvcHRpb24nKyh4PT09Y3VyPyIgc2VsZWN0ZWQiOiIiKSsnPicreCsnPC9vcHRpb24+Jzt9KS5qb2luKCIiKTsKfQpmdW5jdGlvbiBsb2FkU2xhdGUoZm9yY2UpewogIGlmKGZvcmNlKXt2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IExvYWRpbmcgc2xhdGUmaGVsbGlwOyc7fQogIHJldHVybiBmZXRjaCgiL2FwaS9zbGF0ZSIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oZCl7CiAgICBpZihkLm9rPT09ZmFsc2UpdGhyb3cgbmV3IEVycm9yKGQuZXJyb3J8fCJzbGF0ZSBmYWlsZWQiKTsKICAgIFNMQVRFPWQ7CiAgICBpZihkLnRocmVzaG9sZHMpe1RIPWQudGhyZXNob2xkcztkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidGgtbWwiKS50ZXh0Q29udGVudD1USC5NTDtkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgidGgtc3ByIikudGV4dENvbnRlbnQ9VEguU1BSO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJ0aC10b3QiKS50ZXh0Q29udGVudD1USC5UT1Q7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInRoLWJrIikudGV4dENvbnRlbnQ9VEguQk9PS1M7fQogICAgcmVuZGVyS3BpcygpO3JlbmRlckdhbWVzKCk7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiY29ubiIpLmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWdyZWVuKSI+JiM5Njc5Ozwvc3Bhbj4gJysoZC5xdW90YSYmZC5xdW90YS5yZW1haW5pbmchPW51bGw/KCJxdW90YSAiK2QucXVvdGEucmVtYWluaW5nKToiY29ubmVjdGVkIik7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7CiAgICB2YXIgc3Q9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImdhbWVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjsKICAgIHN0LmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLXJlZFRleHQpIj4mIzk4ODg7ICcrZS5tZXNzYWdlKyc8L3NwYW4+ICZtZGFzaDsgPGJ1dHRvbiBjbGFzcz0iaGRyLWJ0biIgb25jbGljaz0ibG9hZEFsbCh0cnVlKSI+UmV0cnk8L2J1dHRvbj4nOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImNvbm4iKS5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5Njc5Ozwvc3Bhbj4gZXJyb3InOwogIH0pOwp9CmZ1bmN0aW9uIHNyb3coZyl7CiAgdmFyIGxpdmU9IWcuY29tcGxldGVkJiZnLnNjb3JlczsKICB2YXIgc2M9Zy5zY29yZXM/Zy5zY29yZXMubWFwKGZ1bmN0aW9uKHMpe3JldHVybiBzLnNjb3JlO30pLmpvaW4oIiBcdTIwMTMgIik6IiI7CiAgcmV0dXJuICc8ZGl2IGNsYXNzPSJzcm93Ij48ZGl2PjxkaXYgY2xhc3M9InQiPicrc2hvcnROYW1lKGcuYXdheV90ZWFtKSsnIEAgJytzaG9ydE5hbWUoZy5ob21lX3RlYW0pKyc8L2Rpdj48ZGl2IGNsYXNzPSJzdCI+JysoZy5jb21wbGV0ZWQ/IkZpbmFsIjoobGl2ZT8nPHNwYW4gY2xhc3M9ImxpdmUtZG90Ij4mIzk2Nzk7IGxpdmU8L3NwYW4+Jzp0aXBUaW1lKGcuY29tbWVuY2VfdGltZSkpKSsnPC9kaXY+PC9kaXY+PGRpdiBjbGFzcz0ic2MiPicrKHNjfHwiXHUyMDE0IikrJzwvZGl2PjwvZGl2Pic7Cn0KZnVuY3Rpb24gbG9hZFNjb3JlcygpewogIHZhciBzdD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgic2NvcmVzLXN0YXR1cyIpO3N0LnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtzdC5pbm5lckhUTUw9JzxzcGFuIGNsYXNzPSJzcGluIj48L3NwYW4+IExvYWRpbmcgc2NvcmVzJmhlbGxpcDsnOwogIGZldGNoKCIvYXBpL3Njb3JlcyIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oZCl7CiAgICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjsKICAgIHZhciBncz1kLmdhbWVzfHxbXTsKICAgIHZhciBsaXZlPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gIWcuY29tcGxldGVkJiZnLnNjb3Jlczt9KTsKICAgIHZhciBkb25lPWdzLmZpbHRlcihmdW5jdGlvbihnKXtyZXR1cm4gZy5jb21wbGV0ZWQ7fSk7CiAgICB2YXIgdXA9Z3MuZmlsdGVyKGZ1bmN0aW9uKGcpe3JldHVybiAhZy5jb21wbGV0ZWQmJiFnLnNjb3Jlczt9KTsKICAgIGZ1bmN0aW9uIHB1dChpZCxoZCxhcnIpe2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKGhkKS5zdHlsZS5kaXNwbGF5PWFyci5sZW5ndGg/ImJsb2NrIjoibm9uZSI7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoaWQpLmlubmVySFRNTD1hcnIubWFwKHNyb3cpLmpvaW4oIiIpO30KICAgIHB1dCgicy1saXZlIiwic2gtbGl2ZSIsbGl2ZSk7cHV0KCJzLWRvbmUiLCJzaC1kb25lIixkb25lKTtwdXQoInMtdXAiLCJzaC11cCIsdXAuc2xpY2UoMCw0MCkpOwogICAgaWYoIWdzLmxlbmd0aCl7c3Quc3R5bGUuZGlzcGxheT0iYmxvY2siO3N0LmlubmVySFRNTD0nPGRpdiBjbGFzcz0iZW1wdHkiPjxiPk5vIGdhbWVzIGluIHRoZSBzY29yZXMgd2luZG93LjwvYj48YnI+PGJyPlNlYXNvbiBydW5zIE5vdmVtYmVyIFx1MjAxMyBBcHJpbC48L2Rpdj4nO30KICB9KS5jYXRjaChmdW5jdGlvbihlKXtzdC5pbm5lckhUTUw9JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1yZWRUZXh0KSI+JiM5ODg4OyAnK2UubWVzc2FnZSsnPC9zcGFuPic7fSk7Cn0KZnVuY3Rpb24gbG9hZERhdGEoKXsKICBQcm9taXNlLmFsbFNldHRsZWQoW2ZldGNoKCIvYXBpL2hlYWx0aCIpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLGZldGNoKCIvYXBpL3JhdGluZ3M/dG9wPTI1IikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSksZmV0Y2goIi9hcGkvZGVidWcvdGVhbW1hcD9zdW1tYXJ5PTEiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KV0pLnRoZW4oZnVuY3Rpb24ocmVzKXsKICAgIHZhciBoPXJlc1swXS5zdGF0dXM9PT0iZnVsZmlsbGVkIj9yZXNbMF0udmFsdWU6e307CiAgICB2YXIgcnQ9cmVzWzFdLnN0YXR1cz09PSJmdWxmaWxsZWQiP3Jlc1sxXS52YWx1ZTp7fTsKICAgIHZhciB0bT1yZXNbMl0uc3RhdHVzPT09ImZ1bGZpbGxlZCI/cmVzWzJdLnZhbHVlOnt9OwogICAgdmFyIHR2PWgudG9ydmlrfHx7fTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJkLWtwaXMiKS5pbm5lckhUTUw9CiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5PZGRzIHF1b3RhPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhoLnF1b3RhJiZoLnF1b3RhLnJlbWFpbmluZyE9bnVsbD9oLnF1b3RhLnJlbWFpbmluZzoiXHUyMDE0IikrJzwvZGl2PjxkaXYgY2xhc3M9InMiPmNyZWRpdHMgcmVtYWluaW5nPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlRvcnZpazwvZGl2PjxkaXYgY2xhc3M9InYiPicrKHR2LnRlYW1zfHwwKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysodHYueWVhcnx8IiIpKycgJm1pZGRvdDsgJysodHYubW9kZXx8Im5vdCBsb2FkZWQiKSsodHYuYWdlTWluIT1udWxsPygnICZtaWRkb3Q7ICcrdHYuYWdlTWluKydtIG9sZCcpOicnKSsnPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlJlZGlzPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoaC5yZWRpcz8ib24iOiJvZmYiKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoaC5yZWRpcz8icGVyc2lzdGVuY2UgYWN0aXZlIjoic2V0IFVwc3Rhc2ggZW52IHZhcnMiKSsnPC9kaXY+PC9kaXY+JzsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJkLW1hcCIpLmlubmVySFRNTD0nPGIgc3R5bGU9ImZvbnQtc2l6ZToxMnB4Ij5UZWFtLW5hbWUgbWFwPC9iPjxkaXYgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDo0cHgiPicrKHRtLm1hdGNoZWQhPW51bGw/KHRtLm1hdGNoZWQrIiBtYXRjaGVkIFx1MDBiNyAiK3RtLnVubWF0Y2hlZCsiIHVubWF0Y2hlZCIrKHRtLnVubWF0Y2hlZD4wPycgXHUyMDE0IHJldmlldyA8c3BhbiBjbGFzcz0ibW9ubyI+L2FwaS9kZWJ1Zy90ZWFtbWFwPC9zcGFuPic6IiIpKToicG9wdWxhdGVzIG9uY2UgYSBzbGF0ZSBoYXMgYmVlbiBmZXRjaGVkIikrJzwvZGl2Pic7CiAgICBycGxTdGF0dXMoKTtycGxSZXBvcnQoZmFsc2UpOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImQteXIiKS50ZXh0Q29udGVudD10di55ZWFyPygiXHUyMDE0ICIrdHYueWVhcik6IiI7CiAgICB2YXIgdGI9ZG9jdW1lbnQucXVlcnlTZWxlY3RvcigiI2QtdGJsIHRib2R5Iik7CiAgICB0Yi5pbm5lckhUTUw9KHJ0LnRlYW1zfHxbXSkubWFwKGZ1bmN0aW9uKHQpe3JldHVybiAnPHRyPjx0ZCBjbGFzcz0ibW9ubyI+Jyt0LnJhbmsrJzwvdGQ+PHRkPicrdC50ZWFtKyc8L3RkPjx0ZCBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj4nKyh0LmNvbmZ8fCIiKSsnPC90ZD48dGQgY2xhc3M9Im1vbm8iIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij4nK3QuYWRqb2UudG9GaXhlZCgxKSsnPC90ZD48dGQgY2xhc3M9Im1vbm8iIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij4nK3QuYWRqZGUudG9GaXhlZCgxKSsnPC90ZD48dGQgY2xhc3M9Im1vbm8iIHN0eWxlPSJ0ZXh0LWFsaWduOnJpZ2h0Ij4nK3QuYWRqdC50b0ZpeGVkKDEpKyc8L3RkPjx0ZCBjbGFzcz0ibW9ubyIgc3R5bGU9InRleHQtYWxpZ246cmlnaHQiPicrdC5iYXJ0aGFnLnRvRml4ZWQoMykrJzwvdGQ+PC90cj4nO30pLmpvaW4oIiIpfHwnPHRyPjx0ZCBjb2xzcGFuPSI3IiBzdHlsZT0iY29sb3I6dmFyKC0tbXV0ZWQpIj5SYXRpbmdzIG5vdCBsb2FkZWQgXHUyMDE0IGNoZWNrIC9hcGkvZGVidWcvdG9ydmlrPC90ZD48L3RyPic7CiAgfSk7Cn0KZnVuY3Rpb24gZXZTdHJpY3QoYnRuKXtFVkYuc3RyaWN0PSFFVkYuc3RyaWN0O2J0bi5jbGFzc0xpc3QudG9nZ2xlKCJvbiIsRVZGLnN0cmljdCk7cmVuZGVyRXYoKTt9CmZ1bmN0aW9uIGV2TWluKHYsYnRuKXtFVkYubWluPXY7dmFyIGJzPWJ0bi5wYXJlbnROb2RlLnF1ZXJ5U2VsZWN0b3JBbGwoIi5jaGlwIik7Zm9yKHZhciBpPTE7aTxicy5sZW5ndGg7aSsrKWJzW2ldLmNsYXNzTGlzdC5yZW1vdmUoIm9uIik7YnRuLmNsYXNzTGlzdC5hZGQoIm9uIik7cmVuZGVyRXYoKTt9CmZ1bmN0aW9uIGV2TGFiZWwocil7aWYoci5ta3Q9PT0iTUwiKXJldHVybiAoci5zaWRlPT09ImhvbWUiP3Nob3J0TmFtZShyLmhvbWUpOnNob3J0TmFtZShyLmF3YXkpKSsiIE1MIjtpZihyLm1rdD09PSJTUFIiKXJldHVybiAoci5zaWRlPT09ImhvbWUiP3Nob3J0TmFtZShyLmhvbWUpOnNob3J0TmFtZShyLmF3YXkpKSsiICIrZm10U3ByKHIubGluZSk7cmV0dXJuIChyLnNpZGU9PT0ib3ZlciI/Ik92ZXIgIjoiVW5kZXIgIikrci5saW5lO30KZnVuY3Rpb24gZXZSb3cocil7CiAgdmFyIGJhZGdlPXIuc3Ryb25nPyc8c3BhbiBjbGFzcz0idGFnIiBzdHlsZT0iYmFja2dyb3VuZDpyZ2JhKDI0LDE4NCwxMjQsLjEyKTtjb2xvcjp2YXIoLS1ncmVlbik7Ym9yZGVyOjFweCBzb2xpZCByZ2JhKDI0LDE4NCwxMjQsLjM1KSI+U1RST05HPC9zcGFuPic6JzxzcGFuIGNsYXNzPSJ0YWcgdGFnLWJrIj5XRUFLPC9zcGFuPic7CiAgdmFyIG1kbD1yLm1vZGVsPyhyLm1vZGVsLmFncmVlPyc8c3BhbiBzdHlsZT0iY29sb3I6dmFyKC0tZ3JlZW4pIj4mIzEwMDAzOyBtb2RlbCAnKyhyLm1vZGVsLnAqMTAwKS50b0ZpeGVkKDApKyclPC9zcGFuPic6JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPiYjMTAwMDc7IG1vZGVsICcrKHIubW9kZWwucCoxMDApLnRvRml4ZWQoMCkrJyU8L3NwYW4+Jyk6JzxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPiZtZGFzaDsgdW5tb2RlbGVkPC9zcGFuPic7CiAgcmV0dXJuICc8ZGl2IGNsYXNzPSJnY2FyZCI+PGRpdiBjbGFzcz0iZy10b3AiPjxkaXYgY2xhc3M9ImctdGVhbXMiPicrc2hvcnROYW1lKHIuYXdheSkrJzxzcGFuIGNsYXNzPSJhdCI+QDwvc3Bhbj4nK3Nob3J0TmFtZShyLmhvbWUpKyc8L2Rpdj48ZGl2IGNsYXNzPSJnLW1ldGEiPjxzcGFuIGNsYXNzPSJ0YWcgdGFnLXRpbWUiPicrdGlwVGltZShyLmNvbW1lbmNlKSsnPC9zcGFuPicrYmFkZ2UrJzwvZGl2PjwvZGl2PicrCiAgJzxkaXYgY2xhc3M9ImctcHJvaiI+PHNwYW4+PGI+JytldkxhYmVsKHIpKyc8L2I+ICcrZm10QW0oci5vZGRzKSsnIEAgJytyLmJvb2srJzwvc3Bhbj48c3Bhbj5FViA8YiBjbGFzcz0ibW9ubyIgc3R5bGU9ImNvbG9yOnZhcigtLWdyZWVuKSI+Kycrci5ldlBjdC50b0ZpeGVkKDEpKyclPC9iPjwvc3Bhbj48c3Bhbj5mYWlyIDxiIGNsYXNzPSJtb25vIj4nKyhyLnBGYWlyKjEwMCkudG9GaXhlZCgxKSsnJTwvYj48L3NwYW4+Jysoci5nYXAhPW51bGw/JzxzcGFuPmdhcCA8YiBjbGFzcz0ibW9ubyI+JytyLmdhcC50b0ZpeGVkKDEpKyc8L2I+PC9zcGFuPic6JycpKyc8L2Rpdj4nKwogICc8ZGl2IGNsYXNzPSJnLXNoYXJwIj4nK21kbCsnICZtaWRkb3Q7ICcrci5uQm9va3MrJyBib29rJysoci5uQm9va3M+MT8icyI6IiIpKycgYXQgdGhpcyBsaW5lPC9kaXY+PC9kaXY+JzsKfQpmdW5jdGlvbiByZW5kZXJFdigpewogIGlmKCFFVkQpcmV0dXJuOwogIHZhciBjPUVWRC5jb3ZlcmFnZXx8e307CiAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LWtwaXMiKS5pbm5lckhUTUw9CiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+Q2FuZGlkYXRlczwvZGl2PjxkaXYgY2xhc3M9InYiPicrKGMuY2FuZGlkYXRlc3x8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPicrKGMuc3Ryb25nfHwwKSsnIHN0cm9uZzwvZGl2PjwvZGl2PicrCiAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+QW5jaG9yPC9kaXY+PGRpdiBjbGFzcz0idiI+JysoYy53aXRoU2hhcnB8fDApKycvJysoYy5saW5lZHx8MCkrJzwvZGl2PjxkaXYgY2xhc3M9InMiPmdhbWVzIHcvIFBpbm5hY2xlPC9kaXY+PC9kaXY+JysKICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5BcmJzPC9kaXY+PGRpdiBjbGFzcz0idiIgc3R5bGU9ImNvbG9yOicrKChFVkQuYXJic3x8W10pLmxlbmd0aD8idmFyKC0tZ3JlZW4pIjoidmFyKC0tbXV0ZWQpIikrJyI+JysoKEVWRC5hcmJzfHxbXSkubGVuZ3RoKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+dHdvLXdheSBNTDwvZGl2PjwvZGl2Pic7CiAgaWYoRVZELmNmZyl7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LWZsb29yIikudGV4dENvbnRlbnQ9RVZELmNmZy5taW47ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImV2LWdhcCIpLnRleHRDb250ZW50PUVWRC5jZmcuc3Ryb25nR2FwO30KICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiZXYtYXJicyIpLmlubmVySFRNTD0oRVZELmFyYnN8fFtdKS5tYXAoZnVuY3Rpb24oYSl7CiAgICByZXR1cm4gJzxkaXYgY2xhc3M9ImNhcmQiIHN0eWxlPSJib3JkZXI6MXB4IHNvbGlkIHJnYmEoMjQsMTg0LDEyNCwuNCkiPjxiIHN0eWxlPSJmb250LXNpemU6MTJweDtjb2xvcjp2YXIoLS1ncmVlbikiPkFSQiArJythLmFyYlBjdC50b0ZpeGVkKDIpKyclPC9iPjxkaXYgc3R5bGU9ImZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLWRpbSk7bWFyZ2luLXRvcDozcHgiPicrc2hvcnROYW1lKGEuYXdheSkrJyAnK2ZtdEFtKGEubGVnQS5vZGRzKSsnIEAgJythLmxlZ0EuYm9vaysnICZuYnNwOy8mbmJzcDsgJytzaG9ydE5hbWUoYS5ob21lKSsnICcrZm10QW0oYS5sZWdILm9kZHMpKycgQCAnK2EubGVnSC5ib29rKyc8L2Rpdj48L2Rpdj4nOwogIH0pLmpvaW4oIiIpOwogIHZhciByb3dzPShFVkQucm93c3x8W10pLmZpbHRlcihmdW5jdGlvbihyKXtpZihFVkYuc3RyaWN0JiYhci5zdHJvbmcpcmV0dXJuIGZhbHNlO2lmKHIuZXZQY3Q8RVZGLm1pbilyZXR1cm4gZmFsc2U7cmV0dXJuIHRydWU7fSk7CiAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1yb3dzIik7CiAgaWYoIXJvd3MubGVuZ3RoKXsKICAgIHZhciBpbm5lcjsKICAgIGlmKCEoRVZELnJvd3N8fFtdKS5sZW5ndGgpe2lubmVyPUVWRC5ub3RlPygnPGI+Tm8gY2FuZGlkYXRlcy48L2I+PGJyPjxicj4nK0VWRC5ub3RlKTooIWMubGluZWQ/JzxiPk5vIGxpbmVkIGdhbWVzIG9uIHRoZSBib2FyZC48L2I+PGJyPjxicj5UaGUgc2NyZWVuIHBvcHVsYXRlcyB3aGVuIGJvb2tzIHBvc3Qgc2xhdGVzLic6KCFjLndpdGhTaGFycD8nPGI+Tm8gUGlubmFjbGUgYW5jaG9ycyB5ZXQuPC9iPjxicj48YnI+UGlubmFjbGUgdHlwaWNhbGx5IHBvc3RzIGNsb3NlciB0byB0aXA7IHRoZSBzY3JlZW4gbmVlZHMgaXRzIG5vLXZpZyBsaW5lIGFzIHRoZSBmYWlyIGJhc2VsaW5lLic6JzxiPk5vICtFViBmb3VuZCBhYm92ZSB0aGUgJysoRVZELmNmZz9FVkQuY2ZnLm1pbjoyKSsnJSBmbG9vci48L2I+PGJyPjxicj5SZXRhaWwgaXMgaW4gbGluZSB3aXRoIFBpbm5hY2xlIHJpZ2h0IG5vdy4nKSk7fQogICAgZWxzZSBpbm5lcj0oRVZELnJvd3MubGVuZ3RoKSsnIGNhbmRpZGF0ZScrKEVWRC5yb3dzLmxlbmd0aD4xPyJzIjoiIikrJyBoaWRkZW4gYnkgZmlsdGVycyDigJQgdG9nZ2xlIFN0cm9uZyBvbmx5IG9yIGxvd2VyIG1pbiBFVi4nOwogICAgZWwuaW5uZXJIVE1MPSc8ZGl2IGNsYXNzPSJlbXB0eSI+Jytpbm5lcisnPC9kaXY+JztyZXR1cm47CiAgfQogIGVsLmlubmVySFRNTD1yb3dzLm1hcChldlJvdykuam9pbigiIik7Cn0KZnVuY3Rpb24gbG9hZEV2KCl7CiAgdmFyIHN0PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJldi1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBTY2FubmluZyB2cyBQaW5uYWNsZeKApic7CiAgZmV0Y2goIi9hcGkvZXYiKS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGQpewogICAgaWYoZC5vaz09PWZhbHNlKXRocm93IG5ldyBFcnJvcihkLmVycm9yfHwiZXYgZmFpbGVkIik7CiAgICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjtFVkQ9ZDtyZW5kZXJFdigpOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3N0LmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLXJlZFRleHQpIj7imqAgJytlLm1lc3NhZ2UrJzwvc3Bhbj4nO30pOwp9CmZ1bmN0aW9uIHNwYXJrU3ZnKGRhaWx5KXsKICB2YXIgdz0zMDAsaD02NCxwYWQ9NSx2YWxzPWRhaWx5Lm1hcChmdW5jdGlvbih4KXtyZXR1cm4geC5jdW07fSk7CiAgdmFyIG1uPU1hdGgubWluKDAsTWF0aC5taW4uYXBwbHkobnVsbCx2YWxzKSksbXg9TWF0aC5tYXgoMCxNYXRoLm1heC5hcHBseShudWxsLHZhbHMpKTsKICBpZihteD09PW1uKW14PW1uKzE7CiAgZnVuY3Rpb24gWChpKXtyZXR1cm4gcGFkK2kqKHctMipwYWQpLyhkYWlseS5sZW5ndGgtMSk7fQogIGZ1bmN0aW9uIFkodil7cmV0dXJuIGgtcGFkLSh2LW1uKSooaC0yKnBhZCkvKG14LW1uKTt9CiAgdmFyIGQ9ZGFpbHkubWFwKGZ1bmN0aW9uKHgsaSl7cmV0dXJuIChpPyJMIjoiTSIpK1goaSkudG9GaXhlZCgxKSsiICIrWSh4LmN1bSkudG9GaXhlZCgxKTt9KS5qb2luKCIgIik7CiAgdmFyIGNvbD12YWxzW3ZhbHMubGVuZ3RoLTFdPj0wPyJ2YXIoLS1ncmVlbikiOiJ2YXIoLS1yZWRUZXh0KSI7CiAgcmV0dXJuICc8c3ZnIHZpZXdCb3g9IjAgMCAnK3crJyAnK2grJyIgc3R5bGU9IndpZHRoOjEwMCU7aGVpZ2h0OjY0cHg7ZGlzcGxheTpibG9jazttYXJnaW4tdG9wOjZweCI+PGxpbmUgeDE9IjAiIHkxPSInK1koMCkudG9GaXhlZCgxKSsnIiB4Mj0iJyt3KyciIHkyPSInK1koMCkudG9GaXhlZCgxKSsnIiBzdHJva2U9InZhcigtLWJvcmRlcikiIHN0cm9rZS13aWR0aD0iMSIvPjxwYXRoIGQ9IicrZCsnIiBmaWxsPSJub25lIiBzdHJva2U9IicrY29sKyciIHN0cm9rZS13aWR0aD0iMiIgc3Ryb2tlLWxpbmVqb2luPSJyb3VuZCIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIi8+PC9zdmc+JzsKfQpmdW5jdGlvbiBiZihtLGJ0bil7QkZJTFQ9bTtCU0hPVz0yNTtkb2N1bWVudC5xdWVyeVNlbGVjdG9yQWxsKCIjYi1maWx0IC5jaGlwIikuZm9yRWFjaChmdW5jdGlvbihiKXtiLmNsYXNzTGlzdC5yZW1vdmUoIm9uIik7fSk7YnRuLmNsYXNzTGlzdC5hZGQoIm9uIik7cmVuZGVyUmVjZW50KCk7fQpmdW5jdGlvbiByZW5kZXJSZWNlbnQoKXsKICBpZighUkMpcmV0dXJuOwogIHZhciBsaXN0PVJDLnJlY2VudHx8W107CiAgaWYoQkZJTFQhPT0iQUxMIilsaXN0PWxpc3QuZmlsdGVyKGZ1bmN0aW9uKHApe3JldHVybiBwLm1rdD09PUJGSUxUO30pOwogIHZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1yZWNlbnQiKTsKICBpZighbGlzdC5sZW5ndGgpe2VsLmlubmVySFRNTD0nPGRpdiBjbGFzcz0iZW1wdHkiPk5vdGhpbmcgZ3JhZGVkJysoQkZJTFQhPT0iQUxMIj8iIGZvciAiK0JGSUxUOiIiKSsnIHlldCDigJQgcmVzdWx0cyBsYW5kIH4yaCBhZnRlciBmaW5hbC48L2Rpdj4nO3JldHVybjt9CiAgdmFyIGh0bWw9bGlzdC5zbGljZSgwLEJTSE9XKS5tYXAoZ3JhZGVkUm93KS5qb2luKCIiKTsKICBpZihsaXN0Lmxlbmd0aD5CU0hPVylodG1sKz0nPGJ1dHRvbiBjbGFzcz0ibW9yZSIgb25jbGljaz0iQlNIT1crPTI1O3JlbmRlclJlY2VudCgpIj5TaG93IG1vcmUgKCcrKGxpc3QubGVuZ3RoLUJTSE9XKSsnKTwvYnV0dG9uPic7CiAgZWwuaW5uZXJIVE1MPWh0bWw7Cn0KZnVuY3Rpb24gY2x2U3RyKHApe2lmKCFwLmNsdilyZXR1cm4gIlx1MjAxNCI7dmFyIHY9cC5jbHYucHRzIT1udWxsP3AuY2x2LnB0czpwLmNsdi5wcDtyZXR1cm4gKHY+MD8iKyI6IiIpK3YrKHAuY2x2LnB0cyE9bnVsbD8iIHB0cyI6IiBwcCIpO30KZnVuY3Rpb24gcGlja0NhcmQocCl7CiAgcmV0dXJuICc8ZGl2IGNsYXNzPSJnY2FyZCI+PGRpdiBjbGFzcz0iZy10b3AiPjxkaXYgY2xhc3M9ImctdGVhbXMiPicrc2hvcnROYW1lKHAuYXdheSkrJzxzcGFuIGNsYXNzPSJhdCI+QDwvc3Bhbj4nK3Nob3J0TmFtZShwLmhvbWUpKyc8L2Rpdj48ZGl2IGNsYXNzPSJnLW1ldGEiPjxzcGFuIGNsYXNzPSJ0YWcgdGFnLXRpbWUiPicrdGlwVGltZShwLmNvbW1lbmNlKSsnPC9zcGFuPjxzcGFuIGNsYXNzPSJ0YWcgdGFnLWJrIj4nK3AuYm9vaysnPC9zcGFuPjwvZGl2PjwvZGl2PicrCiAgJzxkaXYgY2xhc3M9ImctcHJvaiI+PHNwYW4+PGI+JytwLm1rdCsnICcrcC5sYWJlbCsnPC9iPjwvc3Bhbj48c3Bhbj5lZGdlIDxiIGNsYXNzPSJtb25vIj4nKyhwLmVkZ2UqMTAwKS50b0ZpeGVkKDEpKyclPC9iPjwvc3Bhbj48c3Bhbj5zdGFrZSA8YiBjbGFzcz0ibW9ubyI+JytwLnN0YWtlVSsndTwvYj48L3NwYW4+PHNwYW4+bW9kZWwgPGIgY2xhc3M9Im1vbm8iPicrKHAucE1vZGVsKjEwMCkudG9GaXhlZCgwKSsnJTwvYj48L3NwYW4+PC9kaXY+PC9kaXY+JzsKfQpmdW5jdGlvbiBncmFkZWRSb3cocCl7CiAgdmFyIGNvbD1wLnN0YXR1cz09PSJ3b24iPyJ2YXIoLS1ncmVlbikiOnAuc3RhdHVzPT09Imxvc3QiPyJ2YXIoLS1yZWRUZXh0KSI6InZhcigtLWRpbSkiOwogIHZhciB1PXAucmVzdWx0PygocC5yZXN1bHQudW5pdHM+MD8iKyI6IiIpK3AucmVzdWx0LnVuaXRzLnRvRml4ZWQoMikrInUiKToiIjsKICByZXR1cm4gJzxkaXYgY2xhc3M9InNyb3ciPjxkaXY+PGRpdiBjbGFzcz0idCI+JytwLm1rdCsnICcrcC5sYWJlbCsnIDxzcGFuIHN0eWxlPSJjb2xvcjonK2NvbCsnO2ZvbnQtd2VpZ2h0OjgwMCI+JytwLnN0YXR1cy50b1VwcGVyQ2FzZSgpKyc8L3NwYW4+PC9kaXY+PGRpdiBjbGFzcz0ic3QiPicrc2hvcnROYW1lKHAuYXdheSkrJyBAICcrc2hvcnROYW1lKHAuaG9tZSkrJyBcdTAwYjcgQ0xWICcrY2x2U3RyKHApKyc8L2Rpdj48L2Rpdj48ZGl2IGNsYXNzPSJzYyIgc3R5bGU9ImNvbG9yOicrY29sKyciPicrdSsnPC9kaXY+PC9kaXY+JzsKfQpmdW5jdGlvbiBsb2FkQmV0cygpewogIHZhciBzdD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYmV0cy1zdGF0dXMiKTtzdC5zdHlsZS5kaXNwbGF5PSJibG9jayI7c3QuaW5uZXJIVE1MPSc8c3BhbiBjbGFzcz0ic3BpbiI+PC9zcGFuPiBHcmFkaW5nICYgbG9hZGluZ1x1MjAyNic7CiAgZmV0Y2goIi9hcGkvdHJhY2svZ3JhZGUiLHttZXRob2Q6IlBPU1QifSkuY2F0Y2goZnVuY3Rpb24oKXtyZXR1cm4gbnVsbDt9KS50aGVuKGZ1bmN0aW9uKCl7CiAgICByZXR1cm4gUHJvbWlzZS5hbGwoW2ZldGNoKCIvYXBpL3BpY2tzIikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSksZmV0Y2goIi9hcGkvdHJhY2svcmVjb3JkP249MTAwIikudGhlbihmdW5jdGlvbihyKXtyZXR1cm4gci5qc29uKCk7fSldKTsKICB9KS50aGVuKGZ1bmN0aW9uKHJlcyl7CiAgICBzdC5zdHlsZS5kaXNwbGF5PSJub25lIjsKICAgIHZhciBwaz1yZXNbMF0scmM9cmVzWzFdLFI9KHJjLnJlY29yZCYmcmMucmVjb3JkLkFMTCl8fHt9OwogICAgaWYocGsua2VsbHkpZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItbWF4dSIpLnRleHRDb250ZW50PXBrLmtlbGx5Lm1heFU7CiAgICB2YXIgbmV0Q29sPVIubmV0PjA/InZhcigtLWdyZWVuKSI6KFIubmV0PDA/InZhcigtLXJlZFRleHQpIjoidmFyKC0tdGV4dCkiKTsKICAgIGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJiLWtwaXMiKS5pbm5lckhUTUw9CiAgICAgICc8ZGl2IGNsYXNzPSJrcGkiPjxkaXYgY2xhc3M9ImxiIj5OZXQgdW5pdHM8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iIHN0eWxlPSJjb2xvcjonK25ldENvbCsnIj4nKyhSLm5ldD4wPyIrIjoiIikrKFIubmV0IT1udWxsP1IubmV0OjApKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhSLnN0YWtlZHx8MCkrJ3Ugc3Rha2VkPC9kaXY+PC9kaXY+JysKICAgICAgJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPlJlY29yZDwvZGl2PjxkaXYgY2xhc3M9InYgbW9ubyI+JysoUi53fHwwKSsnLScrKFIubHx8MCkrKFIucD8nLScrUi5wOicnKSsnPC9kaXY+PGRpdiBjbGFzcz0icyI+JysoUi5vcGVufHwwKSsnIG9wZW4nKyhyYy5wZW5kaW5nR3JhZGU/JyBcdTAwYjcgJytyYy5wZW5kaW5nR3JhZGUrJyBhd2FpdGluZyBncmFkZSc6JycpKyc8L2Rpdj48L2Rpdj4nKwogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+Uk9JPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhSLnJvaSE9bnVsbD8oUi5yb2kqMTAwKS50b0ZpeGVkKDEpKyclJzonXHUyMDE0JykrJzwvZGl2PjxkaXYgY2xhc3M9InMiPmdyYWRlZCBzdGFrZXM8L2Rpdj48L2Rpdj4nKwogICAgICAnPGRpdiBjbGFzcz0ia3BpIj48ZGl2IGNsYXNzPSJsYiI+Q0xWIGJlYXQ8L2Rpdj48ZGl2IGNsYXNzPSJ2IG1vbm8iPicrKFIuYmVhdCE9bnVsbD8oUi5iZWF0KjEwMCkudG9GaXhlZCgwKSsnJSc6J1x1MjAxNCcpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKyhSLmNsdk58fDApKycgd2l0aCBDTFY8L2Rpdj48L2Rpdj4nOwogICAgZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoImItb3BlbiIpLmlubmVySFRNTD0ocGsub3BlbiYmcGsub3Blbi5sZW5ndGgpP3BrLm9wZW4ubWFwKHBpY2tDYXJkKS5qb2luKCIiKTonPGRpdiBjbGFzcz0iZW1wdHkiPjxiPk5vIG9wZW4gcGlja3MuPC9iPjxicj48YnI+UGlja3MgYXV0by1sb2cgd2hlbiBhIG1vZGVsZWQgbWFya2V0IGNsZWFycyBpdHMgZmxvb3IgKE1MICcrVEguTUwrJyUgLyBTUFIgJytUSC5TUFIrJyUgLyBUT1QgJytUSC5UT1QrJyUpLjwvZGl2Pic7CiAgICBkb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1ta3RzIikuaW5uZXJIVE1MPVsiTUwiLCJTUFIiLCJUT1QiXS5tYXAoZnVuY3Rpb24obSl7CiAgICAgIHZhciByPShyYy5yZWNvcmQmJnJjLnJlY29yZFttXSl8fHt9OwogICAgICByZXR1cm4gJzxkaXYgY2xhc3M9ImtwaSI+PGRpdiBjbGFzcz0ibGIiPicrbSsnPC9kaXY+PGRpdiBjbGFzcz0idiBtb25vIj4nKyhyLnd8fDApKyctJysoci5sfHwwKSsoci5wPyctJytyLnA6JycpKyc8L2Rpdj48ZGl2IGNsYXNzPSJzIj4nKygoci5uZXQ+MD8iKyI6IiIpKyhyLm5ldCE9bnVsbD9yLm5ldDowKSkrJ3UgXHUwMGI3IENMViAnKyhyLmF2Z0NsdiE9bnVsbD8oKHIuYXZnQ2x2PjA/IisiOiIiKStyLmF2Z0NsdisobT09PSJNTCI/IiBwcCI6IiBwdHMiKSk6Ilx1MjAxNCIpKyc8L2Rpdj48L2Rpdj4nOwogICAgfSkuam9pbigiIik7CiAgICBSQz1yYztCU0hPVz0yNTtyZW5kZXJSZWNlbnQoKTsKICAgIHZhciBjdj1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgiYi1jdXJ2ZSIpOwogICAgaWYocmMuZGFpbHkmJnJjLmRhaWx5Lmxlbmd0aD49Mil7Y3Yuc3R5bGUuZGlzcGxheT0iYmxvY2siO2N2LmlubmVySFRNTD0nPGIgc3R5bGU9ImZvbnQtc2l6ZToxMnB4Ij5DdW11bGF0aXZlIHVuaXRzPC9iPjxzcGFuIHN0eWxlPSJmb250LXNpemU6MTFweDtjb2xvcjp2YXIoLS1tdXRlZCkiPiBcdTAwYjcgJytyYy5kYWlseS5sZW5ndGgrJyBkYXlzPC9zcGFuPicrc3BhcmtTdmcocmMuZGFpbHkpO30KICAgIGVsc2UgY3Yuc3R5bGUuZGlzcGxheT0ibm9uZSI7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7c3Quc3R5bGUuZGlzcGxheT0iYmxvY2siO3N0LmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLXJlZFRleHQpIj5cdTI2YTAgJytlLm1lc3NhZ2UrJzwvc3Bhbj4nO30pOwp9CnZhciBSUExydW5uaW5nPWZhbHNlLFJQTHN0b3A9ZmFsc2U7CmZ1bmN0aW9uIHJwbFllYXIoKXtyZXR1cm4gcGFyc2VJbnQoZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC15ZWFyIikudmFsdWUpfHxuZXcgRGF0ZSgpLmdldEZ1bGxZZWFyKCk7fQpmdW5jdGlvbiBycGxMb2cocyxhcHBlbmQpe3ZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLWxvZyIpO2VsLnN0eWxlLmRpc3BsYXk9ImJsb2NrIjtpZihhcHBlbmQpZWwudGV4dENvbnRlbnQrPSJcbiIrcztlbHNlIGVsLnRleHRDb250ZW50PXM7ZWwuc2Nyb2xsVG9wPWVsLnNjcm9sbEhlaWdodDt9CmZ1bmN0aW9uIHJwbEJ1c3kob24pe1JQTHJ1bm5pbmc9b247WyJycGwtcGxhbiIsInJwbC1pbmdlc3QiLCJycGwtcmVzdWx0cyIsInJwbC1ydW4iLCJycGwtcmVwb3J0Il0uZm9yRWFjaChmdW5jdGlvbihpZCl7ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoaWQpLmRpc2FibGVkPW9uO30pO2RvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtc3RvcCIpLnN0eWxlLmRpc3BsYXk9b24/ImlubGluZS1mbGV4Ijoibm9uZSI7fQpmdW5jdGlvbiBycGxTdG9wRm4oKXtSUExzdG9wPXRydWU7cnBsTG9nKCJTdG9wcGluZyBhZnRlciBjdXJyZW50IHJlcXVlc3RcdTIwMjYiLHRydWUpO30KZnVuY3Rpb24gcnBsVG9nZ2xlQ3N2KCl7dmFyIHc9ZG9jdW1lbnQuZ2V0RWxlbWVudEJ5SWQoInJwbC1jc3Z3cmFwIik7dy5zdHlsZS5kaXNwbGF5PXcuc3R5bGUuZGlzcGxheT09PSJub25lIj8iYmxvY2siOiJub25lIjt9CmZ1bmN0aW9uIHJwbFBsYW4oKXsKICB2YXIgeT1ycGxZZWFyKCk7cnBsTG9nKCJQbGFubmluZyAiK3krIlx1MjAyNiIpOwogIGZldGNoKCIvYXBpL3JlcGxheS9wbGFuP3llYXI9Iit5KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGopewogICAgaWYoIWoub2spcmV0dXJuIHJwbExvZygiUGxhbiBlcnJvcjogIisoai5lcnJvcnx8Ij8iKSk7CiAgICB2YXIgZml0cz1qLmZpdHM9PT10cnVlPyJcdTI3MTMgZml0cyI6KGouZml0cz09PWZhbHNlPyJcdTI3MTcgZXhjZWVkcyBxdW90YSI6InF1b3RhIHVua25vd24gXHUyMDE0IG9wZW4gR2FtZXMgb25jZSB0byByZWFkIGl0Iik7CiAgICBycGxMb2coeSsiOiAgIitqLmZyb20rIiBcdTIxOTIgIitqLnRvKyJcbiIrai5kYXlzKyIgZGF5cyBcdTAwZDcgIitqLnNuYXBzUGVyRGF5KyIgc25hcHMgPSAiK2ouY3JlZGl0c05lZWRlZCsiIGNyZWRpdHNcbnF1b3RhICIrKGoucXVvdGFSZW1haW5pbmchPW51bGw/ai5xdW90YVJlbWFpbmluZzoiPyIpKyIgKHNhZmV0eSAiK2ouc2FmZXR5KyIpICBcdTAwYjcgICIrZml0cyk7CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7cnBsTG9nKCJQbGFuIGZhaWxlZDogIitlLm1lc3NhZ2UpO30pOwp9CmZ1bmN0aW9uIHJwbFJlc3VsdHMoKXsKICB2YXIgeT1ycGxZZWFyKCksY3N2PWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtY3N2IikudmFsdWUudHJpbSgpOwogIHJwbExvZyhjc3Y/IkxvYWRpbmcgbWFudWFsIENTVlx1MjAyNiI6IkZldGNoaW5nIFRvcnZpayByZXN1bHRzXHUyMDI2Iik7CiAgZmV0Y2goIi9hcGkvcmVwbGF5L3Jlc3VsdHMiLHttZXRob2Q6IlBPU1QiLGhlYWRlcnM6eyJDb250ZW50LVR5cGUiOiJhcHBsaWNhdGlvbi9qc29uIn0sYm9keTpKU09OLnN0cmluZ2lmeShjc3Y/e3llYXI6eSxjc3Y6Y3N2fTp7eWVhcjp5fSl9KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKGopewogICAgaWYoIWoub2spcmV0dXJuIHJwbExvZygiUmVzdWx0cyBlcnJvcjogIisoai5lcnJvcnx8Ij8iKSx0cnVlKTsKICAgIHJwbExvZygiXHUyNzEzIFJlc3VsdHMgbG9hZGVkOiAiK2ouZ2FtZXMrIiBnYW1lcyAoIitqLm1vZGUrIikiLHRydWUpO3JwbFN0YXR1cygpOwogIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3JwbExvZygiUmVzdWx0cyBmYWlsZWQ6ICIrZS5tZXNzYWdlLHRydWUpO30pOwp9CmZ1bmN0aW9uIHJwbExvb3Aoa2luZCl7CiAgaWYoUlBMcnVubmluZylyZXR1cm47CiAgdmFyIHk9cnBsWWVhcigpO1JQTHN0b3A9ZmFsc2U7cnBsQnVzeSh0cnVlKTsKICB2YXIgZXA9Ii9hcGkvcmVwbGF5LyIra2luZCxib2R5PWtpbmQ9PT0iaW5nZXN0Ij97eWVhcjp5LGRheXM6MTV9Ont5ZWFyOnksZGF5czozMH0saXRlcj0wLHQwPURhdGUubm93KCk7CiAgcnBsTG9nKChraW5kPT09ImluZ2VzdCI/IkluZ2VzdGluZyAiOiJTaW11bGF0aW5nICIpK3krIlx1MjAyNiIpOwogIGZ1bmN0aW9uIHN0ZXAoKXsKICAgIGlmKFJQTHN0b3Ape3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNWEwIFN0b3BwZWQgYWZ0ZXIgIitpdGVyKyIgYmF0Y2goZXMpLiIsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgIGl0ZXIrKzsKICAgIGZldGNoKGVwLHttZXRob2Q6IlBPU1QiLGhlYWRlcnM6eyJDb250ZW50LVR5cGUiOiJhcHBsaWNhdGlvbi9qc29uIn0sYm9keTpKU09OLnN0cmluZ2lmeShib2R5KX0pLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24oail7CiAgICAgIGlmKCFqLm9rJiZqLnByb2Nlc3NlZERheXM9PW51bGwpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiRXJyb3I6ICIrKGouZXJyb3J8fCI/IiksdHJ1ZSk7cmV0dXJuO30KICAgICAgdmFyIHNlY3M9TWF0aC5yb3VuZCgoRGF0ZS5ub3coKS10MCkvMTAwMCk7CiAgICAgIGlmKGtpbmQ9PT0iaW5nZXN0Iil7CiAgICAgICAgcnBsTG9nKCJcdTAwYjcgIitqLm5leHREYXRlKyIgICAoIisoai50b3RhbENyZWRpdHMhPW51bGw/ai50b3RhbENyZWRpdHMrIiBjciI6Ij8iKSsiLCBiYXRjaCAiK2l0ZXIrIikiLHRydWUpOwogICAgICAgIGlmKGouaGFsdGVkKXtycGxCdXN5KGZhbHNlKTtycGxMb2coIlx1MjZhMCBIYWx0ZWQ6ICIrai5oYWx0ZWQsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgICAgICBpZihqLmRvbmUpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNzEzIEluZ2VzdCBjb21wbGV0ZSB0aHJvdWdoICIrai5uZXh0RGF0ZSsiICBcdTIwMTQgICIrc2VjcysicyIsdHJ1ZSk7cnBsU3RhdHVzKCk7cmV0dXJuO30KICAgICAgfWVsc2V7CiAgICAgICAgcnBsTG9nKCJcdTAwYjcgIitqLm5leHREYXRlKyIgICAoIitqLnNpbW1lZCsiIHNpbW1lZCwgYmF0Y2ggIitpdGVyKyIpIix0cnVlKTsKICAgICAgICBpZihqLmRvbmUpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiXHUyNzEzIFNpbSBjb21wbGV0ZSB0aHJvdWdoICIrai5uZXh0RGF0ZSsiICgiK2ouc2ltbWVkKyIgZ2FtZXMpICBcdTIwMTQgICIrc2VjcysicyIsdHJ1ZSk7cnBsU3RhdHVzKCk7cnBsUmVwb3J0KGZhbHNlKTtyZXR1cm47fQogICAgICB9CiAgICAgIHN0ZXAoKTsKICAgIH0pLmNhdGNoKGZ1bmN0aW9uKGUpe3JwbEJ1c3koZmFsc2UpO3JwbExvZygiUmVxdWVzdCBmYWlsZWQ6ICIrZS5tZXNzYWdlLHRydWUpO30pOwogIH0KICBzdGVwKCk7Cn0KZnVuY3Rpb24gcnBsU3RhdHVzKCl7CiAgdmFyIHk9cnBsWWVhcigpOwogIGZldGNoKCIvYXBpL3JlcGxheS9zdGF0dXM/eWVhcj0iK3kpLnRoZW4oZnVuY3Rpb24ocil7cmV0dXJuIHIuanNvbigpO30pLnRoZW4oZnVuY3Rpb24ocnMpewogICAgdmFyIGVsPWRvY3VtZW50LmdldEVsZW1lbnRCeUlkKCJycGwtc3RhdHVzIik7CiAgICBpZihycyYmcnMuY3Vyc29yKXsKICAgICAgZWwuaW5uZXJIVE1MPSdJbmdlc3QgPHNwYW4gY2xhc3M9Im1vbm8iPicrKHJzLmN1cnNvci5pbmdlc3ROZXh0fHxycy5jdXJzb3IuZnJvbSkrJzwvc3Bhbj4nKyhycy5jdXJzb3IuZG9uZT8nIChkb25lKSc6JycpKyhycy5jdXJzb3IuY3JlZGl0cz8oJyBcdTAwYjcgJytycy5jdXJzb3IuY3JlZGl0cysnIGNyIHVzZWQnKTonJykrKHJzLnJlc3VsdHM/KCcgXHUwMGI3IHJlc3VsdHMgJytycy5yZXN1bHRzLmdhbWVzKycgKCcrcnMucmVzdWx0cy5tb2RlKycpJyk6JyBcdTAwYjcgPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLWFtYmVyKSI+cmVzdWx0cyBub3QgbG9hZGVkPC9zcGFuPicpKycgXHUwMGI3IHNpbSAnKyhycy5jdXJzb3Iuc2ltTmV4dD8nPHNwYW4gY2xhc3M9Im1vbm8iPicrcnMuY3Vyc29yLnNpbU5leHQrJzwvc3Bhbj4nOidub3Qgc3RhcnRlZCcpOwogICAgfSBlbHNlIGVsLmlubmVySFRNTD0nPHNwYW4gc3R5bGU9ImNvbG9yOnZhcigtLW11dGVkKSI+Tm90IHN0YXJ0ZWQgXHUyMDE0IFBsYW4gdG8gc2l6ZSB0aGUgc3BlbmQsIHRoZW4gSW5nZXN0IFx1MjE5MiBSZXN1bHRzIFx1MjE5MiBSdW4uPC9zcGFuPic7CiAgfSkuY2F0Y2goZnVuY3Rpb24oKXt9KTsKfQpmdW5jdGlvbiBycGxSZXBvcnQodG9Mb2cpewogIHZhciB5PXJwbFllYXIoKTsKICBmZXRjaCgiL2FwaS9yZXBsYXkvcmVwb3J0P3llYXI9Iit5KS50aGVuKGZ1bmN0aW9uKHIpe3JldHVybiByLmpzb24oKTt9KS50aGVuKGZ1bmN0aW9uKHJwKXsKICAgIHZhciBlbD1kb2N1bWVudC5nZXRFbGVtZW50QnlJZCgicnBsLXJlcG9ydCIpOwogICAgaWYocnAmJnJwLm9rKXsKICAgICAgdmFyIEE9cnAucGlja3MuQUxMLHJlYz1ycC5yZWNvbW1lbmR8fHt9OwogICAgICBlbC5pbm5lckhUTUw9JzxkaXYgc3R5bGU9ImJvcmRlci10b3A6MXB4IHNvbGlkIHZhcigtLWJvcmRlcik7bWFyZ2luLXRvcDo3cHg7cGFkZGluZy10b3A6N3B4Ij4nK3JwLnllYXIrJyBcdTAwYjcgJytycC5jb3ZlcmFnZS5zaW1tZWQrJyBzaW1tZWQgXHUwMGI3IHBpY2tzIDxiPicrQS5yZWNvcmQrJzwvYj4gKCcrKEEudW5pdHM+MD8iKyI6IiIpK0EudW5pdHMrJ3UsIFJPSSAnKyhBLnJvaSE9bnVsbD8oQS5yb2kqMTAwKS50b0ZpeGVkKDEpKyclJzonXHUyMDE0JykrJykgXHUwMGI3IENMViBiZWF0ICcrKEEuY2x2QmVhdCE9bnVsbD8oQS5jbHZCZWF0KjEwMCkudG9GaXhlZCgwKSsnJSc6J1x1MjAxNCcpKwogICAgICAgICc8YnI+bWFyZ2luIFNEIDxiPicrKHJwLnJlc2lkdWFscy5tYXJnaW4/cnAucmVzaWR1YWxzLm1hcmdpbi5zZDonXHUyMDE0JykrJzwvYj4gXHUwMGI3IHRvdGFscyBiaWFzIDxiPicrKHJlYy50b3RhbHNCaWFzIT1udWxsPygocmVjLnRvdGFsc0JpYXM+MD8iKyI6IiIpK3JlYy50b3RhbHNCaWFzKTonXHUyMDE0JykrJzwvYj4gXHUwMGI3IEhDQSBpbXBsaWVkIDxiPicrKHJlYy5IQ0FfaW1wbGllZCE9bnVsbD9yZWMuSENBX2ltcGxpZWQ6J1x1MjAxNCcpKyc8L2I+JysKICAgICAgICAnPGJyPjxzcGFuIHN0eWxlPSJjb2xvcjp2YXIoLS1tdXRlZCkiPkZ1bGwgSlNPTjogPHNwYW4gY2xhc3M9Im1vbm8iPi9hcGkvcmVwbGF5L3JlcG9ydD95ZWFyPScrcnAueWVhcisnPC9zcGFuPiBcdTAwYjcgcmVjb21tZW5kYXRpb25zIGRpc3BsYXktb25seTwvc3Bhbj48L2Rpdj4nOwogICAgICBpZih0b0xvZyl7CiAgICAgICAgdmFyIHN3PXJwLnN3ZWVwfHx7fTsKICAgICAgICBycGxMb2coIlJlcG9ydCAiK3JwLnllYXIrIjpcbiAgcGlja3MgIitBLnJlY29yZCsiICAiKyhBLnVuaXRzPjA/IisiOiIiKStBLnVuaXRzKyJ1ICBST0kgIisoQS5yb2khPW51bGw/KEEucm9pKjEwMCkudG9GaXhlZCgxKSsiJSI6Ilx1MjAxNCIpKyIgIENMViBiZWF0ICIrKEEuY2x2QmVhdCE9bnVsbD8oQS5jbHZCZWF0KjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKwogICAgICAgICAgIlxuICBieSBlZGdlOiAiK1siMi00IiwiNC02IiwiNi04IiwiOCsiXS5tYXAoZnVuY3Rpb24oayl7dmFyIHM9c3dba118fHt9O3JldHVybiBrKyIgIisocy5yb2khPW51bGw/KHMucm9pKjEwMCkudG9GaXhlZCgwKSsiJSI6Ilx1MjAxNCIpKyIoIisocy5ufHwwKSsiKSI7fSkuam9pbigiICAiKSsKICAgICAgICAgICJcbiAgcmVzaWQgU0QgbWFyZ2luICIrKHJwLnJlc2lkdWFscy5tYXJnaW4/cnAucmVzaWR1YWxzLm1hcmdpbi5zZDoiXHUyMDE0IikrIiB0b3RhbCAiKyhycC5yZXNpZHVhbHMudG90YWw/cnAucmVzaWR1YWxzLnRvdGFsLnNkOiJcdTIwMTQiKSsiICBCcmllciAiKyhycC5jYWxpYnJhdGlvbj9ycC5jYWxpYnJhdGlvbi5icmllcjoiXHUyMDE0IikrCiAgICAgICAgICAiXG4gIHJlYzogU0QgIityZWMuU0QrIiAgVE9UX1NEICIrcmVjLlRPVF9TRCsiICB0b3RhbHNCaWFzICIrcmVjLnRvdGFsc0JpYXMrIiAgSENBICIrcmVjLkhDQV9pbXBsaWVkKTsKICAgICAgfQogICAgfSBlbHNlIHsgZWwuaW5uZXJIVE1MPScnOyBpZih0b0xvZylycGxMb2coIk5vIHJlcG9ydCB5ZXQgXHUyMDE0IGluZ2VzdCwgbG9hZCByZXN1bHRzLCB0aGVuIHJ1bi4iLHRydWUpOyB9CiAgfSkuY2F0Y2goZnVuY3Rpb24oZSl7aWYodG9Mb2cpcnBsTG9nKCJSZXBvcnQgZmFpbGVkOiAiK2UubWVzc2FnZSx0cnVlKTt9KTsKfQpmdW5jdGlvbiBsb2FkQWxsKGZvcmNlKXtsb2FkU2xhdGUoZm9yY2UpO30KbG9hZEFsbCh0cnVlKTsKc2V0SW50ZXJ2YWwoZnVuY3Rpb24oKXtsb2FkU2xhdGUoZmFsc2UpO30sMTgwMDAwKTsKPC9zY3JpcHQ+CjwvYm9keT4KPC9odG1sPgo=", "base64").toString("utf8");
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
