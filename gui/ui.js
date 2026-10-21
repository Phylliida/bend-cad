// bend-cad sketcher: the page. Drawing, selection, constraints, and the
// certify loop (relax, order, solve on the server, read the answer back).
import * as M from "./model.js";
import * as PL from "./pipeline.js";

const $ = id => document.getElementById(id);
const cv = $("cv"), ctx = cv.getContext("2d");

// Icons: 24 x 24 line drawings
const ICON = {
  select: '<path d="M6 3l12 9-5.5 1.2L10 19z"/>',
  point: '<circle cx="12" cy="12" r="3"/><path d="M12 4v3M12 17v3M4 12h3M17 12h3"/>',
  line: '<path d="M5 19L19 5"/><circle cx="5" cy="19" r="1.6"/><circle cx="19" cy="5" r="1.6"/>',
  circle: '<circle cx="12" cy="12" r="7.5"/><circle cx="12" cy="12" r="1.2"/>',
  coincident: '<circle cx="10" cy="12" r="5"/><circle cx="14" cy="12" r="5"/>',
  horizontal: '<path d="M4 12h16"/><path d="M4 9v6M20 9v6"/>',
  vertical: '<path d="M12 4v16"/><path d="M9 4h6M9 20h6"/>',
  parallel: '<path d="M6 19L12 5M12 19L18 5"/>',
  perpendicular: '<path d="M5 19h14M12 19V5"/><path d="M12 15h4v4"/>',
  equal: '<path d="M6 10h12M6 14h12"/>',
  concentric: '<circle cx="12" cy="12" r="7.5"/><circle cx="12" cy="12" r="3.5"/>',
  midpoint: '<path d="M4 16L20 8"/><path d="M12 9l2 4h-4z"/>',
  symmetric: '<path d="M12 4v16" stroke-dasharray="2 2"/><circle cx="6.5" cy="12" r="2"/><circle cx="17.5" cy="12" r="2"/>',
  fix: '<path d="M8 11V8a4 4 0 0 1 8 0v3"/><rect x="6" y="11" width="12" height="9" rx="1.5"/>',
  dimension: '<path d="M4 17h16"/><path d="M4 14v6M20 14v6"/><path d="M7 15l-3 2 3 2M17 15l3 2-3 2"/>',
  construction: '<path d="M5 19L19 5" stroke-dasharray="3 3"/>',
};

const TOOLS = [
  { id: "select", label: "Select", key: "S" },
  { id: "point", label: "Point", key: "P" },
  { id: "line", label: "Line", key: "L" },
  { id: "circle", label: "Circle", key: "C" },
];

const CTOOLS = [
  { id: "dimension", label: "Dimension", key: "D" },
  { id: "coincident", label: "Coincident", key: "I" },
  { id: "horizontal", label: "Horizontal", key: "H" },
  { id: "vertical", label: "Vertical", key: "V" },
  { id: "parallel", label: "Parallel", key: "" },
  { id: "perpendicular", label: "Perpendicular", key: "" },
  { id: "equal", label: "Equal", key: "E" },
  { id: "concentric", label: "Concentric", key: "" },
  { id: "midpoint", label: "Midpoint", key: "" },
  { id: "symmetric", label: "Symmetric", key: "" },
  { id: "fix", label: "Fix", key: "F" },
  { id: "construction", label: "Construction", key: "Q" },
];

const TIPS = {
  dimension: "Dimension: two points or a segment (distance), a circle (radius), a point and a segment (distance to the line), two segments (angle)",
  coincident: "Coincident: two points; a point and a segment (on its line); a point and a circle (on it)",
  horizontal: "Horizontal: a segment, or two points", vertical: "Vertical: a segment, or two points",
  parallel: "Parallel: two segments", perpendicular: "Perpendicular: two segments",
  equal: "Equal: two segments (length) or two circles (radius)", concentric: "Concentric: two circles",
  midpoint: "Midpoint: a point and a segment", symmetric: "Symmetric: two points and a segment (the mirror line)",
  fix: "Fix: points, at their current positions", construction: "Construction: toggle construction geometry",
};

const HINTS = {
  select: "Select: click to select (Shift adds), drag points, segments or circles; drag empty space to box-select. Delete removes.",
  point: "Point: click to place a point.",
  line: "Line: click to start, click to end; it continues from the end. Esc or right-click stops. Clicks on points reuse them.",
  circle: "Circle: click the center (reuses a point), then click a point on the circle.",
};

// State
// -----

const S = {
  sk: M.emptySketch(),
  sel: [],            // selected entity ids, in order
  selCon: null,       // selected constraint id
  hoverCon: null,
  hover: null,
  tool: "select",
  view: { cx: 3, cy: 2, s: 60 },
  drag: null,
  pending: null,      // line/circle in progress: {kind, from: pointId}
  mouse: { x: 0, y: 0, wx: 0, wy: 0 },
  undo: [], redo: [],
  cert: { state: "idle", ok: null, red: new Set(), pinned: new Set(), status: new Map(), ms: 0, msg: "", pinsCount: 0, nvars: 0 },
  opts: { relax: true, order: true, dyadic: true, auto: true },
  seq: 0, applied: 0, inflight: false, again: false,
  space: false,
};

// Persistence (per viewer, best effort)
function save() {
  try { localStorage.setItem("bendcad.sketch", JSON.stringify(S.sk)); localStorage.setItem("bendcad.opts", JSON.stringify(S.opts)); } catch (e) {}
}
function load() {
  try {
    const o = JSON.parse(localStorage.getItem("bendcad.opts") || "null");
    if (o) Object.assign(S.opts, o);
    const sk = JSON.parse(localStorage.getItem("bendcad.sketch") || "null");
    if (sk && sk.ents) { S.sk = M.migrate(sk); return true; }
  } catch (e) {}
  return false;
}

function snapshot() {
  S.undo.push(M.clone(S.sk));
  if (S.undo.length > 200) S.undo.shift();
  S.redo = [];
}

// Geometry helpers
// ----------------

let FIND = null;
function find() { return FIND || (FIND = M.classes(S.sk)); }
function touched() { FIND = null; }
function P(e) { return M.pos(S.sk, e, find()); }
function E(id) { return M.ent(S.sk, id); }
function R(c) { return M.val(S.sk, c.r, find()); }

function toScreen(x, y) {
  const { cx, cy, s } = S.view;
  return [(x - cx) * s + cv.clientWidth / 2, cv.clientHeight / 2 - (y - cy) * s];
}
function toWorld(px, py) {
  const { cx, cy, s } = S.view;
  return [(px - cv.clientWidth / 2) / s + cx, cy - (py - cv.clientHeight / 2) / s];
}

function distSeg(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy;
  let t = L2 ? ((px - ax) * dx + (py - ay) * dy) / L2 : 0;
  t = Math.max(0, Math.min(1, t));
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
}

// the entity under the cursor (screen px), points first
function hit(px, py, kinds = ["pt", "seg", "circ"], skip = null) {
  let best = null, bd = 8;
  for (const e of S.sk.ents) {
    if (e.kind !== "pt" || !kinds.includes("pt") || e.id === skip) continue;
    const p = P(e), [x, y] = toScreen(p.x, p.y);
    const d = Math.hypot(px - x, py - y);
    if (d < bd) { bd = d; best = e; }
  }
  if (best) return best;
  bd = 6;
  for (const e of S.sk.ents) {
    if (e.kind === "seg" && kinds.includes("seg")) {
      const a = toScreen(...Object.values(P(E(e.p)))), b = toScreen(...Object.values(P(E(e.q))));
      const d = distSeg(px, py, a[0], a[1], b[0], b[1]);
      if (d < bd) { bd = d; best = e; }
    } else if (e.kind === "circ" && kinds.includes("circ")) {
      const c = P(E(e.c)), [x, y] = toScreen(c.x, c.y);
      const d = Math.abs(Math.hypot(px - x, py - y) - R(e) * S.view.s);
      if (d < bd) { bd = d; best = e; }
    }
  }
  return best;
}

// Certify loop
// ------------

function setStatus(state, text) {
  const st = $("status");
  st.className = "status " + state;
  $("status-text").textContent = text;
}

function changed(opts = {}) {
  touched();
  save();
  if (S.opts.auto || opts.force) certify(opts);
  else { S.cert.state = "stale"; setStatus("", "Changed; press Solve"); }
  render(); renderPanels();
}

async function certify(opts = {}) {
  if (S.inflight) { S.again = true; S.againOpts = opts; return; }
  if (!S.sk.ents.length) { S.cert = { ...S.cert, state: "idle", ok: null, red: new Set(), pinned: new Set(), status: new Map() }; setStatus("", "Empty sketch"); renderPanels(); return; }
  const seq = ++S.seq;
  let prep;
  try {
    prep = PL.prepare(S.sk, S.opts, opts.heavy || []);
  } catch (e) {
    setStatus("bad", "Error preparing the sketch"); console.error(e); return;
  }
  touched();
  render();
  S.inflight = true;
  setStatus("busy", "Certifying");
  $("last-in").textContent = JSON.stringify(prep.req);
  let ans;
  try {
    const r = await fetch("/api/solve", { method: "POST", body: JSON.stringify(prep.req) });
    ans = await r.json();
  } catch (e) {
    ans = { error: "no server: start it with python3 gui/serve.py" };
  }
  S.inflight = false;
  if (ans.input) $("last-in").textContent = ans.input;
  if (seq >= S.applied) {
    S.applied = seq;
    if (ans.error) {
      S.cert = { ...S.cert, state: "error", ok: null, msg: ans.error };
      setStatus("bad", "Solver error");
    } else {
      // apply only if the sketch has not been edited structurally since
      const res = PL.finish(S.sk, prep, ans);
      touched();
      S.cert = { state: ans.ok ? "ok" : "fail", ok: ans.ok, red: res.red, pinned: res.pinned, status: res.status, ms: ans.ms, pinsCount: res.pinsCount, nvars: res.nvars, residual: prep.residual, msg: "" };
      if (ans.ok) {
        const amb = countStatus("amber");
        const parts = [res.red.size ? `${res.red.size} red` : "", amb ? `${amb} redundant` : ""].filter(Boolean);
        setStatus(res.red.size ? "warn" : "ok", ["Certified" + (parts.length ? ", " + parts.join(", ") : ""), `${ans.ms} ms`].join(" · "));
      } else {
        S.cert.msg = reason(prep);
        setStatus("warn", "Not certified");
      }
    }
    render(); renderPanels();
  }
  if (S.again) { S.again = false; certify(S.againOpts || {}); }
}

function countStatus(k) {
  let n = 0;
  for (const st of S.cert.status.values()) if (st.k === k) n++;
  return n;
}

// what the solver said about a constraint, in words ("" for kept)
function statusText(con, num) {
  const st = S.cert.status.get(con.id);
  if (!st || S.cert.ok === null) return "";
  const refs = st.with.map(id => "#" + num.get(id)).filter(r => r !== "#undefined").join(", ");
  switch (st.k) {
    case "conflict":
      if (!st.with.length) return "cannot hold";
      return (S.cert.ok ? "conflicts with " : "cannot all hold with ") + refs;
    case "over": return "over-determined" + (refs ? " with " + refs : "");
    case "amber": return "redundant" + (S.cert.ok ? ", holds anyway" : "");
    case "partly": return "partly implied by earlier ones";
    default: return "";
  }
}

function statusTitle(con) {
  const st = S.cert.status.get(con.id);
  if (!st || S.cert.ok === null) return "";
  switch (st.k) {
    case "conflict": return "Red: it cannot hold together with the constraints listed (its support: drop any one of them and the rest can), and the solver leaves it out";
    case "over": return "Red: with earlier constraints it fixes more than the variables it uses can carry, so the solver leaves it out";
    case "amber": return "Redundant: every equation follows from earlier constraints and every side condition is implied; the solver drops it" + (S.cert.ok ? ", and it holds in the certified drawing" : "");
    case "partly": return "Kept: some of its equations follow from earlier constraints and are dropped from the system solved";
    default: return "";
  }
}

function reason(prep) {
  if (S.cert.red.size) return "Some constraints are red; the rest could not be certified.";
  if (S.opts.relax && prep.residual > 1e-6) return `The constraints conflict, or no solution is near the drawing: the relaxation left a residual of ${prep.residual.toExponential(1)}.`;
  if (!S.opts.dyadic && PL.hasNonDyadic(S.sk)) return "A value is not dyadic (like 3.6 or 30 degrees), and the certifying arithmetic holds dyadic constants only (Q19). Turn on 'Dimensions as dyadics'.";
  if (!S.opts.relax) return "The solver holds the free variables at their drawn values; with this drawing that may leave no regular solution nearby. Try 'Relax the drawing first'.";
  return "The solver found no regular solution near this drawing for its choice of pinned variables (for example a point exactly on a tangent, or two coincident lines). Moving the geometry slightly often helps.";
}

// Editing
// -------

function selEnts() { return S.sel.map(E).filter(Boolean); }

function addCon(kind, ents, extra = {}) {
  const dup = M.duplicateOf(S.sk, { kind, ents, driven: false, ...extra });
  if (dup) $("hint").textContent = `Already constrained: ${M.CK[kind].label} ${ents.map(entName).join(" ")} repeats #${S.sk.cons.indexOf(dup) + 1}; the solver will mark it redundant.`;
  const c = M.addConstraint(S.sk, kind, ents, extra);
  if (!S.opts.relax) { touched(); M.presatisfy(S.sk, c); }
  return c;
}

function applyConstraint(id) {
  const es = selEnts();
  const pts = es.filter(e => e.kind === "pt"), segs = es.filter(e => e.kind === "seg"), circs = es.filter(e => e.kind === "circ");
  const only = (np, ns, nc) => pts.length === np && segs.length === ns && circs.length === nc;
  const ends = s => [s.p, s.q];
  let done = false;
  const go = f => { snapshot(); f(); done = true; };
  switch (id) {
    case "coincident":
      if (pts.length >= 2 && !segs.length && !circs.length) go(() => { for (let i = 1; i < pts.length; i++) addCon("coincident", [pts[0].id, pts[i].id]); });
      else if (only(1, 1, 0)) go(() => addCon("onLine", [pts[0].id, segs[0].id]));
      else if (only(1, 0, 1)) go(() => addCon("onCircle", [pts[0].id, circs[0].id]));
      break;
    case "horizontal": case "vertical":
      if (segs.length && !pts.length && !circs.length) go(() => segs.forEach(s => addCon(id, ends(s))));
      else if (pts.length >= 2 && !segs.length && !circs.length) go(() => { for (let i = 1; i < pts.length; i++) addCon(id, [pts[0].id, pts[i].id]); });
      break;
    case "parallel": case "perpendicular":
      if (segs.length >= 2 && !pts.length && !circs.length) go(() => { for (let i = 1; i < segs.length; i++) addCon(id, [segs[0].id, segs[i].id]); });
      break;
    case "equal":
      if (segs.length >= 2 && !pts.length && !circs.length) go(() => { for (let i = 1; i < segs.length; i++) addCon("equalLength", [segs[0].id, segs[i].id]); });
      else if (circs.length >= 2 && !pts.length && !segs.length) go(() => { for (let i = 1; i < circs.length; i++) addCon("equalRadius", [circs[0].id, circs[i].id]); });
      break;
    case "concentric":
      if (circs.length >= 2 && !pts.length && !segs.length) go(() => { for (let i = 1; i < circs.length; i++) addCon("concentric", [circs[0].id, circs[i].id]); });
      break;
    case "midpoint":
      if (only(1, 1, 0)) go(() => addCon("midpoint", [pts[0].id, segs[0].id]));
      break;
    case "symmetric":
      if (only(2, 1, 0)) go(() => addCon("symmetric", [pts[0].id, pts[1].id, segs[0].id]));
      break;
    case "fix":
      if (pts.length && !segs.length && !circs.length) go(() => pts.forEach(p => { const q = P(p); addCon("fix", [p.id], { fx: round6(q.x), fy: round6(q.y) }); }));
      break;
    case "construction":
      if (es.length) go(() => { const on = !es.every(e => e.construction); es.forEach(e => { e.construction = on; }); });
      break;
    case "dimension":
      openDimension();
      return;
  }
  if (done) changed();
}

function round6(x) { return Math.round(x * 1e6) / 1e6; }
function nice(x) { return Math.round(x * 1000) / 1000; }

// which constraint tools apply to the selection
function applicable(id) {
  const es = selEnts();
  const np = es.filter(e => e.kind === "pt").length, ns = es.filter(e => e.kind === "seg").length, nc = es.filter(e => e.kind === "circ").length;
  switch (id) {
    case "coincident": return (np >= 2 && !ns && !nc) || (np === 1 && ns === 1 && !nc) || (np === 1 && nc === 1 && !ns);
    case "horizontal": case "vertical": return (ns >= 1 && !np && !nc) || (np >= 2 && !ns && !nc);
    case "parallel": case "perpendicular": return ns >= 2 && !np && !nc;
    case "equal": return (ns >= 2 && !np && !nc) || (nc >= 2 && !np && !ns);
    case "concentric": return nc >= 2 && !np && !ns;
    case "midpoint": return np === 1 && ns === 1 && !nc;
    case "symmetric": return np === 2 && ns === 1 && !nc;
    case "fix": return np >= 1 && !ns && !nc;
    case "construction": return es.length > 0;
    case "dimension": return dimensionKinds().length > 0;
  }
  return false;
}

// Dimensions
// ----------

function dimensionKinds() {
  const es = selEnts();
  const pts = es.filter(e => e.kind === "pt"), segs = es.filter(e => e.kind === "seg"), circs = es.filter(e => e.kind === "circ");
  if (pts.length === 2 && !segs.length && !circs.length) return [["distance", [pts[0].id, pts[1].id]], ["hdistance", [pts[0].id, pts[1].id]], ["vdistance", [pts[0].id, pts[1].id]]];
  if (segs.length === 1 && !pts.length && !circs.length) {
    const s = segs[0];
    return [["distance", [s.p, s.q]], ["hdistance", [s.p, s.q]], ["vdistance", [s.p, s.q]]];
  }
  if (circs.length === 1 && !pts.length && !segs.length) return [["radius", [circs[0].id]], ["diameter", [circs[0].id]]];
  if (pts.length === 1 && segs.length === 1 && !circs.length) return [["lineDistance", [pts[0].id, segs[0].id]]];
  if (segs.length === 2 && !pts.length && !circs.length) return [["angle", [segs[0].id, segs[1].id]]];
  return [];
}

function openDimension(editCon = null) {
  const kinds = editCon ? [[editCon.kind, editCon.ents]] : dimensionKinds();
  if (!kinds.length) return;
  const pop = $("pop");
  const unit = k => k === "angle" ? "degrees" : "units";
  const opts = kinds.map(([k], i) => `<option value="${i}">${M.CK[k].label}</option>`).join("");
  pop.innerHTML = `<label>${editCon ? "Edit " + M.CK[editCon.kind].label.toLowerCase() : "Dimension"}</label>
    ${kinds.length > 1 ? `<select id="pop-kind">${opts}</select>` : `<div class="note">${M.CK[kinds[0][0]].label}</div>`}
    <div class="row"><input id="pop-val" type="text" inputmode="decimal"><span class="note" id="pop-unit" style="align-self:center"></span></div>
    <div class="row"><button id="pop-ok">OK</button><button id="pop-cancel">Cancel</button></div>`;
  // near the cursor when it is over the canvas, else near the canvas center
  const inCv = S.mouse.x >= 0 && S.mouse.y >= 0 && S.mouse.x <= cv.clientWidth && S.mouse.y <= cv.clientHeight;
  const [bx, by] = inCv ? [S.mouse.x + 12, S.mouse.y + 12] : [cv.clientWidth / 2 - 110, cv.clientHeight / 2 - 60];
  const mx = Math.max(8, Math.min(bx, cv.clientWidth - 240)), my = Math.max(8, Math.min(by, cv.clientHeight - 150));
  pop.style.left = mx + "px"; pop.style.top = my + "px"; pop.style.display = "block";
  const val = $("pop-val"), kindSel = $("pop-kind");
  const refresh = () => {
    const [k, ents] = kinds[kindSel ? +kindSel.value : 0];
    val.value = editCon ? String(editCon.value) : String(nice(M.measure(S.sk, k, ents, find())));
    $("pop-unit").textContent = unit(k);
    val.select();
  };
  if (kindSel) kindSel.onchange = refresh;
  refresh();
  val.focus();
  const close = () => { pop.style.display = "none"; cv.focus(); };
  const ok = () => {
    const v = Number(val.value);
    if (!Number.isFinite(v)) { val.style.borderColor = "var(--bad)"; return; }
    const [k, ents] = kinds[kindSel ? +kindSel.value : 0];
    snapshot();
    if (editCon) {
      editCon.value = v;
      if (editCon.kind === "angle") editCon.rev = M.angleRev(S.sk, editCon);
      if (!S.opts.relax) { touched(); M.presatisfy(S.sk, editCon); }
    } else {
      const extra = { value: v };
      const f = find();
      if (k === "hdistance" || k === "vdistance") {
        const a = M.pos(S.sk, E(ents[0]), f), b = M.pos(S.sk, E(ents[1]), f);
        extra.swap = k === "hdistance" ? b.x < a.x : b.y < a.y;
      }
      if (k === "lineDistance") {
        const p = M.pos(S.sk, E(ents[0]), f), s = E(ents[1]);
        const a = M.pos(S.sk, E(s.p), f), b = M.pos(S.sk, E(s.q), f);
        extra.rev = (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x) < 0;
      }
      if (k === "angle") extra.rev = M.angleRev(S.sk, { kind: k, ents, value: v }, f);
      addCon(k, ents, extra);
    }
    close();
    changed();
  };
  $("pop-ok").onclick = ok;
  $("pop-cancel").onclick = close;
  val.onkeydown = e => { if (e.key === "Enter") ok(); if (e.key === "Escape") close(); e.stopPropagation(); };
}

// Mouse
// -----

function eventPos(e) {
  const r = cv.getBoundingClientRect();
  return [e.clientX - r.left, e.clientY - r.top];
}

// a point at the cursor: an existing one under it, or a new one
function pointAt(px, py, create = true) {
  const h = hit(px, py, ["pt"]);
  if (h) return h;
  if (!create) return null;
  const [x, y] = toWorld(px, py);
  return M.addPoint(S.sk, round6(x), round6(y));
}

cv.addEventListener("contextmenu", e => e.preventDefault());

cv.addEventListener("mousedown", e => {
  const [px, py] = eventPos(e);
  $("pop").style.display = "none";
  if (e.button === 1 || e.button === 2 || S.space) {
    if (e.button === 2 && S.pending) { S.pending = null; render(); return; }
    S.drag = { kind: "pan", px, py, cx: S.view.cx, cy: S.view.cy };
    return;
  }
  if (S.tool === "point") {
    snapshot();
    pointAt(px, py);
    changed();
    return;
  }
  if (S.tool === "line") {
    if (!S.pending) {
      snapshot();
      const p = pointAt(px, py);
      touched();
      S.pending = { kind: "line", from: p.id };
    } else {
      const q = pointAt(px, py);
      if (q.id !== S.pending.from) M.addSeg(S.sk, S.pending.from, q.id);
      S.pending = { kind: "line", from: q.id };
      changed();
    }
    render();
    return;
  }
  if (S.tool === "circle") {
    if (!S.pending) {
      snapshot();
      const c = pointAt(px, py);
      touched();
      S.pending = { kind: "circle", from: c.id };
    } else {
      const c = P(E(S.pending.from)), [x, y] = toWorld(px, py);
      M.addCircle(S.sk, S.pending.from, round6(Math.max(1e-3, Math.hypot(x - c.x, y - c.y))));
      S.pending = null;
      changed();
    }
    render();
    return;
  }
  // select tool
  const h = hit(px, py);
  if (h) {
    if (e.shiftKey) {
      S.sel = S.sel.includes(h.id) ? S.sel.filter(i => i !== h.id) : [...S.sel, h.id];
    } else if (!S.sel.includes(h.id)) {
      S.sel = [h.id];
    }
    S.selCon = null;
    const [wx, wy] = toWorld(px, py);
    S.drag = { kind: "move", ent: h.id, wx, wy, moved: false, start: M.clone(S.sk) };
    if (h.kind === "circ") {
      const c = P(E(h.c));
      const onEdge = Math.abs(Math.hypot(wx - c.x, wy - c.y) - R(h)) * S.view.s < 8;
      if (onEdge) S.drag.kind = "radius";
    }
  } else {
    if (!e.shiftKey) S.sel = [];
    S.selCon = null;
    S.drag = { kind: "box", px, py, x2: px, y2: py, add: e.shiftKey };
  }
  render(); renderPanels();
});

let lastLive = 0;
window.addEventListener("mousemove", e => {
  const [px, py] = eventPos(e);
  S.mouse.x = px; S.mouse.y = py;
  const [wx, wy] = toWorld(px, py);
  S.mouse.wx = wx; S.mouse.wy = wy;
  $("coords").textContent = `${wx.toFixed(3)}, ${wy.toFixed(3)}`;
  const d = S.drag;
  if (!d) {
    const h = S.tool === "select" ? hit(px, py) : hit(px, py, ["pt"]);
    const id = h ? h.id : null;
    if (id !== S.hover) { S.hover = id; render(); }
    if (S.pending) render();
    return;
  }
  if (d.kind === "pan") {
    S.view.cx = d.cx - (px - d.px) / S.view.s;
    S.view.cy = d.cy + (py - d.py) / S.view.s;
    render();
    return;
  }
  if (d.kind === "box") { d.x2 = px; d.y2 = py; render(); return; }
  // moving geometry
  if (!d.moved) { S.undo.push(d.start); S.redo = []; d.moved = true; }
  const h = E(d.ent);
  const f = find();
  const dx = wx - d.wx, dy = wy - d.wy;
  d.wx = wx; d.wy = wy;
  const heavy = [];
  const movePt = p => { const q = M.pos(S.sk, p, f); M.setPoint(S.sk, p, q.x + dx, q.y + dy, f); heavy.push(p.x, p.y); };
  if (d.kind === "radius") {
    const c = M.pos(S.sk, E(h.c), f);
    S.sk.vars[f(h.r)].val = Math.max(1e-3, Math.hypot(wx - c.x, wy - c.y));
    heavy.push(h.r);
  } else if (h.kind === "pt") {
    M.setPoint(S.sk, h, wx, wy, f); heavy.push(h.x, h.y);
  } else if (h.kind === "seg") {
    const ps = [...new Set([h.p, h.q])].map(E);
    ps.forEach(movePt);
  } else if (h.kind === "circ") {
    movePt(E(h.c));
  }
  touched();
  d.heavy = heavy;
  const now = performance.now();
  if (S.opts.auto && now - lastLive > 30) {
    lastLive = now;
    certify({ heavy });
  }
  render();
});

window.addEventListener("mouseup", () => {
  const d = S.drag;
  S.drag = null;
  if (!d) return;
  if (d.kind === "box") {
    const [x0, x1] = [Math.min(d.px, d.x2), Math.max(d.px, d.x2)];
    const [y0, y1] = [Math.min(d.py, d.y2), Math.max(d.py, d.y2)];
    if (x1 - x0 > 3 || y1 - y0 > 3) {
      const inside = (x, y) => x >= x0 && x <= x1 && y >= y0 && y <= y1;
      const ids = [];
      for (const e of S.sk.ents) {
        let pts = [];
        if (e.kind === "pt") pts = [P(e)];
        else if (e.kind === "seg") pts = [P(E(e.p)), P(E(e.q))];
        else if (e.kind === "circ") { const c = P(E(e.c)), r = R(e); pts = [{ x: c.x - r, y: c.y - r }, { x: c.x + r, y: c.y + r }]; }
        if (pts.every(p => inside(...toScreen(p.x, p.y)))) ids.push(e.id);
      }
      S.sel = d.add ? [...new Set([...S.sel, ...ids])] : ids;
    }
    render(); renderPanels();
    return;
  }
  if ((d.kind === "move" || d.kind === "radius") && d.moved) changed({ heavy: d.heavy, force: true });
});

cv.addEventListener("wheel", e => {
  e.preventDefault();
  const [px, py] = eventPos(e);
  const [wx, wy] = toWorld(px, py);
  const k = Math.exp(-e.deltaY * 0.0015);
  S.view.s = Math.max(2, Math.min(5000, S.view.s * k));
  const [wx2, wy2] = toWorld(px, py);
  S.view.cx += wx - wx2; S.view.cy += wy - wy2;
  render();
}, { passive: false });

// Keys
// ----

window.addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT" || e.target.tagName === "SELECT") return;
  const k = e.key.toLowerCase();
  if ((e.ctrlKey || e.metaKey) && k === "z") { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
  if ((e.ctrlKey || e.metaKey) && k === "y") { e.preventDefault(); redo(); return; }
  if (e.key === " ") { S.space = true; return; }
  if (e.key === "Escape") { S.pending = null; S.sel = []; S.selCon = null; setTool("select"); render(); renderPanels(); return; }
  if (e.key === "Delete" || e.key === "Backspace") { deleteSelection(); return; }
  if (e.key === "Enter") { certify({ force: true }); return; }
  const t = TOOLS.find(t => t.key.toLowerCase() === k);
  if (t) { setTool(t.id); return; }
  const c = CTOOLS.find(t => t.key && t.key.toLowerCase() === k);
  if (c && applicable(c.id)) applyConstraint(c.id);
});
window.addEventListener("keyup", e => { if (e.key === " ") S.space = false; });

function deleteSelection() {
  if (S.selCon !== null) {
    snapshot();
    S.sk.cons = S.sk.cons.filter(c => c.id !== S.selCon);
    S.selCon = null;
    changed();
    return;
  }
  if (!S.sel.length) return;
  snapshot();
  M.removeEnts(S.sk, S.sel);
  S.sel = [];
  changed();
}

function undo() {
  if (!S.undo.length) return;
  S.redo.push(M.clone(S.sk));
  S.sk = S.undo.pop();
  S.sel = []; S.pending = null;
  changed();
}
function redo() {
  if (!S.redo.length) return;
  S.undo.push(M.clone(S.sk));
  S.sk = S.redo.pop();
  S.sel = []; S.pending = null;
  changed();
}

function setTool(id) {
  S.tool = id;
  S.pending = null;
  $("hint").textContent = HINTS[id] || "";
  renderPanels();
  render();
}

// Drawing
// -------

let css = {};
function readColors() {
  const st = getComputedStyle(document.documentElement);
  for (const k of ["canvas", "grid", "grid-major", "geom", "construct", "sel", "hover", "pinned", "dim", "bad", "warn", "ok", "muted", "panel", "line", "ink"]) css[k] = st.getPropertyValue("--" + k).trim();
}

function resize() {
  const dpr = window.devicePixelRatio || 1;
  cv.width = cv.clientWidth * dpr; cv.height = cv.clientHeight * dpr;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  render();
}

let raf = 0;
function render() {
  if (raf) return;
  raf = requestAnimationFrame(() => { raf = 0; draw(); });
}

function drawGrid() {
  const W = cv.clientWidth, H = cv.clientHeight, s = S.view.s;
  ctx.fillStyle = css.canvas; ctx.fillRect(0, 0, W, H);
  let step = 1;
  while (step * s < 14) step *= 5;
  while (step * s > 70) step /= 5;
  const [x0, y1] = toWorld(0, 0), [x1, y0] = toWorld(W, H);
  ctx.lineWidth = 1;
  for (let gx = Math.floor(x0 / step) * step; gx <= x1; gx += step) {
    const major = Math.abs(Math.round(gx / step) % 5) === 0;
    ctx.strokeStyle = major ? css["grid-major"] : css.grid;
    const [sx] = toScreen(gx, 0);
    ctx.beginPath(); ctx.moveTo(Math.round(sx) + 0.5, 0); ctx.lineTo(Math.round(sx) + 0.5, H); ctx.stroke();
  }
  for (let gy = Math.floor(y0 / step) * step; gy <= y1; gy += step) {
    const major = Math.abs(Math.round(gy / step) % 5) === 0;
    ctx.strokeStyle = major ? css["grid-major"] : css.grid;
    const [, sy] = toScreen(0, gy);
    ctx.beginPath(); ctx.moveTo(0, Math.round(sy) + 0.5); ctx.lineTo(W, Math.round(sy) + 0.5); ctx.stroke();
  }
  ctx.strokeStyle = css.muted; ctx.globalAlpha = 0.35;
  const [ox, oy] = toScreen(0, 0);
  ctx.beginPath(); ctx.moveTo(ox, 0); ctx.lineTo(ox, H); ctx.moveTo(0, oy); ctx.lineTo(W, oy); ctx.stroke();
  ctx.globalAlpha = 1;
}

// entities touched by red constraints and by the hovered/selected constraint
function involved(cid) {
  const c = S.sk.cons.find(c => c.id === cid);
  if (!c) return new Set();
  const out = new Set(c.ents);
  for (const i of c.ents) { const e = E(i); if (e && e.kind === "seg") { out.add(e.p); out.add(e.q); } if (e && e.kind === "circ") out.add(e.c); }
  return out;
}

function colorOf(e, redEnts, hiEnts) {
  if (S.sel.includes(e.id)) return css.sel;
  if (hiEnts.has(e.id)) return css.sel;
  if (redEnts.has(e.id)) return css.bad;
  if (S.hover === e.id) return css.hover;
  return e.construction ? css.construct : css.geom;
}

function label(text, x, y, color, bg = true) {
  ctx.font = "12px system-ui, sans-serif";
  const w = ctx.measureText(text).width;
  if (bg) {
    ctx.fillStyle = css.canvas; ctx.globalAlpha = 0.9;
    ctx.fillRect(x - w / 2 - 3, y - 8, w + 6, 16);
    ctx.globalAlpha = 1;
  }
  ctx.fillStyle = color;
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  ctx.fillText(text, x, y);
}

function fmt(v) { return String(nice(v)); }

function drawDimension(c, color) {
  const f = find();
  const pt = id => M.pos(S.sk, E(id), f);
  const sc = (p) => toScreen(p.x, p.y);
  ctx.strokeStyle = color; ctx.lineWidth = 1;
  switch (c.kind) {
    case "distance": case "hdistance": case "vdistance": {
      let a = pt(c.ents[0]), b = pt(c.ents[1]);
      if (c.kind === "hdistance") b = { x: b.x, y: a.y };
      if (c.kind === "vdistance") b = { x: a.x, y: b.y };
      const [ax, ay] = sc(a), [bx, by] = sc(b);
      let nx = -(by - ay), ny = bx - ax;
      const L = Math.hypot(nx, ny) || 1;
      nx = nx / L * 18; ny = ny / L * 18;
      ctx.setLineDash([3, 3]);
      ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(ax + nx, ay + ny); ctx.moveTo(bx, by); ctx.lineTo(bx + nx, by + ny); ctx.stroke();
      ctx.setLineDash([]);
      ctx.beginPath(); ctx.moveTo(ax + nx, ay + ny); ctx.lineTo(bx + nx, by + ny); ctx.stroke();
      label(fmt(c.value), (ax + bx) / 2 + nx, (ay + by) / 2 + ny, color);
      return [(ax + bx) / 2 + nx, (ay + by) / 2 + ny];
    }
    case "radius": case "diameter": {
      const e = E(c.ents[0]), ctr = pt(e.c), r = M.val(S.sk, e.r, f);
      const [cx, cy] = sc(ctr), [ex, ey] = toScreen(ctr.x + r * Math.SQRT1_2, ctr.y + r * Math.SQRT1_2);
      ctx.beginPath(); ctx.moveTo(c.kind === "diameter" ? 2 * cx - ex : cx, c.kind === "diameter" ? 2 * cy - ey : cy); ctx.lineTo(ex, ey); ctx.stroke();
      label((c.kind === "radius" ? "R " : "D ") + fmt(c.value), ex + 14, ey - 10, color);
      return [ex + 14, ey - 10];
    }
    case "lineDistance": {
      const p = pt(c.ents[0]), s = E(c.ents[1]), a = pt(s.p), b = pt(s.q);
      const dx = b.x - a.x, dy = b.y - a.y, L2 = dx * dx + dy * dy || 1;
      const t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / L2;
      const foot = { x: a.x + t * dx, y: a.y + t * dy };
      const [px, py] = sc(p), [fx, fy] = sc(foot);
      ctx.setLineDash([3, 3]); ctx.beginPath(); ctx.moveTo(px, py); ctx.lineTo(fx, fy); ctx.stroke(); ctx.setLineDash([]);
      label(fmt(c.value), (px + fx) / 2 + 10, (py + fy) / 2, color);
      return [(px + fx) / 2 + 10, (py + fy) / 2];
    }
    case "angle": {
      const sa = E(c.ents[0]), sb = E(c.ents[1]);
      const a0 = pt(sa.p), a1 = pt(sa.q), b0 = pt(sb.p), b1 = pt(sb.q);
      // around the second segment's start
      const [ox, oy] = sc(b0);
      // the second direction as the constraint reads it (rev: backwards)
      const ta = Math.atan2(a1.y - a0.y, a1.x - a0.x), tb = Math.atan2(b1.y - b0.y, b1.x - b0.x) + (c.rev ? Math.PI : 0);
      ctx.beginPath(); ctx.arc(ox, oy, 26, -ta, -tb, true); ctx.stroke();
      const tm = ta + ((((tb - ta) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)) / 2;
      label(fmt(c.value) + "°", ox + 44 * Math.cos(tm), oy - 44 * Math.sin(tm), color);
      return [ox + 44 * Math.cos(tm), oy - 44 * Math.sin(tm)];
    }
  }
  return null;
}

const GLYPH = { horizontal: "H", vertical: "V", parallel: "∥", perpendicular: "⊥", equalLength: "=", equalRadius: "=",
  concentric: "◎", midpoint: "M", symmetric: "S", fix: "F", coincident: "•", onLine: "•", onCircle: "•" };

function glyphPos(c) {
  const f = find();
  const pt = id => M.pos(S.sk, E(id), f);
  const e0 = E(c.ents[0]);
  if (!e0) return null;
  if (e0.kind === "seg") { const a = pt(e0.p), b = pt(e0.q); return toScreen((a.x + b.x) / 2, (a.y + b.y) / 2); }
  if (e0.kind === "circ") { const ctr = pt(e0.c); return toScreen(ctr.x, ctr.y + M.val(S.sk, e0.r, f)); }
  const p = pt(e0.id);
  if (c.kind === "horizontal" || c.kind === "vertical") { const q = pt(c.ents[1]); return toScreen((p.x + q.x) / 2, (p.y + q.y) / 2); }
  return toScreen(p.x, p.y);
}

function draw() {
  if (!css.canvas) readColors();
  drawGrid();
  const f = find();
  const red = new Set(), hi = new Set();
  for (const c of S.sk.cons) if (S.cert.red.has(c.id)) involved(c.id).forEach(i => red.add(i));
  const hc = S.hoverCon ?? S.selCon;
  if (hc !== null && hc !== undefined) involved(hc).forEach(i => hi.add(i));
  // curves
  for (const e of S.sk.ents) {
    if (e.kind === "pt") continue;
    ctx.strokeStyle = colorOf(e, red, hi);
    ctx.lineWidth = S.sel.includes(e.id) || S.hover === e.id ? 2.4 : 1.7;
    ctx.setLineDash(e.construction ? [6, 5] : []);
    ctx.beginPath();
    if (e.kind === "seg") {
      const a = M.pos(S.sk, E(e.p), f), b = M.pos(S.sk, E(e.q), f);
      ctx.moveTo(...toScreen(a.x, a.y)); ctx.lineTo(...toScreen(b.x, b.y));
    } else if (e.kind === "circ") {
      const c = M.pos(S.sk, E(e.c), f), [x, y] = toScreen(c.x, c.y);
      ctx.arc(x, y, Math.max(0.5, M.val(S.sk, e.r, f) * S.view.s), 0, 2 * Math.PI);
    }
    ctx.stroke();
  }
  ctx.setLineDash([]);
  // constraint glyphs and dimensions
  const glyphCount = new Map();
  for (const c of S.sk.cons) {
    const st = S.cert.ok === null ? undefined : S.cert.status.get(c.id);
    const color = S.cert.red.has(c.id) ? css.bad : hc === c.id ? css.sel : st && st.k === "amber" ? css.warn : css.dim;
    if (M.CK[c.kind].value) { drawDimension(c, color); continue; }
    const g = GLYPH[c.kind];
    const p = glyphPos(c);
    if (!g || !p) continue;
    const key = Math.round(p[0] / 6) + "," + Math.round(p[1] / 6);
    const n = glyphCount.get(key) || 0;
    glyphCount.set(key, n + 1);
    label(g, p[0] + 12 + n * 14, p[1] - 12, color);
  }
  // points
  for (const e of S.sk.ents) {
    if (e.kind !== "pt") continue;
    const p = M.pos(S.sk, e, f), [x, y] = toScreen(p.x, p.y);
    const held = S.cert.ok !== null && (S.cert.pinned.has(e.x) || S.cert.pinned.has(e.y));
    const col = colorOf(e, red, hi);
    ctx.beginPath(); ctx.arc(x, y, S.sel.includes(e.id) || S.hover === e.id ? 4.5 : 3.5, 0, 2 * Math.PI);
    if (held) {
      ctx.fillStyle = css.canvas; ctx.fill();
      ctx.strokeStyle = col === css.geom ? css.pinned : col; ctx.lineWidth = 1.6; ctx.stroke();
    } else {
      ctx.fillStyle = col; ctx.fill();
    }
  }
  // tool previews
  if (S.pending) {
    const a = M.pos(S.sk, E(S.pending.from), f), [ax, ay] = toScreen(a.x, a.y);
    const snap = hit(S.mouse.x, S.mouse.y, ["pt"], S.pending.from);
    let [mx, my] = [S.mouse.x, S.mouse.y];
    if (snap) { const q = M.pos(S.sk, snap, f); [mx, my] = toScreen(q.x, q.y); }
    ctx.strokeStyle = css.sel; ctx.lineWidth = 1.4; ctx.setLineDash([5, 4]);
    ctx.beginPath();
    if (S.pending.kind === "line") { ctx.moveTo(ax, ay); ctx.lineTo(mx, my); }
    else ctx.arc(ax, ay, Math.hypot(mx - ax, my - ay), 0, 2 * Math.PI);
    ctx.stroke(); ctx.setLineDash([]);
  }
  if (S.drag && S.drag.kind === "box") {
    const d = S.drag;
    ctx.strokeStyle = css.sel; ctx.fillStyle = css.sel; ctx.globalAlpha = 0.08;
    ctx.fillRect(d.px, d.py, d.x2 - d.px, d.y2 - d.py);
    ctx.globalAlpha = 1; ctx.lineWidth = 1; ctx.setLineDash([4, 3]);
    ctx.strokeRect(d.px + 0.5, d.py + 0.5, d.x2 - d.px, d.y2 - d.py); ctx.setLineDash([]);
  }
}

// Panels
// ------

function icon(name) { return `<svg viewBox="0 0 24 24">${ICON[name] || ""}</svg>`; }

function buildToolbars() {
  $("tools").innerHTML = TOOLS.map(t => `<button data-tool="${t.id}" title="${t.label} (${t.key})">${icon(t.id)}<span>${t.label}</span><kbd>${t.key}</kbd></button>`).join("");
  $("ctools").innerHTML = CTOOLS.map(t => `<button data-ctool="${t.id}" title="${TIPS[t.id]}${t.key ? " (" + t.key + ")" : ""}">${icon(t.id)}<span>${t.label}</span></button>`).join("");
  for (const b of document.querySelectorAll("[data-tool]")) b.onclick = () => setTool(b.dataset.tool);
  for (const b of document.querySelectorAll("[data-ctool]")) b.onclick = () => applyConstraint(b.dataset.ctool);
}

function entName(id) {
  const e = E(id);
  if (!e) return "?";
  return { pt: "P", seg: "L", circ: "C" }[e.kind] + e.id;
}

function renderPanels() {
  for (const b of document.querySelectorAll("[data-tool]")) b.classList.toggle("on", b.dataset.tool === S.tool);
  for (const b of document.querySelectorAll("[data-ctool]")) b.disabled = !applicable(b.dataset.ctool);
  $("b-undo").disabled = !S.undo.length; $("b-redo").disabled = !S.redo.length;
  const es = selEnts();
  $("selinfo").textContent = es.length ? es.map(e => entName(e.id)).join(", ") : "Nothing selected";
  // certificate
  const c = S.cert;
  const rows = [];
  if (c.ok === null && c.state !== "error") rows.push(["Status", "not run yet"]);
  else if (c.state === "error") rows.push(["Status", "solver error"], ["", c.msg.slice(0, 300)]);
  else {
    rows.push(["Status", c.ok ? "certified" : "not certified"]);
    rows.push(["Variables", String(c.nvars)]);
    rows.push(["Held (pins)", `${c.pinsCount} at drawn values`]);
    rows.push(["Red", String(c.red.size)]);
    rows.push(["Redundant", String(countStatus("amber"))]);
    if (c.ok) rows.push(["Time", `${c.ms} ms`]);
    if (!c.ok && c.msg) rows.push(["Why", c.msg]);
  }
  $("cert").innerHTML = rows.map(([k, v]) => `<span>${k}</span><b>${escapeHtml(v)}</b>`).join("");
  // constraints
  const ul = $("cons");
  if (!S.sk.cons.length) { ul.innerHTML = `<li class="empty">No constraints yet</li>`; return; }
  const num = new Map(S.sk.cons.map((con, i) => [con.id, i + 1]));
  ul.innerHTML = S.sk.cons.map((con, i) => {
    const k = M.CK[con.kind];
    const red = S.cert.red.has(con.id);
    const st = S.cert.ok === null ? undefined : S.cert.status.get(con.id);
    const cl = red ? "red" : st && st.k === "amber" ? "amber" : st && st.k === "partly" ? "part" : "";
    const v = k.value ? `<input data-val="${con.id}" value="${con.value}">` : "";
    const fx = con.kind === "fix" ? ` (${nice(con.fx)}, ${nice(con.fy)})` : "";
    const say = statusText(con, num);
    return `<li data-con="${con.id}" class="${cl} ${S.selCon === con.id ? "sel" : ""}" title="${escapeHtml(statusTitle(con))}">
      <span class="no">#${i + 1}</span><span class="nm">${k.label} ${con.ents.map(entName).join(" ")}${fx}${say ? `<em class="st">${escapeHtml(say)}</em>` : ""}</span>${v}<button class="x" data-del="${con.id}" title="Delete">×</button></li>`;
  }).join("");
  for (const li of ul.querySelectorAll("[data-con]")) {
    const id = +li.dataset.con;
    li.onmouseenter = () => { S.hoverCon = id; render(); };
    li.onmouseleave = () => { S.hoverCon = null; render(); };
    li.onclick = e => { if (e.target.tagName === "INPUT" || e.target.tagName === "BUTTON") return; S.selCon = S.selCon === id ? null : id; S.sel = []; renderPanels(); render(); };
  }
  for (const inp of ul.querySelectorAll("[data-val]")) {
    inp.onkeydown = e => { e.stopPropagation(); if (e.key === "Enter") inp.blur(); };
    inp.onchange = () => {
      const con = S.sk.cons.find(c => c.id === +inp.dataset.val);
      const v = Number(inp.value);
      if (!con || !Number.isFinite(v)) { inp.value = con ? con.value : ""; return; }
      snapshot();
      con.value = v;
      if (con.kind === "angle") con.rev = M.angleRev(S.sk, con);
      if (!S.opts.relax) { touched(); M.presatisfy(S.sk, con); }
      changed();
    };
  }
  for (const b of ul.querySelectorAll("[data-del]")) b.onclick = () => {
    snapshot();
    S.sk.cons = S.sk.cons.filter(c => c.id !== +b.dataset.del);
    changed();
  };
}

function escapeHtml(s) { return String(s).replace(/[&<>"]/g, ch => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[ch])); }

// Header buttons and settings
// ---------------------------

$("b-new").onclick = () => { snapshot(); S.sk = M.emptySketch(); S.sel = []; S.cert = { ...S.cert, ok: null, red: new Set(), pinned: new Set(), status: new Map() }; changed(); };
$("b-example").onclick = () => { snapshot(); S.sk = PL.example(); S.sel = []; S.view = { cx: 3.5, cy: 3, s: 60 }; changed({ force: true }); };
$("b-undo").onclick = undo;
$("b-redo").onclick = redo;
$("b-solve").onclick = () => certify({ force: true });
$("b-export").onclick = () => {
  const blob = new Blob([JSON.stringify(S.sk, null, 1)], { type: "application/json" });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob); a.download = "sketch.json"; a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
};
$("b-import").onclick = () => $("f-import").click();
$("f-import").onchange = async () => {
  const f = $("f-import").files[0];
  if (!f) return;
  try {
    const sk = JSON.parse(await f.text());
    if (!sk.ents || !sk.cons || !sk.vars) throw new Error("not a sketch");
    snapshot(); S.sk = M.migrate(sk); S.sel = []; changed({ force: true });
  } catch (e) { setStatus("bad", "Could not read that file"); }
  $("f-import").value = "";
};
for (const k of ["relax", "order", "dyadic", "auto"]) {
  const box = $("o-" + k);
  box.checked = S.opts[k];
  box.onchange = () => { S.opts[k] = box.checked; save(); if (k !== "auto") certify({ force: true }); };
}

window.addEventListener("resize", resize);
if (window.matchMedia) window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => { readColors(); render(); });

// for tests and the console: the state and screen positions
window.bendcad = {
  S,
  screenOf(id) {
    const e = E(id);
    if (!e) return null;
    if (e.kind === "pt") { const p = P(e); return toScreen(p.x, p.y); }
    if (e.kind === "seg") { const a = P(E(e.p)), b = P(E(e.q)); return toScreen((a.x + b.x) / 2, (a.y + b.y) / 2); }
    const c = P(E(e.c)); return toScreen(c.x + R(e), c.y);
  },
};

// Start
// -----

const had = load();
for (const k of ["relax", "order", "dyadic", "auto"]) $("o-" + k).checked = S.opts[k];
if (!had) S.sk = PL.example();
buildToolbars();
setTool("select");
resize();
renderPanels();
certify({ force: true });
