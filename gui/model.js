// bend-cad sketcher: the sketch model, independent of the page.
//
// Entities own variables (a point its x and y, a circle its radius). The
// merge constraints (coincident, horizontal, vertical, concentric, equal
// radius) are equations like any other (spec/sketch.bend, D3 as revised):
// the solver gets every variable and the merges' equations. The drawing
// keeps merged variables together through union-find classes (classes):
// it shows a class at one value and moves it as one.

export const VK = { coord: 0, length: 1, param: 2, aux: 3 };

// constraint kinds: solver code, what they take, and whether they carry a value
export const CK = {
  coincident:    { code: 0,  sig: ["pt", "pt"], merge: true, label: "Coincident" },
  horizontal:    { code: 1,  sig: ["pt", "pt"], merge: true, label: "Horizontal" },
  vertical:      { code: 2,  sig: ["pt", "pt"], merge: true, label: "Vertical" },
  concentric:    { code: 3,  sig: ["circ", "circ"], merge: true, label: "Concentric" },
  equalRadius:   { code: 4,  sig: ["circ", "circ"], merge: true, label: "Equal radius" },
  fix:           { code: 5,  sig: ["pt"], label: "Fix" },
  distance:      { code: 6,  sig: ["pt", "pt"], value: true, label: "Distance" },
  hdistance:     { code: 7,  sig: ["pt", "pt"], value: true, label: "Horizontal distance" },
  vdistance:     { code: 8,  sig: ["pt", "pt"], value: true, label: "Vertical distance" },
  radius:        { code: 9,  sig: ["circ"], value: true, label: "Radius" },
  diameter:      { code: 10, sig: ["circ"], value: true, label: "Diameter" },
  lineDistance:  { code: 11, sig: ["pt", "seg"], value: true, label: "Point-line distance" },
  angle:         { code: 12, sig: ["seg", "seg"], value: true, label: "Angle" },
  equalLength:   { code: 13, sig: ["seg", "seg"], label: "Equal length" },
  perpendicular: { code: 14, sig: ["seg", "seg"], label: "Perpendicular" },
  parallel:      { code: 15, sig: ["seg", "seg"], label: "Parallel" },
  onLine:        { code: 16, sig: ["pt", "seg"], label: "On line" },
  onCircle:      { code: 17, sig: ["pt", "circ"], label: "On circle" },
  midpoint:      { code: 18, sig: ["pt", "seg"], label: "Midpoint" },
  symmetric:     { code: 19, sig: ["pt", "pt", "seg"], label: "Symmetric" },
};

export function emptySketch() {
  return { nextVar: 0, nextEnt: 0, nextCon: 0, vars: {}, ents: [], cons: [] };
}

export function clone(sk) {
  return JSON.parse(JSON.stringify(sk));
}

function newVar(sk, kind, val) {
  const id = sk.nextVar++;
  sk.vars[id] = { kind, val };
  return id;
}

export function addPoint(sk, x, y, construction = false) {
  const e = { id: sk.nextEnt++, kind: "pt", construction, x: newVar(sk, VK.coord, x), y: newVar(sk, VK.coord, y) };
  sk.ents.push(e);
  return e;
}

export function addSeg(sk, p, q, construction = false) {
  const e = { id: sk.nextEnt++, kind: "seg", construction, p, q };
  sk.ents.push(e);
  return e;
}

export function addCircle(sk, c, r, construction = false) {
  const e = { id: sk.nextEnt++, kind: "circ", construction, c, r: newVar(sk, VK.length, r) };
  sk.ents.push(e);
  return e;
}

export function ent(sk, id) {
  return sk.ents.find(e => e.id === id);
}

// Union-find over variables, from the merge constraints present
export function classes(sk) {
  const parent = {};
  const find = v => {
    while (parent[v] !== undefined && parent[v] !== v) v = parent[v];
    return v;
  };
  const union = (a, b) => {
    const ra = find(a), rb = find(b);
    if (ra !== rb) parent[rb] = ra;
  };
  for (const v of Object.keys(sk.vars)) parent[v] = Number(v);
  for (const c of sk.cons) {
    const [a, b] = c.ents.map(i => ent(sk, i));
    if (!a || !b) continue;
    switch (c.kind) {
      case "coincident": union(a.x, b.x); union(a.y, b.y); break;
      case "horizontal": union(a.y, b.y); break;
      case "vertical": union(a.x, b.x); break;
      case "concentric": {
        const ca = ent(sk, a.c), cb = ent(sk, b.c);
        union(ca.x, cb.x); union(ca.y, cb.y); break;
      }
      case "equalRadius": union(a.r, b.r); break;
    }
  }
  return find;
}

// the value a variable has now (its class representative's)
export function val(sk, v, find = classes(sk)) {
  return sk.vars[find(v)].val;
}

export function pos(sk, p, find = classes(sk)) {
  return { x: val(sk, p.x, find), y: val(sk, p.y, find) };
}

// moving a point moves its classes
export function setPoint(sk, p, x, y, find = classes(sk)) {
  sk.vars[find(p.x)].val = x;
  sk.vars[find(p.y)].val = y;
}

function segPts(sk, s, find) {
  return [pos(sk, ent(sk, s.p), find), pos(sk, ent(sk, s.q), find)];
}

// the current measured value of a dimension, for its default
export function measure(sk, kind, ents, find = classes(sk)) {
  const E = ents.map(i => ent(sk, i));
  switch (kind) {
    case "distance": {
      const a = pos(sk, E[0], find), b = pos(sk, E[1], find);
      return Math.hypot(b.x - a.x, b.y - a.y);
    }
    case "hdistance": {
      const a = pos(sk, E[0], find), b = pos(sk, E[1], find);
      return Math.abs(b.x - a.x);
    }
    case "vdistance": {
      const a = pos(sk, E[0], find), b = pos(sk, E[1], find);
      return Math.abs(b.y - a.y);
    }
    case "radius": return val(sk, E[0].r, find);
    case "diameter": return 2 * val(sk, E[0].r, find);
    case "lineDistance": {
      const p = pos(sk, E[0], find), [a, b] = segPts(sk, E[1], find);
      const L = Math.hypot(b.x - a.x, b.y - a.y) || 1;
      return Math.abs((b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)) / L;
    }
    case "angle": {
      const [a0, a1] = segPts(sk, E[0], find), [b0, b1] = segPts(sk, E[1], find);
      const ta = Math.atan2(a1.y - a0.y, a1.x - a0.x), tb = Math.atan2(b1.y - b0.y, b1.x - b0.x);
      let d = (tb - ta) * 180 / Math.PI;
      while (d < 0) d += 360;
      while (d >= 360) d -= 360;
      return d;
    }
  }
  return 0;
}

// an exact rational unit vector near angle deg: c = (1 - t^2)/(1 + t^2),
// s = 2t/(1 + t^2) with t a rational near tan(deg/4)... we use t near
// tan(theta/2), which gives c^2 + s^2 = 1 exactly
export function rationalRotation(deg) {
  const th = deg * Math.PI / 180;
  // near +-180 degrees tan(th/2) blows up: rotate by 180 via a sign flip
  let flip = false, t2 = th;
  if (Math.cos(th / 2) < 0.2 && Math.cos(th / 2) > -0.2) { flip = true; t2 = th - Math.PI; }
  const t = Math.tan(t2 / 2);
  const [n, d] = approx(t, 10000);
  const c = { n: d * d - n * n, d: d * d + n * n };
  const s = { n: 2 * n * d, d: d * d + n * n };
  if (flip) { c.n = -c.n; s.n = -s.n; }
  return { c: frac(c), s: frac(s) };
}

function gcd(a, b) {
  a = Math.abs(a); b = Math.abs(b);
  while (b) [a, b] = [b, a % b];
  return a || 1;
}

function frac({ n, d }) {
  const g = gcd(n, d);
  return (n / g) + "/" + (d / g);
}

// best rational approximation with denominator at most maxD
function approx(x, maxD) {
  let [h0, h1, k0, k1] = [0, 1, 1, 0];
  let y = x;
  for (let i = 0; i < 40; i++) {
    const a = Math.floor(y);
    const h2 = a * h1 + h0, k2 = a * k1 + k0;
    if (k2 > maxD) break;
    [h0, h1, k0, k1] = [h1, h2, k1, k2];
    if (Math.abs(y - a) < 1e-12) break;
    y = 1 / (y - a);
  }
  return [h1, k1];
}

// The sketch the solver reads (gui/serve.py's JSON), and how to read back
// its answer: each variable becomes a solver variable starting at its
// class's value (so the merges hold in the drawing), entities are
// renumbered, fix becomes two Fix records, and each record remembers its
// constraint.
// a value as the solver reads it: exactly as given, or (dyadic mode) the
// nearest multiple of 2^-40, since the certifying arithmetic holds only
// dyadic constants (DESIGN Q19)
export function qval(x, dyadic) {
  if (!dyadic) return String(x);
  let m = Math.round(x * 2 ** 40), e = 40;
  while (e > 0 && m % 2 === 0) { m /= 2; e--; }
  return m + "/" + 2 ** e;
}

// opts.repeats keeps the repeats duplicateOf finds (for diagnosis: the
// solver's answer to the sketch as drawn, tools/diag)
export function toSolver(sk, opts = { dyadic: true }) {
  const dy = opts.dyadic;
  const find = classes(sk);
  const vix = new Map(), vars = [], g0 = [];
  const vi = v => {
    if (!vix.has(v)) {
      vix.set(v, vars.length);
      vars.push(sk.vars[v].kind);
      g0.push(val(sk, v, find));
    }
    return vix.get(v);
  };
  const eid = new Map();
  sk.ents.forEach((e, i) => eid.set(e.id, i));
  const ents = sk.ents.map((e, i) => {
    const c = e.construction ? 1 : 0;
    switch (e.kind) {
      case "pt": return [i, c, 0, vi(e.x), vi(e.y)];
      case "seg": return [i, c, 1, eid.get(e.p), eid.get(e.q)];
      case "circ": return [i, c, 2, eid.get(e.c), vi(e.r)];
    }
  });
  const cons = [], owner = [];
  for (const c of sk.cons) {
    if (!opts.repeats && duplicateOf(sk, c)) continue;
    const k = CK[c.kind], E = c.ents.map(i => eid.get(i));
    const dr = c.driven ? 1 : 0;
    const v = c.value;
    switch (c.kind) {
      case "fix": {
        const p = ent(sk, c.ents[0]);
        cons.push([dr, 5, vi(p.x), qval(c.fx, dy)]); owner.push(c.id);
        cons.push([dr, 5, vi(p.y), qval(c.fy, dy)]); owner.push(c.id);
        break;
      }
      case "hdistance": case "vdistance":
        cons.push([dr, k.code, ...(c.swap ? [E[1], E[0]] : E), qval(v, dy)]); owner.push(c.id); break;
      case "lineDistance": {
        // the aux variable l is the segment's length
        const s = ent(sk, c.ents[1]);
        const a = pos(sk, ent(sk, s.p), find), b = pos(sk, ent(sk, s.q), find);
        const l = vars.length;
        vars.push(VK.aux); g0.push(Math.hypot(b.x - a.x, b.y - a.y) || 1);
        cons.push([dr, 11, E[0], E[1], c.rev ? 1 : 0, qval(v, dy), l]); owner.push(c.id);
        break;
      }
      case "angle": {
        // (c, s) need not be a unit vector: the constraint fixes the
        // direction, the angle atan2(s, c)
        const th = v * Math.PI / 180;
        const r = dy ? { c: qval(Math.cos(th), true), s: qval(Math.sin(th), true) } : rationalRotation(v);
        cons.push([dr, 12, E[0], 0, E[1], 0, r.c, r.s]); owner.push(c.id);
        break;
      }
      default:
        cons.push([dr, k.code, ...E, ...(k.value ? [qval(v, dy)] : [])]); owner.push(c.id);
    }
  }
  return { req: { vars, ents, cons, g0 }, vix, owner };
}

// write a certified answer back: every variable gets its box center (the
// drawing shows a class at its representative's); returns the set of
// pinned base variables (a class is shown pinned when one of its variables
// is: the merges hold the rest) and the red constraint ids
export function applyAnswer(sk, map, ans) {
  const find = classes(sk);
  const pinned = new Set(), red = new Set();
  for (const r of ans.red || []) if (map.owner[r] !== undefined) red.add(map.owner[r]);
  if (ans.ok && ans.gc && ans.gc.length) {
    for (const [v, i] of map.vix) {
      if (i < ans.gc.length) sk.vars[v].val = ans.gc[i];
    }
  }
  const pins = new Set(ans.pins || []), pinCls = new Set();
  for (const [v, i] of map.vix) if (pins.has(i)) pinCls.add(find(v));
  for (const v of Object.keys(sk.vars)) {
    if (pinCls.has(find(Number(v)))) pinned.add(Number(v));
  }
  return { pinned, red };
}

// deleting an entity deletes what depends on it
export function removeEnts(sk, ids) {
  const gone = new Set(ids);
  let changed = true;
  while (changed) {
    changed = false;
    for (const e of sk.ents) {
      if (gone.has(e.id)) continue;
      const deps = e.kind === "seg" ? [e.p, e.q] : e.kind === "circ" ? [e.c] : [];
      if (deps.some(d => gone.has(d))) { gone.add(e.id); changed = true; }
    }
  }
  sk.ents = sk.ents.filter(e => !gone.has(e.id));
  sk.cons = sk.cons.filter(c => !c.ents.some(i => gone.has(i)));
}

// kinds that say the same thing with their two entities either way round
const SYMMETRIC = new Set(["coincident", "horizontal", "vertical", "concentric", "equalRadius",
  "distance", "equalLength", "perpendicular", "parallel"]);

// equal for two constraints exactly when they are the same constraint: the
// kind, the entities (a symmetric kind's in either order) and every value
export function conKey(c) {
  const ents = SYMMETRIC.has(c.kind) ? [...c.ents].sort((a, b) => a - b) : c.ents;
  const vals = Object.keys(c).filter(k => !["id", "kind", "ents", "driven"].includes(k)).sort().map(k => [k, c[k]]);
  return JSON.stringify([c.kind, ents, vals]);
}

// the earlier driving constraint that c repeats, if any. A repeat is not
// redundant by structure (each copy can be matched to another variable),
// so the solver would keep both copies and meet a singular block: the
// request leaves repeats out, and the page does not add them.
export function duplicateOf(sk, c) {
  if (c.driven) return null;
  const key = conKey(c);
  for (const d of sk.cons) {
    if (d === c || (c.id !== undefined && d.id === c.id)) return null;
    if (!d.driven && conKey(d) === key) return d;
  }
  return null;
}

export function addConstraint(sk, kind, ents, extra = {}) {
  const c = { id: sk.nextCon++, kind, ents, driven: false, ...extra };
  sk.cons.push(c);
  return c;
}

// Pre-satisfying a constraint in the drawing, as CAD tools do when one is
// added or edited: the drawing moves (the last argument moves) so that the
// constraint holds there, and the verified solver then certifies the whole
// sketch from it. This only edits the drawing the solver starts from.
export function presatisfy(sk, c) {
  const find = classes(sk);
  const E = c.ents.map(i => ent(sk, i));
  const P = p => pos(sk, p, find);
  const set = (p, x, y) => setPoint(sk, p, x, y, find);
  const segEnds = s => [ent(sk, s.p), ent(sk, s.q)];
  switch (c.kind) {
    case "distance": {
      const a = P(E[0]), b = P(E[1]);
      let dx = b.x - a.x, dy = b.y - a.y, L = Math.hypot(dx, dy);
      if (L < 1e-9) { dx = 1; dy = 0; L = 1; }
      set(E[1], a.x + dx / L * c.value, a.y + dy / L * c.value);
      break;
    }
    case "hdistance": {
      const a = P(E[0]), b = P(E[1]);
      if (c.swap) set(E[0], b.x + c.value, a.y); else set(E[1], a.x + c.value, b.y);
      break;
    }
    case "vdistance": {
      const a = P(E[0]), b = P(E[1]);
      if (c.swap) set(E[0], a.x, b.y + c.value); else set(E[1], b.x, a.y + c.value);
      break;
    }
    case "radius": sk.vars[find(E[0].r)].val = c.value; break;
    case "diameter": sk.vars[find(E[0].r)].val = c.value / 2; break;
    case "lineDistance": {
      const p = P(E[0]), [s0, s1] = segEnds(E[1]).map(P);
      const dx = s1.x - s0.x, dy = s1.y - s0.y, L = Math.hypot(dx, dy) || 1;
      // the left normal; p goes to the left of the line (or the right, when rev)
      const nx = -dy / L, ny = dx / L, sgn = c.rev ? -1 : 1;
      const t = ((p.x - s0.x) * dx + (p.y - s0.y) * dy) / (L * L);
      set(E[0], s0.x + t * dx + sgn * nx * c.value, s0.y + t * dy + sgn * ny * c.value);
      break;
    }
    case "angle": case "parallel": case "perpendicular": {
      const [a0, a1] = segEnds(E[0]).map(P);
      const [bq0, bq1] = segEnds(E[1]);
      const b0 = P(bq0), b1 = P(bq1);
      const ta = Math.atan2(a1.y - a0.y, a1.x - a0.x);
      const tb = Math.atan2(b1.y - b0.y, b1.x - b0.x);
      let target;
      if (c.kind === "angle") target = ta + c.value * Math.PI / 180;
      else {
        // the nearest of the allowed directions
        const step = c.kind === "parallel" ? Math.PI : Math.PI / 2;
        const base = c.kind === "parallel" ? ta : ta + Math.PI / 2;
        target = base + step * Math.round((tb - base) / step);
      }
      const L = Math.hypot(b1.x - b0.x, b1.y - b0.y);
      set(bq1, b0.x + L * Math.cos(target), b0.y + L * Math.sin(target));
      break;
    }
    case "equalLength": {
      const [a0, a1] = segEnds(E[0]).map(P);
      const [bq0, bq1] = segEnds(E[1]);
      const b0 = P(bq0), b1 = P(bq1);
      const La = Math.hypot(a1.x - a0.x, a1.y - a0.y);
      let dx = b1.x - b0.x, dy = b1.y - b0.y, L = Math.hypot(dx, dy);
      if (L < 1e-9) { dx = 1; dy = 0; L = 1; }
      set(bq1, b0.x + dx / L * La, b0.y + dy / L * La);
      break;
    }
    case "onLine": {
      const p = P(E[0]), [s0, s1] = segEnds(E[1]).map(P);
      const dx = s1.x - s0.x, dy = s1.y - s0.y, L2 = dx * dx + dy * dy || 1;
      const t = ((p.x - s0.x) * dx + (p.y - s0.y) * dy) / L2;
      set(E[0], s0.x + t * dx, s0.y + t * dy);
      break;
    }
    case "onCircle": {
      const p = P(E[0]), ctr = P(ent(sk, E[1].c)), r = val(sk, E[1].r, find);
      let dx = p.x - ctr.x, dy = p.y - ctr.y, L = Math.hypot(dx, dy);
      if (L < 1e-9) { dx = 1; dy = 0; L = 1; }
      set(E[0], ctr.x + dx / L * r, ctr.y + dy / L * r);
      break;
    }
    case "midpoint": {
      const [s0, s1] = segEnds(E[1]).map(P);
      set(E[0], (s0.x + s1.x) / 2, (s0.y + s1.y) / 2);
      break;
    }
    case "symmetric": {
      const p = P(E[0]), [s0, s1] = segEnds(E[2]).map(P);
      const dx = s1.x - s0.x, dy = s1.y - s0.y, L2 = dx * dx + dy * dy || 1;
      const t = ((p.x - s0.x) * dx + (p.y - s0.y) * dy) / L2;
      const fx = s0.x + t * dx, fy = s0.y + t * dy;
      set(E[1], 2 * fx - p.x, 2 * fy - p.y);
      break;
    }
    case "fix": set(E[0], c.fx, c.fy); break;
  }
}
