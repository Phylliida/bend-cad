// bend-cad sketcher: from the sketch to the solver's request and back.
//   prepare: the request (optionally relaxed and reordered)
//   finish:  the solver's answer applied to the sketch
import * as M from "./model.js";
import { relax, chooseOrder, permute } from "./relax.js";

// heavy: base variable ids that should resist moving (a dragged point)
export function prepare(sk, opts, heavy = []) {
  const map = M.toSolver(sk, { dyadic: opts.dyadic, dedupe: opts.dedupe });
  let residual = 0;
  if (opts.relax) {
    // a dragged point's classes resist moving
    const find = M.classes(sk);
    const heavyCls = new Set(heavy.map(v => find(v)));
    const weights = {};
    for (const [v, i] of map.vix) if (heavyCls.has(find(v))) weights[i] = 1e6;
    const r = relax(map.req, weights);
    map.req.g0 = r.g0;
    residual = r.residual;
    // the relaxed drawing becomes the drawing
    for (const [v, i] of map.vix) sk.vars[v].val = r.g0[i];
  }
  const order = opts.order ? chooseOrder(map.req) : map.req.g0.map((_, i) => i);
  const p = permute(map.req, order);
  return { map, order, req: p.req, residual };
}

// the answer, read in the unpermuted variables
export function finish(sk, prep, ans) {
  const { map, order } = prep;
  const gc = new Array(order.length);
  if (ans.ok && ans.gc) ans.gc.forEach((x, k) => { gc[order[k]] = x; });
  const pins = (ans.pins || []).map(k => order[k]);
  const res = M.applyAnswer(sk, map, { ok: ans.ok, red: ans.red, pins, cls: ans.cls, own: ans.own, gc: ans.ok ? gc : [] });
  return { ...res, pinsCount: pins.length, nvars: order.length };
}

// do the values need Q19's dyadic rounding to certify?
export function hasNonDyadic(sk) {
  const dy = x => Number.isFinite(x) && Math.abs(x * 2 ** 40 - Math.round(x * 2 ** 40)) < 1e-6 && Number.isInteger(Math.round(x * 2 ** 40));
  for (const c of sk.cons) {
    if (c.kind === "angle") {
      if (Math.abs(c.value % 90) > 1e-12) return true;
    } else if (c.kind === "fix") {
      if (!dy(c.fx) || !dy(c.fy)) return true;
    } else if (c.value !== undefined && !Number.isInteger(c.value * 1024 * 1024 * 1024)) {
      // exact decimals like 3.6 are not dyadic
      const s = String(c.value);
      if (s.includes(".") || s.includes("e")) return true;
    }
  }
  return false;
}

// the example: a plate with a hole and a sloped edge
export function example() {
  const sk = M.emptySketch();
  const P = (x, y) => M.addPoint(sk, x, y);
  const p0 = P(0, 0), p1 = P(6.3, 0.2), p2 = P(6.1, 3.8), p3 = P(0.2, 4.1);
  const s0 = M.addSeg(sk, p0.id, p1.id), s1 = M.addSeg(sk, p1.id, p2.id);
  const s2 = M.addSeg(sk, p2.id, p3.id), s3 = M.addSeg(sk, p3.id, p0.id);
  const C = (k, e, x = {}) => M.addConstraint(sk, k, e, x);
  C("fix", [p0.id], { fx: 0, fy: 0 });
  C("horizontal", [p0.id, p1.id]);
  C("horizontal", [p3.id, p2.id]);
  C("vertical", [p1.id, p2.id]);
  C("vertical", [p0.id, p3.id]);
  C("distance", [p0.id, p1.id], { value: 6 });
  C("distance", [p1.id, p2.id], { value: 4 });
  const hc = P(2.1, 1.9), hole = M.addCircle(sk, hc.id, 0.9);
  C("hdistance", [p0.id, hc.id], { value: 2 });
  C("vdistance", [p0.id, hc.id], { value: 2 });
  C("radius", [hole.id], { value: 1 });
  const t = P(4.6, 6.0), s4 = M.addSeg(sk, p2.id, t.id);
  C("angle", [s0.id, s4.id], { value: 120 });
  C("distance", [p2.id, t.id], { value: 2.5 });
  const m = P(3.1, 0.3);
  C("midpoint", [m.id, s0.id]);
  return sk;
}
