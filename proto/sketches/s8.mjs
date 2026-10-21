// The small sketches PLAN-sk13a S8 adds to the regression, built with the
// page's own model (gui/model.js) and written as GUI exports NAME.json;
// gen.sh then makes their solver inputs. Usage: bun s8.mjs (from here).
import * as M from "../../gui/model.js";
import { writeFileSync } from "fs";

const out = {};
const sketch = (name, f) => { const sk = M.emptySketch(); f(sk); out[name] = sk; };
const P = (sk, x, y) => M.addPoint(sk, x, y).id;
const S = (sk, p, q) => M.addSeg(sk, p, q).id;
const C = (sk, k, e, x = {}) => M.addConstraint(sk, k, e, x);

// x0 = 0, then x1 - x0 = 1, x2 - x1 = 1 and x2 - x0 = 2 (implied) or 3
for (const [name, last] of [["hchain", 2], ["hchain-bad", 3]]) {
  sketch(name, sk => {
    const a = P(sk, 0, 0), b = P(sk, 1, 0.1), c = P(sk, 2, -0.1);
    C(sk, "fix", [a], { fx: 0, fy: 0 });
    C(sk, "hdistance", [a, b], { value: 1 });
    C(sk, "hdistance", [b, c], { value: 1 });
    C(sk, "hdistance", [a, c], { value: last });
  });
}

// a midpoint whose y equation the two horizontals already give
sketch("midpoint-part", sk => {
  const p = P(sk, 0, 0), q = P(sk, 4, 0), m = P(sk, 2, 0.2);
  const s = S(sk, p, q);
  C(sk, "horizontal", [p, q]);
  C(sk, "horizontal", [p, m]);
  C(sk, "midpoint", [m, s]);
});

// a distance 5, then the same pair at -5
sketch("distance-neg", sk => {
  const p = P(sk, 0, 0), q = P(sk, 3, 4);
  C(sk, "distance", [p, q], { value: 5 });
  C(sk, "distance", [p, q], { value: -5 });
});

// a radius 3, then -5 (the circle keeps r > 0)
sketch("radius-neg", sk => {
  const o = P(sk, 0, 0), c = M.addCircle(sk, o, 3).id;
  C(sk, "radius", [c], { value: 3 });
  C(sk, "radius", [c], { value: -5 });
});

// an angle of 30 degrees, then of 210 (the opposite direction; both read
// the segments as drawn, rev false, else the page would read 210 as the
// same lines at 30)
sketch("angle-opposite", sk => {
  const o = P(sk, 0, 0), a = P(sk, 4, 0), b = P(sk, 3.4, 2);
  const s = S(sk, o, a), t = S(sk, o, b);
  C(sk, "angle", [s, t], { value: 30, rev: false });
  C(sk, "angle", [s, t], { value: 210, rev: false });
});

// a segment as long as itself
sketch("equal-self", sk => {
  const p = P(sk, 0, 0), q = P(sk, 3, 1), s = S(sk, p, q);
  C(sk, "equalLength", [s, s]);
});

// y equal, and 3 apart in y
sketch("horizontal-vdist", sk => {
  const p = P(sk, 0, 0), q = P(sk, 3, 0.5);
  C(sk, "horizontal", [p, q]);
  C(sk, "vdistance", [p, q], { value: 3 });
});

// the same coincidence twice
sketch("coincident-twice", sk => {
  const p = P(sk, 0, 0), q = P(sk, 0.1, 0.1);
  C(sk, "coincident", [p, q]);
  C(sk, "coincident", [p, q]);
});

// the v4 audit's support case: Vertical(A, B), Coincident(A, B), then
// HDistance(A, B) = 1, whose irreducible support is the Coincident alone
sketch("vch-support", sk => {
  const a = P(sk, 0, 0), b = P(sk, 0.1, 1);
  C(sk, "vertical", [a, b]);
  C(sk, "coincident", [a, b]);
  C(sk, "hdistance", [a, b], { value: 1 });
});

// x - x + y: a point-line distance from the segment's own first endpoint.
// Its first equation mentions both points' coordinates but depends only
// on the segment's length variable l (the cross product is identically 0),
// so with distance 1 it says -l = 0 against l > 0: it cannot hold
sketch("cancel", sk => {
  const p = P(sk, 0, 0), q = P(sk, 3, 1), s = S(sk, p, q);
  C(sk, "lineDistance", [p, s], { value: 1 });
});

for (const [name, sk] of Object.entries(out)) writeFileSync(name + ".json", JSON.stringify(sk));
console.log(Object.keys(out).join(" "));
