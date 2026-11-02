// The small sketches PLAN-sk13b B8 adds to the regression (the direction
// layer), built with the page's own model (gui/model.js) and written as
// GUI exports NAME.json; gen.sh then makes their solver inputs. Usage: bun
// b8.mjs (from here). Drawings are near, not on, a solution: the page
// relaxes them first.
import * as M from "../../gui/model.js";
import { writeFileSync } from "fs";

const out = {};
const sketch = (name, f) => { const sk = M.emptySketch(); f(sk); out[name] = sk; };
const P = (sk, x, y) => M.addPoint(sk, x, y).id;
const S = (sk, p, q) => M.addSeg(sk, p, q).id;
const C = (sk, k, e, x = {}) => M.addConstraint(sk, k, e, x);

// a quadrilateral with four right angles: the fourth is implied, where
// the sides between have nonzero length
sketch("right-angles", sk => {
  const a = P(sk, 0, 0), b = P(sk, 4, 0.1), c = P(sk, 4.1, 3), d = P(sk, -0.1, 3.1);
  const s0 = S(sk, a, b), s1 = S(sk, b, c), s2 = S(sk, c, d), s3 = S(sk, d, a);
  C(sk, "perpendicular", [s0, s1]);
  C(sk, "perpendicular", [s1, s2]);
  C(sk, "perpendicular", [s2, s3]);
  C(sk, "perpendicular", [s3, s0]);
});

// three separate segments, a chain of parallels closed: the last is
// implied, where the middle one has nonzero length
sketch("parallels-closed", sk => {
  const a = S(sk, P(sk, 0, 0), P(sk, 3, 1));
  const b = S(sk, P(sk, 0, 2), P(sk, 3, 3.1));
  const c = S(sk, P(sk, 1, 4), P(sk, 4, 4.9));
  C(sk, "parallel", [a, b]);
  C(sk, "parallel", [b, c]);
  C(sk, "parallel", [c, a]);
});

// two segments parallel, then perpendicular (slowsketches 8 and 9's #66
// and #67 in small): red, unless one of them has length 0
sketch("par-perp", sk => {
  const a = S(sk, P(sk, 0, 0), P(sk, 3, 0.2));
  const b = S(sk, P(sk, 0, 2), P(sk, 3, 2.5));
  C(sk, "parallel", [a, b]);
  C(sk, "perpendicular", [a, b]);
});

// a horizontal segment, a parallel to it, then that one vertical: red
sketch("h-par-v", sk => {
  const p = P(sk, 0, 0), q = P(sk, 3, 0.1), r = P(sk, 0, 2), t = P(sk, 3, 2.3);
  const a = S(sk, p, q), b = S(sk, r, t);
  C(sk, "horizontal", [p, q]);
  C(sk, "parallel", [a, b]);
  C(sk, "vertical", [r, t]);
});

// two points on a segment's line, then the segment between them parallel
// to it: implied (a constant combination of the two OnLines)
sketch("online-par", sk => {
  const p = P(sk, 0, 0), q = P(sk, 4, 1);
  const a = S(sk, p, q);
  const r = P(sk, 1, 0.4), t = P(sk, 3, 0.6);
  C(sk, "onLine", [r, a]);
  C(sk, "onLine", [t, a]);
  const b = S(sk, r, t);
  C(sk, "parallel", [a, b]);
});

// a Coincident collapsing a segment, then a Parallel on it: implied,
// vacuously (a point is parallel to everything)
sketch("collapse-par", sk => {
  const p = P(sk, 0, 0), q = P(sk, 0.1, 0.1);
  const a = S(sk, p, q), b = S(sk, P(sk, 1, 2), P(sk, 4, 3));
  C(sk, "coincident", [p, q]);
  C(sk, "parallel", [a, b]);
});

// the same in the other order: the Parallel is kept, then the Coincident
// makes it hold everywhere, so the system is singular and refused
// (PLAN-sk13b decision 4)
sketch("par-collapse", sk => {
  const p = P(sk, 0, 0), q = P(sk, 0.1, 0.1);
  const a = S(sk, p, q), b = S(sk, P(sk, 1, 2), P(sk, 4, 3));
  C(sk, "parallel", [a, b]);
  C(sk, "coincident", [p, q]);
});

// three segments turned by 90, 90 and 180 degrees, a cycle: the last
// Angle's equation is implied, but its side (the turn is not the
// opposite one) is not a constant combination, so it is kept
sketch("angle-cycle", sk => {
  const a = S(sk, P(sk, 0, 0), P(sk, 3, 0.2));
  const b = S(sk, P(sk, 4, 0), P(sk, 4.1, 3));
  const c = S(sk, P(sk, 3, 4), P(sk, 0, 4.2));
  C(sk, "angle", [a, b], { value: 90 });
  C(sk, "angle", [b, c], { value: 90 });
  C(sk, "angle", [c, a], { value: 180 });
});

// the same with 60, 60 and 240 degrees: sent as rotations rounded to
// dyadics, whose product is not 1, so the last is honestly red
sketch("angle-rounded", sk => {
  const a = S(sk, P(sk, 0, 0), P(sk, 3, 0.2));
  const b = S(sk, P(sk, 4, 0), P(sk, 5.4, 2.6));
  const c = S(sk, P(sk, 3, 4), P(sk, 1.6, 6.5));
  C(sk, "angle", [a, b], { value: 60 });
  C(sk, "angle", [b, c], { value: 60 });
  C(sk, "angle", [c, a], { value: 240 });
});

// AUDIT-sk13b-plan.md's sketch A: Parallels only; #2 is implied where s1
// has nonzero length
sketch("audit-a", sk => {
  const A = P(sk, 0, 0), B = P(sk, 2, 0.6), Cc = P(sk, 4, 1.1), D = P(sk, 0, 3), E = P(sk, 3, 3.8);
  const h = S(sk, D, E), s1 = S(sk, A, B), s2 = S(sk, B, Cc), s3 = S(sk, A, Cc);
  C(sk, "parallel", [h, s1]);
  C(sk, "parallel", [s1, s2]);
  C(sk, "parallel", [h, s3]);
});

// its sketch B: a split edge; #3 is implied where h and s1 have nonzero
// length
sketch("audit-b", sk => {
  const A = P(sk, 0, 0), B = P(sk, 2, 0.2), Cc = P(sk, 4, -0.1), D = P(sk, 0, 3), E = P(sk, 3, 3.2);
  const h = S(sk, D, E), s1 = S(sk, A, B), s2 = S(sk, B, Cc);
  C(sk, "horizontal", [D, E]);
  C(sk, "parallel", [h, s1]);
  C(sk, "parallel", [s1, s2]);
  C(sk, "horizontal", [A, Cc]);
});

// its sketch V: a horizontal h, s parallel to it, then s 3 high: red,
// unless h has length 0
sketch("audit-v", sk => {
  const A = P(sk, 0, 0), B = P(sk, 3, 0.4), D = P(sk, 0, 3), E = P(sk, 3, 3.1);
  const h = S(sk, D, E), s = S(sk, A, B);
  C(sk, "horizontal", [D, E]);
  C(sk, "parallel", [h, s]);
  C(sk, "vdistance", [A, B], { value: 3 });
});

for (const [name, sk] of Object.entries(out)) writeFileSync(name + ".json", JSON.stringify(sk));
console.log(Object.keys(out).join(" "));
