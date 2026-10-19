// bend-cad sketcher: an untrusted drawing relaxation. It moves the drawing
// (the solver's start values) as little as it can, in the least-squares
// sense, until every constraint nearly holds. The verified solver then
// certifies from there: the solver holds free variables at their drawn
// values and runs Newton from the drawing, and is complete for drawings
// near a solution (DESIGN §10.3-10.4). Nothing here is part of the
// certificate; it only edits the drawing the solver starts from.
//
// It reads the request toSolver builds: vars (kinds), ents
// ([id, construction, kind, a, b]), cons ([driven, kind, args...]) and g0.

function frac(s) {
  const t = String(s);
  if (t.includes("/")) {
    const [n, d] = t.split("/").map(Number);
    return n / d;
  }
  return Number(t);
}

// the residuals of each constraint at values v
function residuals(req, v) {
  const E = req.ents;
  const pt = i => ({ x: v[E[i][3]], y: v[E[i][4]] });
  const seg = i => [pt(E[i][3]), pt(E[i][4])];
  const circ = i => ({ c: pt(E[i][3]), r: v[E[i][4]] });
  const out = [];
  for (const c of req.cons) {
    if (c[0]) continue; // driven: measured, not imposed
    const k = c[1], a = c.slice(2);
    switch (k) {
      case 0: { const p = pt(a[0]), q = pt(a[1]); out.push(p.x - q.x, p.y - q.y); break; }
      case 1: out.push(pt(a[0]).y - pt(a[1]).y); break;
      case 2: out.push(pt(a[0]).x - pt(a[1]).x); break;
      case 3: { const p = circ(a[0]).c, q = circ(a[1]).c; out.push(p.x - q.x, p.y - q.y); break; }
      case 4: out.push(circ(a[0]).r - circ(a[1]).r); break;
      case 5: out.push(v[a[0]] - frac(a[1])); break;
      case 6: { const p = pt(a[0]), q = pt(a[1]); out.push(Math.hypot(q.x - p.x, q.y - p.y) - frac(a[2])); break; }
      case 7: { const p = pt(a[0]), q = pt(a[1]); out.push(q.x - p.x - frac(a[2])); break; }
      case 8: { const p = pt(a[0]), q = pt(a[1]); out.push(q.y - p.y - frac(a[2])); break; }
      case 9: out.push(circ(a[0]).r - frac(a[1])); break;
      case 10: out.push(2 * circ(a[0]).r - frac(a[1])); break;
      case 11: {
        const p = pt(a[0]), [s0, s1] = seg(a[1]);
        let dx = s1.x - s0.x, dy = s1.y - s0.y;
        if (a[2]) { dx = -dx; dy = -dy; }
        const L = Math.hypot(dx, dy) || 1e-12;
        const base = a[2] ? s1 : s0;
        out.push((dx * (p.y - base.y) - dy * (p.x - base.x)) / L - frac(a[3]));
        out.push(v[a[4]] - L);
        break;
      }
      case 12: {
        const [a0, a1] = seg(a[0]), [b0, b1] = seg(a[2]);
        let ax = a1.x - a0.x, ay = a1.y - a0.y, bx = b1.x - b0.x, by = b1.y - b0.y;
        if (a[1]) { ax = -ax; ay = -ay; }
        if (a[3]) { bx = -bx; by = -by; }
        const cs = frac(a[4]), sn = frac(a[5]);
        const rx = cs * ax - sn * ay, ry = sn * ax + cs * ay;
        const La = Math.hypot(ax, ay) || 1e-12, Lb = Math.hypot(bx, by) || 1e-12;
        out.push((rx * by - ry * bx) / (La * Lb));
        break;
      }
      case 13: { const [a0, a1] = seg(a[0]), [b0, b1] = seg(a[1]); out.push(Math.hypot(a1.x - a0.x, a1.y - a0.y) - Math.hypot(b1.x - b0.x, b1.y - b0.y)); break; }
      case 14: case 15: {
        const [a0, a1] = seg(a[0]), [b0, b1] = seg(a[1]);
        const ax = a1.x - a0.x, ay = a1.y - a0.y, bx = b1.x - b0.x, by = b1.y - b0.y;
        const L = (Math.hypot(ax, ay) * Math.hypot(bx, by)) || 1e-12;
        out.push((k === 14 ? ax * bx + ay * by : ax * by - ay * bx) / L);
        break;
      }
      case 16: {
        const p = pt(a[0]), [s0, s1] = seg(a[1]);
        const dx = s1.x - s0.x, dy = s1.y - s0.y, L = Math.hypot(dx, dy) || 1e-12;
        out.push((dx * (p.y - s0.y) - dy * (p.x - s0.x)) / L);
        break;
      }
      case 17: { const p = pt(a[0]), cc = circ(a[1]); out.push(Math.hypot(p.x - cc.c.x, p.y - cc.c.y) - cc.r); break; }
      case 18: { const m = pt(a[0]), [s0, s1] = seg(a[1]); out.push(m.x - (s0.x + s1.x) / 2, m.y - (s0.y + s1.y) / 2); break; }
      case 19: {
        const p = pt(a[0]), q = pt(a[1]), [s0, s1] = seg(a[2]);
        const dx = s1.x - s0.x, dy = s1.y - s0.y, L = Math.hypot(dx, dy) || 1e-12;
        const mx = (p.x + q.x) / 2, my = (p.y + q.y) / 2;
        out.push((dx * (my - s0.y) - dy * (mx - s0.x)) / L);
        out.push((dx * (q.x - p.x) + dy * (q.y - p.y)) / L);
        break;
      }
    }
  }
  return out;
}

// solve A x = b (A square, symmetric positive definite after damping)
function solveSPD(A, b) {
  const n = b.length;
  const M = A.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
    [M[c], M[p]] = [M[p], M[c]];
    const d = M[c][c];
    if (Math.abs(d) < 1e-300) continue;
    for (let r = 0; r < n; r++) {
      if (r === c) continue;
      const f = M[r][c] / d;
      if (f === 0) continue;
      for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
    }
  }
  return M.map((row, i) => (Math.abs(row[i]) < 1e-300 ? 0 : row[n] / row[i]));
}

// The relaxation: damped minimum-weighted-norm Gauss-Newton steps toward
// F(v) = 0, each moving the drawing as little as it can. weights[i] is how
// hard variable i resists moving (a dragged point resists strongly).
export function relax(req, weights = {}, iters = 40) {
  const v = req.g0.slice();
  const n = v.length;
  const w = Array.from({ length: n }, (_, i) => weights[i] ?? (req.vars[i] === 3 ? 1e-3 : 1));
  let F = residuals(req, v);
  const m = F.length;
  if (m === 0) return { g0: v, residual: 0 };
  let lam = 1e-9;
  for (let it = 0; it < iters; it++) {
    const norm = Math.hypot(...F);
    if (norm < 1e-13) break;
    // numerical Jacobian
    const J = Array.from({ length: m }, () => new Array(n).fill(0));
    for (let j = 0; j < n; j++) {
      const h = 1e-7 * Math.max(1, Math.abs(v[j]));
      const old = v[j];
      v[j] = old + h;
      const Fp = residuals(req, v);
      v[j] = old;
      for (let i = 0; i < m; i++) J[i][j] = (Fp[i] - F[i]) / h;
    }
    // (J W^-1 J^T + lam I) y = F, step = -W^-1 J^T y
    const A = Array.from({ length: m }, (_, i) => Array.from({ length: m }, (_, k) => {
      let s = 0;
      for (let j = 0; j < n; j++) s += J[i][j] * J[k][j] / w[j];
      return s + (i === k ? lam : 0);
    }));
    const y = solveSPD(A, F);
    const step = Array.from({ length: n }, (_, j) => {
      let s = 0;
      for (let i = 0; i < m; i++) s += J[i][j] * y[i];
      return -s / w[j];
    });
    // backtrack until the residual drops
    let t = 1, improved = false;
    for (let tries = 0; tries < 12; tries++) {
      const v2 = v.map((x, j) => x + t * step[j]);
      const F2 = residuals(req, v2);
      if (Math.hypot(...F2) < norm) {
        for (let j = 0; j < n; j++) v[j] = v2[j];
        F = F2;
        improved = true;
        break;
      }
      t /= 2;
    }
    if (!improved) {
      lam = lam * 100 + 1e-6;
      if (lam > 1e6) break;
    } else {
      lam = Math.max(lam / 10, 1e-12);
    }
  }
  return { g0: v, residual: Math.hypot(...F) };
}

// Variable order. The solver's pins are the variables its matching
// leaves over, latest variables matched first, so the earliest variables
// become pins (DESIGN §10.4). At the relaxed drawing we choose, by
// Gaussian elimination with column pivoting on the Jacobian, a
// well-conditioned set of variables to solve for, and order the others
// first. This changes only the order of the variables, never the sketch.
export function chooseOrder(req) {
  const n = req.g0.length;
  const v = req.g0.slice();
  const F = residuals(req, v);
  const m = F.length;
  const J = Array.from({ length: m }, () => new Array(n).fill(0));
  for (let j = 0; j < n; j++) {
    const h = 1e-7 * Math.max(1, Math.abs(v[j]));
    const old = v[j];
    v[j] = old + h;
    const Fp = residuals(req, v);
    v[j] = old;
    for (let i = 0; i < m; i++) J[i][j] = (Fp[i] - F[i]) / h;
  }
  // scale each row so the pivots compare fairly
  for (const row of J) {
    const s = Math.max(...row.map(Math.abs));
    if (s > 0) for (let j = 0; j < n; j++) row[j] /= s;
  }
  const solved = [];
  const used = new Set();
  const rows = J.map(r => r.slice());
  for (let r = 0; r < m; r++) {
    // the largest remaining entry in any unused column of any remaining row
    let best = 0, bi = -1, bj = -1;
    for (let i = 0; i < rows.length; i++) {
      if (!rows[i]) continue;
      for (let j = 0; j < n; j++) {
        if (used.has(j)) continue;
        const a = Math.abs(rows[i][j]);
        if (a > best) { best = a; bi = i; bj = j; }
      }
    }
    if (bi < 0 || best < 1e-9) break;
    used.add(bj); solved.push(bj);
    const pr = rows[bi];
    rows[bi] = null;
    for (let i = 0; i < rows.length; i++) {
      if (!rows[i]) continue;
      const f = rows[i][bj] / pr[bj];
      if (f !== 0) for (let j = 0; j < n; j++) rows[i][j] -= f * pr[j];
    }
  }
  const rest = [];
  for (let j = 0; j < n; j++) if (!used.has(j)) rest.push(j);
  return rest.concat(solved);
}

// the request with its variables in a new order: order[k] is the old
// index of the new variable k
export function permute(req, order) {
  const inv = new Array(order.length);
  order.forEach((old, k) => { inv[old] = k; });
  const vars = order.map(o => req.vars[o]);
  const g0 = order.map(o => req.g0[o]);
  const ents = req.ents.map(e => {
    switch (e[2]) {
      case 0: return [e[0], e[1], 0, inv[e[3]], inv[e[4]]];
      case 2: return [e[0], e[1], 2, e[3], inv[e[4]]];
      default: return e.slice();
    }
  });
  const cons = req.cons.map(c => {
    const k = c[1], a = c.slice(2);
    if (k === 5) return [c[0], 5, inv[a[0]], a[1]];
    if (k === 11) return [c[0], 11, a[0], a[1], a[2], a[3], inv[a[4]]];
    return c.slice();
  });
  return { req: { vars, ents, cons, g0 }, inv };
}
