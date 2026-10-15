# bend-cad: norms and perturbation under solve_complete (DESIGN §10.4,
# C3c), restated here so the gate checks lib/normpf.bend until the
# completeness proof imports it. In every ordered field, with |v| a
# vector's largest |entry| and |A| (over n columns) a matrix's largest row
# sum of |entries| among its first n columns:
# - |A v| <= |A| |v| for v of length n;
# - if J (n rows) has an inverse with n rows and norm at most c, then
#   |v| <= c |J v| for v of length n;
# - perturbation: if moreover |J' - J| <= d with 2 c d <= 1, and J' is
#   square (n rows of n entries), then J' has an inverse with n rows and
#   norm at most 2c.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/gjpf.bend as GJ
import ../lib/normpf.bend as NP

def norm_matvec(~F: O.OField, +a: M.Mat(~F), +n: Nat, +v: M.Vec(~F), lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, NP.vn(~F, M.matvec(~F, a, v)), O.mul(F, NP.mnorm(~F, a, n), NP.vn(~F, v))):
  NP.mv_n(~F, a, n, v, lv)

def inverse_bounds_below(~F: O.OField, +j: M.Mat(~F), +n: Nat, +c: O.C(F), h: NP.InvB(~F, j, n, c), +hj: {GJ.nrows(~F, j) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, NP.vn(~F, v), O.mul(F, c, NP.vn(~F, M.matvec(~F, j, v)))):
  NP.lowb(~F, j, n, c, h, hj, v, lv)

def perturbation(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +c: O.C(F), +d: O.C(F), +h: NP.InvB(~F, j, n, c), +hj: {GJ.nrows(~F, j) == n : Nat}, +hj2: {GJ.nrows(~F, j2) == n : Nat}, hw2: GJ.All(~(i => GJ.roww(~F, j2, n, i)), n), +hd: O.le(~F, NP.mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d), +hcd: O.le(~F, O.add(F, O.mul(F, c, d), O.mul(F, c, d)), O.one(F))) -> NP.InvB(~F, j2, n, O.add(F, c, c)):
  NP.pert(~F, j, j2, n, c, d, h, hj, hj2, hw2, hd, hcd)
