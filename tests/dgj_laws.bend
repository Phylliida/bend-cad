# bend-cad: the solver's rounded Gauss-Jordan under solve_complete
# (DESIGN §10.4, C4), restated here so the gate checks lib/dgjpf.bend until
# the completeness proof imports it. In every ordered field F (dyadics read
# through ofd):
# - the partial-pivoting search dpivot returns a row r >= c whose |entry c|
#   bounds every candidate's (rows c and below), or None only when every
#   candidate in column c is 0;
# - dinverse(n, w, a), for a dyadic n x n matrix a read as J, with
#   |J_ij| <= g and an inverse of norm at most beta, returns some A with n
#   rows and every entry of I - A J at most (KD_n + KP_n) 2^-w, once
#   2^-w A_c <= 1 for every column c. KD, KP and A_c are explicit in n, g
#   and beta (DG.kst, DG.acoef); the elimination never meets a zero pivot.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/gjpf.bend as GJ
import ../lib/normpf.bend as NP
import ../lib/numer.bend as NU
import ../lib/dgjpf.bend as DG

def pivot_search(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat) -> DG.pfin(~F, t, c, c, GJ.nrows(~F, M.ofdm(~F, t)), NU.dpivot(t, c, c, 0n, None{}, NU.dzero())):
  DG.pivot_ok(~F, t, c)

def dinverse_complete(~F: O.OField, +n: Nat, +w: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +bb: O.C(F), +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hJ: NP.InvB(~F, M.ofdm(~F, a), n, bb), +hj: DG.mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +hsm: GJ.All(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), DG.acoef(~F, n, bb, q, DG.kst(~F, n, g, bb, q))), O.one(F))), n)) -> DG.dinv_res(~F, n, M.ofdm(~F, a), O.add(F, O.mul(F, DG.kd(~F, DG.kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, DG.kp(~F, DG.kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NU.dinverse(n, w, a)):
  DG.dinverse_ok(~F, n, w, a, g, bb, hw, hjn, hJ, hj, hg, hb, hsm)
