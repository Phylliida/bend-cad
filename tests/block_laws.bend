# bend-cad: one block at P under solve_complete (DESIGN §10.4, C5),
# restated here so the gate checks lib/apxpf.bend and lib/nwtpf.bend
# (importing a module checks all of it) until the completeness proof
# imports them. In every ordered field F:
# - every embedding of the dyadics is ofd;
# - C4's entrywise bound on I - A J gives |v - A J v| <= n e |v|;
# - an inequality proved in F passes the checker's comparison, in any K;
# - lib/nwtpf.bend's newton_ok: from a drawing within d of a regular
#   solution x_b of the block (parameters within rho), the solver's
#   Newton never meets a singular Jacobian, settles by its second step,
#   and returns a point within en = 8h + e1 of x_b (h = 2^-(p+1)).

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../lib/kinst.bend as KI
import ../lib/karith.bend as KA
import ../lib/fring.bend as FR
import ../lib/normpf.bend as NP
import ../lib/dgjpf.bend as DG
import ../lib/gjpf.bend as GJ
import ../lib/apxpf.bend as AP
import ../lib/nwtpf.bend as NW

def dyadic_embedding(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, x: S.D) -> {N.emap(KI.dnum(), F, H, x) == M.ofd(~F, x) : O.C(F)}:
  AP.hofd(~F, ~H, x)

def inverse_vector_form(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, NP.vn(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)))), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v))):
  AP.vform(~F, n, jm, A, e, he, ha, hA, v, lv)

def compare_complete(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.kle(~K, a, b) == True{} : Bool}:
  AP.kle_of(~K, ~F, ~H, a, b, h)

def newton_settle(~F: O.OField, +p: Nat) -> O.le(~F, O.zero(F), NW.h8(~F, p)):
  NW.h8_nn(~F, p)
