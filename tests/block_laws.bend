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
# - lib/radpf.bend: every radius r <= rb with S <= r/2 passes the block
#   checker (window_ok); the solver's radius search returns one with
#   (65/64) S <= r <= U (rs_init); and |yc - x_b| <= (65/64) S (inbox_ok).
#   Restated here: the search's arithmetic (1/2 + 1/2 = 1, 16 steps of
#   1/16 make 1, the dyadics' order is K's).

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../lib/kinst.bend as KI
import ../lib/numer.bend as NU
import ../lib/karith.bend as KA
import ../lib/fring.bend as FR
import ../lib/normpf.bend as NP
import ../lib/dgjpf.bend as DG
import ../lib/gjpf.bend as GJ
import ../lib/apxpf.bend as AP
import ../lib/nwtpf.bend as NW
import ../lib/radpf.bend as RD

def dyadic_embedding(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, x: S.D) -> {N.emap(KI.dnum(), F, H, x) == M.ofd(~F, x) : O.C(F)}:
  AP.hofd(~F, ~H, x)

def inverse_vector_form(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, NP.vn(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)))), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v))):
  AP.vform(~F, n, jm, A, e, he, ha, hA, v, lv)

def compare_complete(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.kle(~K, a, b) == True{} : Bool}:
  AP.kle_of(~K, ~F, ~H, a, b, h)

def newton_settle(~F: O.OField, +p: Nat) -> O.le(~F, O.zero(F), NW.h8(~F, p)):
  NW.h8_nn(~F, p)

def half_twice(~F: O.OField) -> {O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())) == O.one(F) : O.C(F)}:
  RD.half_two(~F)

def sixteen_steps(~F: O.OField) -> {O.mul(F, FR.ofn(~F, 16n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})) == O.one(F) : O.C(F)}:
  RD.n16_eq(~F)

def dyadic_order(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +a: S.D, +b: S.D, h: {KA.kle(~KI.dnum(), a, b) == True{} : Bool}) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, b)):
  RD.dle(~F, ~H, a, b, h)
