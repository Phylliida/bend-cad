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
# - lib/blockpf.bend's block_ok (one_block below): from a drawing within d
#   of a regular solution x_b of the block, parameters x_z in the balls
#   pc +- pr (pr <= rho), and smallness conditions on the given constants
#   (Newton's s1, s2, s4 and elimination's small; w1 the box of radius rb
#   about the center below magnitude bb, w2 thR < 1, w3 the window's
#   cw <= 1/2, w4 (65/64) kappa <= 1/64), the solver's block returns BOk
#   of a certificate the block checker accepts, x_b in its box, n radii in
#   [0, rb], and the input parameters' balls (pc, pr) as its own.

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
import ../lib/blockpf.bend as BK
import ../spec/ring.bend as E
import ../spec/deriv.bend as DV
import ../lib/cert.bend as CK
import ../lib/certdef.bend as C
import ../lib/fvec.bend as FV

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

def one_block(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, NW.jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, NW.bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), NW.dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, NW.settle(~F, n, m, b, lam, ms, d, rho, p), NW.h6(~F, p)), +y0: List<&2, S.D>, +ly0: {M.len(~F, M.ofdv(~F, y0)) == n : Nat}, +hy0: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y0), xb), d), +q2: Nat, +hp2: {p == 1n+(1n+q2) : Nat}, +pr: List<&2, S.D>, +lpr: {M.len(~F, M.ofdv(~F, pr)) == m : Nat}, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rho), +w1: O.le(~F, O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), BK.rbc(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +w2: O.lt(F, BK.thrc(~F, n, m, b, lam, ms, d, rho, p), O.one(F)), +w3: O.le(~F, O.add(F, O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, m), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))), M.ofd(~F, NU.half())), +w4: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))))), O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F)))) -> BK.bgood(~F, n, eqs, xb, BK.rbc(~F, n, m, b, lam, ms, d, rho, p), pc, pr, NU.block(eqs, n, pc, pr, y0, p)):
  BK.block_ok(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y0, ly0, hy0, q2, hp2, pr, lpr, hpn, hzr, hpr, w1, w2, w3, w4)
