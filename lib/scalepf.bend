# bend-cad: one block in scale form, for solve_complete (DESIGN §10.4
# "C6 plan", C6a). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/scalepf.draft lib/scalepf.bend
#
# Write h = 2^-(p+1) (Newton's rounding), u = 2^-(p+32) (elimination's)
# and t = 2^-(p/2) (Y's): u <= h <= t <= 1. With the drawing within d <= h
# of x_b and the parameters' radii rho <= h T, every constant of
# lib/blockpf.bend's block_ok is peval of a reflected expression
# (lib/pmono.bend) over the small atoms d, rho, h, u, v and the block's
# fixed constants, so each smallness hypothesis follows from t Q < 1, with
# Q = qblk(n, m, b, lam, ms, T) independent of p, d and rho (block_sc),
# and the block's radius bound is at most h Phi, Phi = phib(...) >= T
# (rb_sc). Two scales: t for the w's, s1, s2 and C4's acoef; h (v fixed)
# for the radius and the settle test.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/big.bend as SB
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ./karith.bend as KA
import ./cert.bend as CK
import ./certdef.bend as C
import ./kinst.bend as KI
import ./numer.bend as NU
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./qemb.bend as QE
import ./nat.bend as LN
import ./natord.bend as NO
import ./listpf.bend as L
import ./gjpf.bend as GJ
import ./normpf.bend as NP
import ./dgjpf.bend as DG
import ./apxpf.bend as AP
import ./nwtpf.bend as NW
import ./radpf.bend as RD
import ./blockpf.bend as BK
import ./pmono.bend as PM
import ./real.bend as RL

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Scales
# ------

def le_of_Le.go(+a: Nat, +b: Nat, +k: Nat, e: {Nat.add(a, k) == b : Nat}) -> {KA.natle(a, b) == True{} : Bool}:
  %e : {KA.natle(a, _) == True{} : Bool}
  KA.natle_add_r(a, k)

def le_of_Le(+a: Nat, +b: Nat, h: SB.Le(a, b)) -> {KA.natle(a, b) == True{} : Bool}:
  match h:
    case (k, e):
      le_of_Le.go(a, b, k, e)

def natle_s(p: Nat) -> {KA.natle(p, 1n+p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      natle_s(q)

# p/2 <= p + 1
def div2_le(+p: Nat) -> {KA.natle(Nat.div(p, 2n), 1n+p) == True{} : Bool}:
  +q = Nat.div(p, 2n)
  KA.natle_trans(q, p, 1n+p, KA.natle_trans(q, Nat.mul(q, 2n), p, (%LN.mul_succ(q, 1n) : {KA.natle(q, _) == True{} : Bool}
    KA.natle_add_r(q, Nat.mul(q, 1n))), le_of_Le(Nat.mul(q, 2n), p, NO.divb_le(p, 1n))), natle_s(p))

# p + 1 <= p + 32
def wb_le(+p: Nat) -> {KA.natle(1n+p, NU.wbits(p)) == True{} : Bool}:
  %LN.add_succ(p, 31n) : {KA.natle(1n+p, _) == True{} : Bool}
  KA.natle_add_r(p, 31n)


# 2^-b <= 2^-a for a <= b
def pw_le(~F: O.OField, a: Nat, b: Nat, +h: {KA.natle(a, b) == True{} : Bool}) -> O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, a})):
  match a b:
    case 0n b:
      %DM.ofd_one(~F) : O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), _)
      DG.u_le1(~F, b)
    case 1n++i 0n:
      absurd(O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 0n}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+i})), KA.ft(h))
    case 1n++i 1n++j:
      %DM.ofd_mul(~F, S.D{S.Zpos{S.XH{}}, 1n}, S.D{S.Zpos{S.XH{}}, j}) : O.le(~F, _, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+i}))
      %DM.ofd_mul(~F, S.D{S.Zpos{S.XH{}}, 1n}, S.D{S.Zpos{S.XH{}}, i}) : O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, j})), _)
      FV.mul_le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, j}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, i}), DG.u_nn(~F, 1n), pw_le(~F, i, j, h))


def h_le_t(~F: O.OField, +p: Nat) -> O.le(~F, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n))):
  pw_le(~F, Nat.div(p, 2n), 1n+p, div2_le(p))

def u_le_h(~F: O.OField, +p: Nat) -> O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), NW.hnw(~F, p)):
  pw_le(~F, 1n+p, NU.wbits(p), wb_le(p))

def t_le1(~F: O.OField, +p: Nat) -> O.le(~F, AP.vbit(~F, Nat.div(p, 2n)), O.one(F)):
  DG.u_le1(~F, Nat.div(p, 2n))

# Atoms
# -----
# 0 d, 1 rho, 2 h, 3 u, 4 v (small; v is fixed, bound 1, at scale h),
# 5 one, 6 n, 7 m, 8 ms, 9 lam, 10 b, 11 kd, 12 kp (C4's constants),
# 13 17/16, 14 2^-7, 15 65/64 (fixed). The bounds: 1 for d, h, u, v and
# T (tt) for rho, so rho <= h T.


def fixd(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F)) -> List<&2, PM.Atm<O.C(F)>>:
  Con{PM.Atm{O.one(F), O.one(F), False{}}, Con{PM.Atm{FR.ofn(~F, n), FR.ofn(~F, n), False{}}, Con{PM.Atm{FR.ofn(~F, m), FR.ofn(~F, m), False{}}, Con{PM.Atm{ms, ms, False{}}, Con{PM.Atm{lam, lam, False{}}, Con{PM.Atm{b, b, False{}}, Con{PM.Atm{DG.kd(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), DG.kd(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), False{}}, Con{PM.Atm{DG.kp(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), DG.kp(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), False{}}, Con{PM.Atm{M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), False{}}, Con{PM.Atm{M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), False{}}, Con{PM.Atm{M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), False{}}, Nil{}}}}}}}}}}}}

# at scale t = v
def envt(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> List<&2, PM.Atm<O.C(F)>>:
  Con{PM.Atm{d, O.one(F), True{}}, Con{PM.Atm{rho, tt, True{}}, Con{PM.Atm{NW.hnw(~F, p), O.one(F), True{}}, Con{PM.Atm{M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), O.one(F), True{}}, Con{PM.Atm{AP.vbit(~F, Nat.div(p, 2n)), O.one(F), True{}}, fixd(~F, n, m, b, lam, ms)}}}}}

# at scale h
def envh(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> List<&2, PM.Atm<O.C(F)>>:
  Con{PM.Atm{d, O.one(F), True{}}, Con{PM.Atm{rho, tt, True{}}, Con{PM.Atm{NW.hnw(~F, p), O.one(F), True{}}, Con{PM.Atm{M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), O.one(F), True{}}, Con{PM.Atm{AP.vbit(~F, Nat.div(p, 2n)), O.one(F), False{}}, fixd(~F, n, m, b, lam, ms)}}}}}

# the bounds (both scales)
def cts(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F)) -> List<&2, O.C(F)>:
  Con{O.one(F), Con{tt, Con{O.one(F), Con{O.one(F), Con{O.one(F), Con{O.one(F), Con{FR.ofn(~F, n), Con{FR.ofn(~F, m), Con{ms, Con{lam, Con{b, Con{DG.kd(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), Con{DG.kp(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), Con{M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), Con{M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), Con{M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), Nil{}}}}}}}}}}}}}}}}}


# Reflected constants (lib/nwtpf.bend, lib/blockpf.bend)
# ------------------------------------------------------

def at(i: Nat) -> PM.PE:
  PM.PAt{i}

def pp(x: PM.PE, y: PM.PE) -> PM.PE:
  PM.PPlus{x, y}

def pt(x: PM.PE, y: PM.PE) -> PM.PE:
  PM.PTimes{x, y}

def r_bt2() -> PM.PE:
  pp(at(10n), at(10n))

def r_ea() -> PM.PE:
  pp(pt(at(11n), at(3n)), pt(at(12n), at(3n)))

def r_al() -> PM.PE:
  pt(pp(at(5n), pt(at(6n), r_ea())), r_bt2())

def r_g0c() -> PM.PE:
  pp(pt(pt(at(6n), at(8n)), at(0n)), pt(pt(at(7n), at(8n)), at(1n)))

def r_dl0() -> PM.PE:
  pp(pt(r_al(), r_g0c()), at(2n))

def r_e1() -> PM.PE:
  pp(at(2n), pp(pp(pt(pt(at(6n), r_ea()), at(0n)), pt(r_al(), pt(pt(at(6n), pt(at(9n), pp(at(0n), at(1n)))), at(0n)))), pt(r_al(), pt(pt(at(7n), at(8n)), at(1n)))))

def r_h6() -> PM.PE:
  pp(pp(pp(at(2n), at(2n)), pp(at(2n), at(2n))), pp(at(2n), at(2n)))

def r_h8() -> PM.PE:
  pp(pp(at(2n), at(2n)), r_h6())

def r_en() -> PM.PE:
  pp(r_h8(), r_e1())

def r_dx() -> PM.PE:
  pp(pp(at(0n), at(1n)), pp(r_en(), r_dl0()))

def r_settle() -> PM.PE:
  pp(pp(pt(pt(at(6n), r_ea()), at(2n)), pt(r_al(), pt(pt(at(6n), pt(at(9n), r_dl0())), at(2n)))), pp(pt(r_al(), pt(pt(at(6n), pt(at(9n), r_dl0())), pt(r_bt2(), r_g0c()))), pt(r_al(), pt(pt(at(6n), at(8n)), pt(pt(at(6n), r_ea()), pt(r_bt2(), r_g0c()))))))

def r_ync() -> PM.PE:
  pt(pp(at(5n), at(4n)), r_al())

def r_thlc() -> PM.PE:
  pp(pt(at(6n), r_ea()), pt(pt(at(4n), r_al()), pt(at(6n), at(8n))))

def r_thrc() -> PM.PE:
  pp(pt(pt(at(6n), at(8n)), pt(pt(at(6n), r_ea()), r_bt2())), pt(pt(at(6n), at(8n)), pt(at(4n), r_al())))

def r_sbc() -> PM.PE:
  pp(pt(r_ync(), pp(pt(pt(at(6n), at(8n)), r_en()), pt(pt(at(7n), at(8n)), at(1n)))), pt(r_ync(), pt(pt(at(7n), at(8n)), at(1n))))

def r_ubc() -> PM.PE:
  pt(pt(at(13n), pp(at(5n), at(14n))), pp(r_sbc(), r_sbc()))

def r_rbc() -> PM.PE:
  pp(r_ubc(), at(1n))

# the smallness hypotheses' left sides
def r_s1() -> PM.PE:
  pp(r_dx(), r_dx())

def r_s2() -> PM.PE:
  pp(pt(at(10n), pt(at(6n), pt(at(9n), r_dx()))), pt(at(10n), pt(at(6n), pt(at(9n), r_dx()))))

def r_w1() -> PM.PE:
  pp(r_dx(), r_rbc())

def r_w3() -> PM.PE:
  pp(pp(r_thlc(), pt(r_ync(), pt(at(6n), pt(at(9n), r_rbc())))), pt(r_ync(), pt(at(7n), pt(at(9n), r_rbc()))))

def r_w4() -> PM.PE:
  pt(at(15n), pp(r_thlc(), pt(r_ync(), pt(at(6n), pt(at(9n), r_dx())))))

def cv_s1(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), NW.dx(~F, n, m, b, lam, ms, d, rho, p)) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_s1()) : O.C(F)}:
  {==}

def cv_s2(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p))))) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_s2()) : O.C(F)}:
  {==}

def cv_s4(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {NW.settle(~F, n, m, b, lam, ms, d, rho, p) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_settle()) : O.C(F)}:
  {==}

def cv_w1(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), BK.rbc(~F, n, m, b, lam, ms, d, rho, p)) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_w1()) : O.C(F)}:
  {==}

def cv_w2(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {BK.thrc(~F, n, m, b, lam, ms, d, rho, p) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_thrc()) : O.C(F)}:
  {==}

def cv_w3(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {O.add(F, O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, m), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_w3()) : O.C(F)}:
  {==}

def cv_w4(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))))) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_w4()) : O.C(F)}:
  {==}

def cv_rb(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +tt: O.C(F)) -> {BK.rbc(~F, n, m, b, lam, ms, d, rho, p) == PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), r_rbc()) : O.C(F)}:
  {==}

# The atoms' bounds
# -----------------


def fx(~F: O.OField, +x: O.C(F), +s: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> PM.At(~F, x, x, False{}, s):
  (hx, (hx, FO.le_refl(~F, x)))

def fixd_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +s: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms)) -> PM.Bnd(~F, fixd(~F, n, m, b, lam, ms), s):
  +hk = DG.kst_nn(~F, n, ms, NW.bt2(~F, b), hm0, NW.bt2_nn(~F, b, hb0), n)
  (fx(~F, O.one(F), s, FO.one_nn(~F)), (fx(~F, FR.ofn(~F, n), s, DG.ofn_nn(~F, n)), (fx(~F, FR.ofn(~F, m), s, DG.ofn_nn(~F, m)), (fx(~F, ms, s, hm0), (fx(~F, lam, s, hl0), (fx(~F, b, s, hb0), (fx(~F, DG.kd(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), s, DG.knn_d(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n), hk)), (fx(~F, DG.kp(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n)), s, DG.knn_p(~F, DG.kst(~F, n, ms, NW.bt2(~F, b), n), hk)), (fx(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), s, RD.dnn(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, {==})), (fx(~F, M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), s, RD.dnn(~F, ~H, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}, {==})), (fx(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), s, RD.c65_nn(~F, ~H)), Unit{})))))))))))

# x <= s gives x <= s 1
def le_s1(~F: O.OField, +x: O.C(F), +s: O.C(F), h: O.le(~F, x, s)) -> O.le(~F, x, O.mul(F, s, O.one(F))):
  PM.le_r(~F, x, s, O.mul(F, s, O.one(F)), O.mul_one(F)(s), h)

def envt_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt))) -> PM.Bnd(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt), AP.vbit(~F, Nat.div(p, 2n))):
  +ht = h_le_t(~F, p)
  ((hd0, (FO.one_nn(~F), le_s1(~F, d, AP.vbit(~F, Nat.div(p, 2n)), DM.le_trans(~F, d, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), hdh, ht)))),
  ((hr0, (htt, DM.le_trans(~F, rho, O.mul(F, NW.hnw(~F, p), tt), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), tt), hrh, FV.mul_le_r(~F, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), tt, htt, ht)))),
  ((NW.hnw_nn(~F, p), (FO.one_nn(~F), le_s1(~F, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), ht))),
  ((DG.u_nn(~F, NU.wbits(p)), (FO.one_nn(~F), le_s1(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), AP.vbit(~F, Nat.div(p, 2n)), DM.le_trans(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), u_le_h(~F, p), ht)))),
  ((BK.vb_nn(~F, p), (FO.one_nn(~F), le_s1(~F, AP.vbit(~F, Nat.div(p, 2n)), AP.vbit(~F, Nat.div(p, 2n)), FO.le_refl(~F, AP.vbit(~F, Nat.div(p, 2n)))))),
  fixd_bnd(~F, ~H, n, m, b, lam, ms, AP.vbit(~F, Nat.div(p, 2n)), hb0, hl0, hm0))))))

def envh_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt))) -> PM.Bnd(~F, envh(~F, n, m, b, lam, ms, d, rho, p, tt), NW.hnw(~F, p)):
  ((hd0, (FO.one_nn(~F), le_s1(~F, d, NW.hnw(~F, p), hdh))),
  ((hr0, (htt, hrh)),
  ((NW.hnw_nn(~F, p), (FO.one_nn(~F), le_s1(~F, NW.hnw(~F, p), NW.hnw(~F, p), FO.le_refl(~F, NW.hnw(~F, p))))),
  ((DG.u_nn(~F, NU.wbits(p)), (FO.one_nn(~F), le_s1(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), NW.hnw(~F, p), u_le_h(~F, p)))),
  ((BK.vb_nn(~F, p), (FO.one_nn(~F), t_le1(~F, p))),
  fixd_bnd(~F, ~H, n, m, b, lam, ms, NW.hnw(~F, p), hb0, hl0, hm0))))))

# Q and Phi
# ---------


# every atom at its bound, all fixed
def env0(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F)) -> List<&2, PM.Atm<O.C(F)>>:
  Con{PM.Atm{O.one(F), O.one(F), False{}}, Con{PM.Atm{tt, tt, False{}}, Con{PM.Atm{O.one(F), O.one(F), False{}}, Con{PM.Atm{O.one(F), O.one(F), False{}}, Con{PM.Atm{O.one(F), O.one(F), False{}}, fixd(~F, n, m, b, lam, ms)}}}}}

def env0_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> PM.Bnd(~F, env0(~F, n, m, b, lam, ms, tt), O.one(F)):
  (fx(~F, O.one(F), O.one(F), FO.one_nn(~F)), (fx(~F, tt, O.one(F), htt), (fx(~F, O.one(F), O.one(F), FO.one_nn(~F)), (fx(~F, O.one(F), O.one(F), FO.one_nn(~F)), (fx(~F, O.one(F), O.one(F), FO.one_nn(~F)), fixd_bnd(~F, ~H, n, m, b, lam, ms, O.one(F), hb0, hl0, hm0))))))

# a reflected constant at the bounds is not negative
def qnn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +e: PM.PE) -> O.le(~F, O.zero(F), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), e)):
  PM.pe_cnn(~F, env0(~F, n, m, b, lam, ms, tt), O.one(F), env0_bnd(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt), e)

def acoef_nn(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +c: Nat) -> O.le(~F, O.zero(F), DG.acoef(~F, n, bb, c, DG.kst(~F, n, g, bb, c))):
  +st = DG.kst(~F, n, g, bb, c)
  +hk = DG.kst_nn(~F, n, g, bb, hg, hb, c)
  FO.nonneg_add(~F, O.add(F, O.add(F, O.one(F), DG.ac1(~F, n, bb, c, st)), DG.ac2(~F, bb, st)), DG.ac3(~F, n, bb, st), FO.nonneg_add(~F, O.add(F, O.one(F), DG.ac1(~F, n, bb, c, st)), DG.ac2(~F, bb, st), FO.nonneg_add(~F, O.one(F), DG.ac1(~F, n, bb, c, st), FO.one_nn(~F), DG.ac1_nn(~F, n, bb, c, st, hb, hk)), DG.ac2_nn(~F, bb, st, hb, hk)), DG.ac3_nn(~F, n, bb, st, hb, hk))

# C4's column coefficients, summed over the first k columns
def asum(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), k: Nat) -> O.C(F):
  match k:
    case 0n:
      O.zero(F)
    case 1n++j:
      O.add(F, asum(~F, n, g, bb, j), DG.acoef(~F, n, bb, j, DG.kst(~F, n, g, bb, j)))

def asum_nn(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), k: Nat) -> O.le(~F, O.zero(F), asum(~F, n, g, bb, k)):
  match k:
    case 0n:
      FO.le_refl(~F, O.zero(F))
    case 1n++j:
      FO.nonneg_add(~F, asum(~F, n, g, bb, j), DG.acoef(~F, n, bb, j, DG.kst(~F, n, g, bb, j)), asum_nn(~F, n, g, bb, hg, hb, j), acoef_nn(~F, n, g, bb, hg, hb, j))

def ain.go(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +i: Nat, +j: Nat, b: Bool, e: {KA.nateq(i, j) == b : Bool}, hi: {KA.natle(1n+i, 1n+j) == True{} : Bool}, ih: {KA.natle(1n+i, j) == True{} : Bool} -> O.le(~F, DG.acoef(~F, n, bb, i, DG.kst(~F, n, g, bb, i)), asum(~F, n, g, bb, j))) -> O.le(~F, DG.acoef(~F, n, bb, i, DG.kst(~F, n, g, bb, i)), asum(~F, n, g, bb, 1n+j)):
  match b:
    case True{}:
      %Equal.sym(Nat, i, j, KA.nateq_ok(i, j, e)) : O.le(~F, DG.acoef(~F, n, bb, _, DG.kst(~F, n, g, bb, _)), asum(~F, n, g, bb, 1n+j))
      FV.le_addl(~F, asum(~F, n, g, bb, j), DG.acoef(~F, n, bb, j, DG.kst(~F, n, g, bb, j)), asum_nn(~F, n, g, bb, hg, hb, j))
    case False{}:
      DM.le_trans(~F, DG.acoef(~F, n, bb, i, DG.kst(~F, n, g, bb, i)), asum(~F, n, g, bb, j), asum(~F, n, g, bb, 1n+j), ih(GJ.le_ne(i, j, hi, e)), FV.le_addr(~F, asum(~F, n, g, bb, j), DG.acoef(~F, n, bb, j, DG.kst(~F, n, g, bb, j)), acoef_nn(~F, n, g, bb, hg, hb, j)))

# column i's coefficient is at most the sum, for i < k
def ain(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), k: Nat, +i: Nat, hi: {KA.natle(1n+i, k) == True{} : Bool}) -> O.le(~F, DG.acoef(~F, n, bb, i, DG.kst(~F, n, g, bb, i)), asum(~F, n, g, bb, k)):
  match k:
    case 0n:
      absurd(O.le(~F, DG.acoef(~F, n, bb, i, DG.kst(~F, n, g, bb, i)), O.zero(F)), KA.ft(hi))
    case 1n++j:
      ain.go(~F, n, g, bb, hg, hb, i, j, KA.nateq(i, j), {==}, hi, hj => ain(~F, n, g, bb, hg, hb, j, i, hj))


# the block's smallness budget: t qblk < 1 gives every smallness
# hypothesis of block_ok
def qblk(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F)) -> O.C(F):
  O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))

# the block's radius is at most h phib
def phib(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F)) -> O.C(F):
  PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_rbc())

def phib_ge(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, tt, phib(~F, n, m, b, lam, ms, tt)):
  FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_ubc()), tt, qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_ubc()))

def nn7(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))):
  FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_settle()), asum_nn(~F, n, ms, NW.bt2(~F, b), hm0, NW.bt2_nn(~F, b, hb0), n))

def nn6(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))):
  FO.nonneg_add(~F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), FO.mul_nonneg(~F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4()), DG.ofn_nn(~F, 64n), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w4())), nn7(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def nn5(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))):
  FO.nonneg_add(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w3()), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w3())), nn6(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def nn4(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))):
  FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_thrc()), nn5(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def nn3(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))):
  FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w1()), nn4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def nn2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))):
  FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_s2()), nn3(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def in2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_s1()))

def in3(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  DM.le_trans(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_s2())), in2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def in4(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  DM.le_trans(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w1())), in3(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def in5(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  DM.le_trans(~F, O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_thrc())), in4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def in6(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  DM.le_trans(~F, O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w3()), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w3()))), in5(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def in7(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))))):
  DM.le_trans(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), FO.mul_nonneg(~F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4()), DG.ofn_nn(~F, 64n), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_w4()))), in6(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

# t a < 1 for a part a of q, from t q < 1
def part(~F: O.OField, +t: O.C(F), +a: O.C(F), +q: O.C(F), +ht0: O.le(~F, O.zero(F), t), +ha: O.le(~F, a, q), +hq: O.lt(F, O.mul(F, t, q), O.one(F))) -> O.lt(F, O.mul(F, t, a), O.one(F)):
  FO.le_lt_trans(~F, O.mul(F, t, a), O.mul(F, t, q), O.one(F), FV.mul_le(~F, t, a, q, ht0, ha), hq)


def tq_s1(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1())), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), FV.le_addr(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), nn2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_s2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2())), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), nn3(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), in2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_w1(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1())), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), nn4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), in3(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_w2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc())), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), nn5(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), in4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_w3(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()))), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), nn6(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), in5(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_w4(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4()))), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), nn7(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), in6(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_s4(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle())), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addr(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n), asum_nn(~F, n, ms, NW.bt2(~F, b), hm0, NW.bt2_nn(~F, b, hb0), n)), in7(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

def tq_as(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt), +p: Nat, +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), asum(~F, n, ms, NW.bt2(~F, b), n)), O.one(F)):
  part(~F, AP.vbit(~F, Nat.div(p, 2n)), asum(~F, n, ms, NW.bt2(~F, b), n), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), BK.vb_nn(~F, p), DM.le_trans(~F, asum(~F, n, ms, NW.bt2(~F, b), n), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n)))))))), FV.le_addl(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_settle())), in7(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)), hsq)

# Dyadic constants
# ----------------


def n64_eq(~F: O.OField) -> {O.mul(F, FR.ofn(~F, 64n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})) == O.one(F) : O.C(F)}:
  FO.eq_of_sub(~F, O.mul(F, O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.zero(F))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(6n))))), O.one(F), FO.cert1(~F, O.sub(~F, O.mul(F, O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.zero(F))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(6n))))), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(6n)))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(6n)))], E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Z0{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(6n))))

def c65_eq(~F: O.OField) -> {O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})) == M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}) : O.C(F)}:
  FO.eq_of_sub(~F, O.add(F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(6n))))), O.mul(F, O.ofz(~F, S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(6n)))), FO.cert1(~F, O.sub(~F, O.add(F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(6n))))), O.mul(F, O.ofz(~F, S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(6n))))), O.neg(F, O.one(F)), O.sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(6n)))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(6n)))], E.ZSub{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}, E.ZMul{E.ZCst{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}}, E.ZVar{0n}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(6n))))

def c65m1(~F: O.OField) -> {O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F)) == M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}) : O.C(F)}:
  %c65_eq(~F) : {O.sub(~F, _, O.one(F)) == M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}) : O.C(F)}
  FR.fring_eq(~F, [M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})], E.ZSub{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

# t (64 q) < 1 gives t q <= 1/64
def tq64(~F: O.OField, +t: O.C(F), +q: O.C(F), h: O.lt(F, O.mul(F, t, O.mul(F, FR.ofn(~F, 64n), q)), O.one(F))) -> O.le(~F, O.mul(F, t, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})):
  +a = O.mul(F, t, O.mul(F, FR.ofn(~F, 64n), q))
  +h1 = PM.le_r(~F, O.mul(F, a, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})), O.mul(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}), FR.fring_eq(~F, [M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})], E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, {==}), FV.mul_le_r(~F, a, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}), DG.u_nn(~F, 6n), FO.lt_le(~F, a, O.one(F), h)))
  RL.le_rw_l(~F, O.mul(F, O.mul(F, t, q), O.one(F)), O.mul(F, t, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}), O.mul_one(F)(O.mul(F, t, q)),
    (%n64_eq(~F) : O.le(~F, O.mul(F, O.mul(F, t, q), _), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}))
    RL.le_rw_l(~F, O.mul(F, a, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})), O.mul(F, O.mul(F, t, q), O.mul(F, FR.ofn(~F, 64n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}), FR.fring_eq(~F, [t, q, FR.ofn(~F, 64n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n})], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, {==}), h1)))

def hh_le1(~F: O.OField, +p: Nat) -> O.le(~F, NW.hnw(~F, p), O.one(F)):
  DM.le_trans(~F, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), O.one(F), h_le_t(~F, p), t_le1(~F, p))

# h <= 6h
def h6_ge(~F: O.OField, +p: Nat) -> O.le(~F, NW.hnw(~F, p), NW.h6(~F, p)):
  +hn = NW.hnw_nn(~F, p)
  +h2 = FO.nonneg_add(~F, NW.hnw(~F, p), NW.hnw(~F, p), hn, hn)
  DM.le_trans(~F, NW.hnw(~F, p), O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), NW.h6(~F, p), FV.le_addr(~F, NW.hnw(~F, p), NW.hnw(~F, p), hn), DM.le_trans(~F, O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), O.add(F, O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), O.add(F, NW.hnw(~F, p), NW.hnw(~F, p))), NW.h6(~F, p), FV.le_addr(~F, O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), h2), FV.le_addr(~F, O.add(F, O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), O.add(F, NW.hnw(~F, p), NW.hnw(~F, p))), O.add(F, NW.hnw(~F, p), NW.hnw(~F, p)), h2)))

# The hypotheses
# --------------


def cond_t(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +e: PM.PE, +hd: {PM.d1(PM.svs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), e) == True{} : Bool}, +q: O.C(F), +hb: O.le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), e)), q)) -> O.le(~F, PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), e), q):
  DM.le_trans(~F, PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), e), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), e)), q, PM.pe_lin(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt), AP.vbit(~F, Nat.div(p, 2n)), envt_bnd(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh), BK.vb_nn(~F, p), t_le1(~F, p), e, hd), hb)

def cond_h(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +e: PM.PE, +hd: {PM.d1(PM.svs(~F, envh(~F, n, m, b, lam, ms, d, rho, p, tt)), e) == True{} : Bool}) -> O.le(~F, PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), e), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), e))):
  PM.pe_lin(~F, envh(~F, n, m, b, lam, ms, d, rho, p, tt), NW.hnw(~F, p), envh_bnd(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh), NW.hnw_nn(~F, p), hh_le1(~F, p), e, hd)

def cond_hq(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +e: PM.PE, +hd: {PM.d2(PM.svs(~F, envh(~F, n, m, b, lam, ms, d, rho, p, tt)), e) == True{} : Bool}) -> O.le(~F, PM.peval(~F, PM.avs(~F, envt(~F, n, m, b, lam, ms, d, rho, p, tt)), e), O.mul(F, NW.hnw(~F, p), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), e)))):
  PM.pe_quad(~F, envh(~F, n, m, b, lam, ms, d, rho, p, tt), NW.hnw(~F, p), envh_bnd(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh), NW.hnw_nn(~F, p), hh_le1(~F, p), e, hd)


def s1_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), NW.dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)):
  cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_s1(), {==}, O.one(F), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1())), O.one(F), tq_s1(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))

def s2_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)):
  cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_s2(), {==}, O.one(F), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2())), O.one(F), tq_s2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))

def w1_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, O.add(F, NW.dx(~F, n, m, b, lam, ms, d, rho, p), BK.rbc(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)):
  cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_w1(), {==}, O.one(F), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1())), O.one(F), tq_w1(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))

def w2_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.lt(F, BK.thrc(~F, n, m, b, lam, ms, d, rho, p), O.one(F)):
  FO.le_lt_trans(~F, BK.thrc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc())), O.one(F), cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_thrc(), {==}, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc())), FO.le_refl(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc())))), tq_w2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq))

def w3_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, O.add(F, O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, m), O.mul(F, lam, BK.rbc(~F, n, m, b, lam, ms, d, rho, p))))), M.ofd(~F, NU.half())):
  +s = O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()))
  +hh = RL.le_rw_l(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()))), O.add(F, s, s), O.one(F), O.mul_add(F)(AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()))), O.one(F), tq_w3(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))
  cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_w3(), {==}, M.ofd(~F, NU.half()), PM.le_r(~F, s, O.mul(F, M.ofd(~F, NU.half()), O.one(F)), M.ofd(~F, NU.half()), Equal.sym(O.C(F), O.mul(F, M.ofd(~F, NU.half()), O.one(F)), M.ofd(~F, NU.half()), O.mul_one(F)(M.ofd(~F, NU.half()))), RD.half_le(~F, ~H, s, O.one(F), hh)))

def w4_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, BK.thlc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, BK.ync(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, NW.dx(~F, n, m, b, lam, ms, d, rho, p)))))), O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F))):
  cond_t(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_w4(), {==}, O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F)), PM.le_r(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 6n}), O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F)), c65m1(~F), tq64(~F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4()), tq_w4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq))))

def s4_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> O.le(~F, NW.settle(~F, n, m, b, lam, ms, d, rho, p), NW.h6(~F, p)):
  +hn = NW.hnw_nn(~F, p)
  +hq1 = DM.le_trans(~F, O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle())), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle())), O.one(F), FV.mul_le_r(~F, NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_settle()), h_le_t(~F, p)), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle())), O.one(F), tq_s4(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))
  DM.le_trans(~F, NW.settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, NW.hnw(~F, p), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()))), NW.h6(~F, p), cond_hq(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_settle(), {==}), DM.le_trans(~F, O.mul(F, NW.hnw(~F, p), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()))), NW.hnw(~F, p), NW.h6(~F, p), PM.le_r(~F, O.mul(F, NW.hnw(~F, p), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()))), O.mul(F, NW.hnw(~F, p), O.one(F)), NW.hnw(~F, p), Equal.sym(O.C(F), O.mul(F, NW.hnw(~F, p), O.one(F)), NW.hnw(~F, p), O.mul_one(F)(NW.hnw(~F, p))), FV.mul_le(~F, NW.hnw(~F, p), O.mul(F, NW.hnw(~F, p), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle())), O.one(F), hn, hq1)), h6_ge(~F, p)))

# C4's columns: u a_i <= t asum < 1
def col_sm(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F)), +i: Nat, hi: {KA.natle(1n+i, n) == True{} : Bool}) -> O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), DG.acoef(~F, n, NW.bt2(~F, b), i, DG.kst(~F, n, ms, NW.bt2(~F, b), i))), O.one(F)):
  +a = DG.acoef(~F, n, NW.bt2(~F, b), i, DG.kst(~F, n, ms, NW.bt2(~F, b), i))
  +hb2 = NW.bt2_nn(~F, b, hb0)
  DM.le_trans(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), a), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), asum(~F, n, ms, NW.bt2(~F, b), n)), O.one(F), DM.le_trans(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), a), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), a), O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), asum(~F, n, ms, NW.bt2(~F, b), n)), FV.mul_le_r(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), AP.vbit(~F, Nat.div(p, 2n)), a, acoef_nn(~F, n, ms, NW.bt2(~F, b), hm0, hb2, i), DM.le_trans(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), NW.hnw(~F, p), AP.vbit(~F, Nat.div(p, 2n)), u_le_h(~F, p), h_le_t(~F, p))), FV.mul_le(~F, AP.vbit(~F, Nat.div(p, 2n)), a, asum(~F, n, ms, NW.bt2(~F, b), n), BK.vb_nn(~F, p), ain(~F, n, ms, NW.bt2(~F, b), hm0, hb2, n, i, hi))), FO.lt_le(~F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), asum(~F, n, ms, NW.bt2(~F, b), n)), O.one(F), tq_as(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, p, hsq)))

def hsm_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> AP.small(~F, n, ms, NW.bt2(~F, b), NU.wbits(p)):
  GJ.all_mk(~n, ~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, NU.wbits(p)}), DG.acoef(~F, n, NW.bt2(~F, b), q, DG.kst(~F, n, ms, NW.bt2(~F, b), q))), O.one(F))), ~(i => hi => col_sm(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq, i, hi)), n, KA.natle_refl(n))

# Results
# -------

# the block's radius bound is at most h phib
def rb_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt))) -> O.le(~F, BK.rbc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, NW.hnw(~F, p), phib(~F, n, m, b, lam, ms, tt))):
  cond_h(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, r_rbc(), {==})


# block_ok with its smallness hypotheses in scale form: the drawing within
# d <= h, the parameters' radii rho <= h T, and t qblk < 1
def block_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, NW.jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +y0: List<&2, S.D>, +ly0: {M.len(~F, M.ofdv(~F, y0)) == n : Nat}, +hy0: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y0), xb), d), +q2: Nat, +hp2: {p == 1n+(1n+q2) : Nat}, +pr: List<&2, S.D>, +lpr: {M.len(~F, M.ofdv(~F, pr)) == m : Nat}, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> BK.bgood(~F, n, eqs, xb, BK.rbc(~F, n, m, b, lam, ms, d, rho, p), pc, pr, NU.block(eqs, n, pc, pr, y0, p)):
  BK.block_ok(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), s1_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), s2_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), s4_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), y0, ly0, hy0, q2, hp2, pr, lpr, hpn, hzr, hpr, w1_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), w2_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), w3_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq), w4_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh, hsq))

# qblk and phib are not negative
def qblk_nn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), qblk(~F, n, m, b, lam, ms, tt)):
  FO.nonneg_add(~F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_s2()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w1()), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_thrc()), O.add(F, O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3()), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w3())), O.add(F, O.mul(F, FR.ofn(~F, 64n), PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_w4())), O.add(F, PM.peval(~F, cts(~F, n, m, b, lam, ms, tt), r_settle()), asum(~F, n, ms, NW.bt2(~F, b), n))))))), qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_s1()), nn2(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt))

def phib_nn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, O.zero(F), phib(~F, n, m, b, lam, ms, tt)):
  qnn(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt, r_rbc())
