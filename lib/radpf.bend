# bend-cad: the block's radius and box, for solve_complete (DESIGN §10.4,
# C5c). Proofs only.
#
# After Newton (lib/nwtpf.bend) the solver inverts the Jacobian at the
# center once more, rounds the inverse to Y, and searches radii from
# r0, the self-map bound at radius 0 times 65/64. This file shows that
# every radius between 2S and U passes the block checker (S the largest
# entry of that self-map bound), that the search reaches one, and that
# x_b lies in the box: |yc - x_b| <= (65/64) S <= r0 <= r.
#
# The self-map at radius r is compared entry by entry with the one at
# radius 0: the parameters' slope balls widen by at most ls r when the
# unknowns' radius grows from 0 to r (pair grades, below), so the
# comparison costs only first-order terms in r.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certdef.bend as C
import ./certpf.bend as CP
import ./kinst.bend as KI
import ./numer.bend as NU
import ./struct.bend as ST
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./gjpf.bend as GJ
import ./normpf.bend as NP
import ./dgjpf.bend as DG
import ./bndpf.bend as BP
import ./roundpf.bend as RP
import ./real.bend as RL
import ./qemb.bend as QE
import ./apxpf.bend as AP
import ./nwtpf.bend as NW
import ./slope.bend as SL
import ./nat.bend as LN

# K's absolute value is F's
# -------------------------

def kabs_eq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K)) -> {N.emap(K, F, H, KA.kabs(~K, a)) == FV.fabs(~F, N.emap(K, F, H, a)) : O.C(F)}:
  RL.le_antisymm(~F, N.emap(K, F, H, KA.kabs(~K, a)), FV.fabs(~F, N.emap(K, F, H, a)), BP.kabs_le(~K, ~F, ~H, a, FV.fabs(~F, N.emap(K, F, H, a)), FV.fabs_bnd(~F, N.emap(K, F, H, a))), FV.fabs_le(~F, N.emap(K, F, H, a), N.emap(K, F, H, KA.kabs(~K, a)), KA.kabs_bnd(~K, ~F, ~H, a)))

# Pair grades
# -----------
# Two balls with the same center over two boxes with the same centers,
# the second box's radii at least the first's and at most dl more: the
# second ball's radius is at least the first's and at most l dl more.

def pd(~F: O.OField, +dl: O.C(F), +r0: O.C(F), +r1: O.C(F), +l: O.C(F)) -> Data:
  M.Both(O.le(~F, O.zero(F), r0), M.Both(O.le(~F, r0, r1), O.le(~F, O.sub(~F, r1, r0), O.mul(F, l, dl))))

def pd_0(~F: O.OField, +dl: O.C(F), +r0: O.C(F), +r1: O.C(F), +l: O.C(F), h: pd(~F, dl, r0, r1, l)) -> O.le(~F, O.zero(F), r0):
  (a, b) = h
  a

def pd_12(~F: O.OField, +dl: O.C(F), +r0: O.C(F), +r1: O.C(F), +l: O.C(F), h: pd(~F, dl, r0, r1, l)) -> M.Both(O.le(~F, r0, r1), O.le(~F, O.sub(~F, r1, r0), O.mul(F, l, dl))):
  (a, b) = h
  b

def pd_1(~F: O.OField, +dl: O.C(F), +r0: O.C(F), +r1: O.C(F), +l: O.C(F), +h: pd(~F, dl, r0, r1, l)) -> O.le(~F, r0, r1):
  AP.both_l(O.le(~F, r0, r1), O.le(~F, O.sub(~F, r1, r0), O.mul(F, l, dl)), pd_12(~F, dl, r0, r1, l, h))

def pd_2(~F: O.OField, +dl: O.C(F), +r0: O.C(F), +r1: O.C(F), +l: O.C(F), +h: pd(~F, dl, r0, r1, l)) -> O.le(~F, O.sub(~F, r1, r0), O.mul(F, l, dl)):
  AP.both_r(O.le(~F, r0, r1), O.le(~F, O.sub(~F, r1, r0), O.mul(F, l, dl)), pd_12(~F, dl, r0, r1, l, h))

def pd_add(~F: O.OField, +dl: O.C(F), +a0: O.C(F), +a1: O.C(F), +l1: O.C(F), +b0: O.C(F), +b1: O.C(F), +l2: O.C(F), +ha: pd(~F, dl, a0, a1, l1), +hb: pd(~F, dl, b0, b1, l2)) -> pd(~F, dl, O.add(F, a0, b0), O.add(F, a1, b1), O.add(F, l1, l2)):
  (FO.nonneg_add(~F, a0, b0, pd_0(~F, dl, a0, a1, l1, ha), pd_0(~F, dl, b0, b1, l2, hb)),
   (FV.le_add2(~F, a0, a1, b0, b1, pd_1(~F, dl, a0, a1, l1, ha), pd_1(~F, dl, b0, b1, l2, hb)),
    FV.le_rw_r(~F, O.sub(~F, O.add(F, a1, b1), O.add(F, a0, b0)), O.add(F, O.mul(F, l1, dl), O.mul(F, l2, dl)), O.mul(F, O.add(F, l1, l2), dl), FR.fring_eq(~F, [l1, l2, dl], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}),
      RL.le_rw_l(~F, O.add(F, O.sub(~F, a1, a0), O.sub(~F, b1, b0)), O.sub(~F, O.add(F, a1, b1), O.add(F, a0, b0)), O.add(F, O.mul(F, l1, dl), O.mul(F, l2, dl)), FR.fring_eq(~F, [a0, a1, b0, b1], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}),
        FV.le_add2(~F, O.sub(~F, a1, a0), O.mul(F, l1, dl), O.sub(~F, b1, b0), O.mul(F, l2, dl), pd_2(~F, dl, a0, a1, l1, ha), pd_2(~F, dl, b0, b1, l2, hb))))))

# a product: |c1| = k1, |c2| = k2 (both boxes' centers agree), with
# k1 + a1 <= m1 and k2 + b1 <= m2 (the second box's grades)
def pd_mul(~F: O.OField, +dl: O.C(F), +k1: O.C(F), +k2: O.C(F), +a0: O.C(F), +a1: O.C(F), +l1: O.C(F), +m1: O.C(F), +b0: O.C(F), +b1: O.C(F), +l2: O.C(F), +m2: O.C(F), +hk1: O.le(~F, O.zero(F), k1), +hk2: O.le(~F, O.zero(F), k2), +ha: pd(~F, dl, a0, a1, l1), +hb: pd(~F, dl, b0, b1, l2), +hm1: O.le(~F, O.add(F, k1, a1), m1), +hm2: O.le(~F, O.add(F, k2, b1), m2)) -> pd(~F, dl, O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0)), O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1))):
  +ha0 = pd_0(~F, dl, a0, a1, l1, ha)
  +hb0 = pd_0(~F, dl, b0, b1, l2, hb)
  +da = FM.sub_nonneg(~F, a0, a1, pd_1(~F, dl, a0, a1, l1, ha))
  +db = FM.sub_nonneg(~F, b0, b1, pd_1(~F, dl, b0, b1, l2, hb))
  +ea_ = FM.sub_nonneg(~F, O.sub(~F, a1, a0), O.mul(F, l1, dl), pd_2(~F, dl, a0, a1, l1, ha))
  +eb_ = FM.sub_nonneg(~F, O.sub(~F, b1, b0), O.mul(F, l2, dl), pd_2(~F, dl, b0, b1, l2, hb))
  +ha1 = DM.le_trans(~F, O.zero(F), a0, a1, ha0, pd_1(~F, dl, a0, a1, l1, ha))
  +hb1 = DM.le_trans(~F, O.zero(F), b0, b1, hb0, pd_1(~F, dl, b0, b1, l2, hb))
  +fm1 = FM.sub_nonneg(~F, O.add(F, k1, a1), m1, hm1)
  +fm2 = DM.le_trans(~F, O.zero(F), O.sub(~F, m2, O.add(F, k2, b1)), O.sub(~F, m2, O.add(F, k2, b0)), FM.sub_nonneg(~F, O.add(F, k2, b1), m2, hm2), FV.le_of_sub(~F, O.sub(~F, m2, O.add(F, k2, b1)), O.sub(~F, m2, O.add(F, k2, b0)), FM.nn_eq(~F, O.sub(~F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, m2, O.add(F, k2, b1))), O.sub(~F, b1, b0), FR.fring_eq(~F, [m2, k2, b0, b1], E.ZSub{E.ZVar{3n}, E.ZVar{2n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}}, {==}), db)))
  +m1n = DM.le_trans(~F, O.zero(F), O.add(F, k1, a1), m1, FO.nonneg_add(~F, k1, a1, hk1, ha1), hm1)
  +m2n = DM.le_trans(~F, O.zero(F), O.add(F, k2, b1), m2, FO.nonneg_add(~F, k2, b1, hk2, hb1), hm2)
  (FO.nonneg_add(~F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0), FO.nonneg_add(~F, O.mul(F, k1, b0), O.mul(F, k2, a0), FO.mul_nonneg(~F, k1, b0, hk1, hb0), FO.mul_nonneg(~F, k2, a0, hk2, ha0)), FO.mul_nonneg(~F, a0, b0, ha0, hb0)),
   (FV.le_of_sub(~F, O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0)), O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)),
      FM.nn_eq(~F, O.sub(~F, O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)), O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0))), O.add(F, O.mul(F, O.add(F, k1, a1), O.sub(~F, b1, b0)), O.mul(F, O.add(F, k2, b0), O.sub(~F, a1, a0))),
        FR.fring_eq(~F, [k1, k2, a0, a1, b0, b1], E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{3n}}, E.ZSub{E.ZVar{5n}, E.ZVar{4n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{4n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{2n}, E.ZVar{4n}}}}, {==}),
        FO.nonneg_add(~F, O.mul(F, O.add(F, k1, a1), O.sub(~F, b1, b0)), O.mul(F, O.add(F, k2, b0), O.sub(~F, a1, a0)), FO.mul_nonneg(~F, O.add(F, k1, a1), O.sub(~F, b1, b0), FO.nonneg_add(~F, k1, a1, hk1, ha1), db), FO.mul_nonneg(~F, O.add(F, k2, b0), O.sub(~F, a1, a0), FO.nonneg_add(~F, k2, b0, hk2, hb0), da)))),
    FV.le_of_sub(~F, O.sub(~F, O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)), O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0))), O.mul(F, O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)), dl),
      FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)), dl), O.sub(~F, O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)), O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0)))), O.add(F, O.add(F, O.mul(F, O.sub(~F, m1, O.add(F, k1, a1)), O.sub(~F, b1, b0)), O.mul(F, m1, O.sub(~F, O.mul(F, l2, dl), O.sub(~F, b1, b0)))), O.add(F, O.mul(F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, a1, a0)), O.mul(F, m2, O.sub(~F, O.mul(F, l1, dl), O.sub(~F, a1, a0))))),
        FR.fring_eq(~F, [k1, k2, a0, a1, b0, b1, m1, m2, l1, l2, dl], E.ZAdd{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZAdd{E.ZVar{0n}, E.ZVar{3n}}}, E.ZSub{E.ZVar{5n}, E.ZVar{4n}}}, E.ZMul{E.ZVar{6n}, E.ZSub{E.ZMul{E.ZVar{9n}, E.ZVar{10n}}, E.ZSub{E.ZVar{5n}, E.ZVar{4n}}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZAdd{E.ZVar{1n}, E.ZVar{4n}}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{7n}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZVar{10n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{9n}}, E.ZMul{E.ZVar{7n}, E.ZVar{8n}}}, E.ZVar{10n}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{2n}, E.ZVar{4n}}}}}, {==}),
        FO.nonneg_add(~F, O.add(F, O.mul(F, O.sub(~F, m1, O.add(F, k1, a1)), O.sub(~F, b1, b0)), O.mul(F, m1, O.sub(~F, O.mul(F, l2, dl), O.sub(~F, b1, b0)))), O.add(F, O.mul(F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, a1, a0)), O.mul(F, m2, O.sub(~F, O.mul(F, l1, dl), O.sub(~F, a1, a0)))),
          FO.nonneg_add(~F, O.mul(F, O.sub(~F, m1, O.add(F, k1, a1)), O.sub(~F, b1, b0)), O.mul(F, m1, O.sub(~F, O.mul(F, l2, dl), O.sub(~F, b1, b0))), FO.mul_nonneg(~F, O.sub(~F, m1, O.add(F, k1, a1)), O.sub(~F, b1, b0), fm1, db), FO.mul_nonneg(~F, m1, O.sub(~F, O.mul(F, l2, dl), O.sub(~F, b1, b0)), m1n, eb_)),
          FO.nonneg_add(~F, O.mul(F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, a1, a0)), O.mul(F, m2, O.sub(~F, O.mul(F, l1, dl), O.sub(~F, a1, a0))), FO.mul_nonneg(~F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, a1, a0), fm2, da), FO.mul_nonneg(~F, m2, O.sub(~F, O.mul(F, l1, dl), O.sub(~F, a1, a0)), m2n, ea_)))))))

def pd_zero(~F: O.OField, +dl: O.C(F), +x: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> pd(~F, dl, x, x, O.zero(F)):
  (hx, (FO.le_refl(~F, x), FV.le_of_sub(~F, O.sub(~F, x, x), O.mul(F, O.zero(F), dl), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.zero(F), dl), O.sub(~F, x, x)), O.zero(F), FR.fring_eq(~F, [x, dl], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZVar{0n}}}, {==}), FO.le_refl(~F, O.zero(F))))))

def pd_one(~F: O.OField, +dl: O.C(F), +x: O.C(F), +hx: O.le(~F, O.zero(F), x), +hdl: O.le(~F, O.zero(F), dl)) -> pd(~F, dl, x, x, O.one(F)):
  (hx, (FO.le_refl(~F, x), FV.le_of_sub(~F, O.sub(~F, x, x), O.mul(F, O.one(F), dl), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.one(F), dl), O.sub(~F, x, x)), dl, FR.fring_eq(~F, [x, dl], E.ZVar{1n}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZVar{0n}}}, {==}), hdl))))


# Pairs of balls and of boxes
# ---------------------------

def bpd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), x0: KB.KB<K>, x1: KB.KB<K>, +l: O.C(F)) -> Data:
  pd(~F, dl, N.emap(K, F, H, KB.KB.r(K, x0)), N.emap(K, F, H, KB.KB.r(K, x1)), l)

# two boxes ball by ball: radii 0 <= r0 <= r1 <= r0 + dl
def bpair(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), b0: List<&2, KB.KB<K>>, b1: List<&2, KB.KB<K>>) -> Data:
  match b0 b1:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{x1, t1}:
      Empty
    case Con{x0, t0} Nil{}:
      Empty
    case Con{x0, t0} Con{x1, t1}:
      M.Both(bpd(~K, ~F, ~H, dl, x0, x1, O.one(F)), bpair(~K, ~F, ~H, dl, t0, t1))

def blook_pd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +hdl: O.le(~F, O.zero(F), dl), b0: List<&2, KB.KB<K>>, b1: List<&2, KB.KB<K>>, i: Nat, h: bpair(~K, ~F, ~H, dl, b0, b1)) -> bpd(~K, ~F, ~H, dl, KB.blook(~K, b0, i), KB.blook(~K, b1, i), O.one(F)):
  match b0 b1 i:
    case Nil{} Nil{} i:
      pd_one(~F, dl, N.emap(K, F, H, N.nzero(K)), KB.e0_nonneg(~K, ~F, ~H), hdl)
    case Nil{} Con{x1, t1} i:
      FO.absurd(bpd(~K, ~F, ~H, dl, KB.blook(~K, Nil{}, i), KB.blook(~K, Con{x1, t1}, i), O.one(F)), h)
    case Con{x0, t0} Nil{} i:
      FO.absurd(bpd(~K, ~F, ~H, dl, KB.blook(~K, Con{x0, t0}, i), KB.blook(~K, Nil{}, i), O.one(F)), h)
    case Con{+x0, +t0} Con{+x1, +t1} 0n:
      (h1, h2) = h
      h1
    case Con{+x0, +t0} Con{+x1, +t1} 1n+j:
      (h1, h2) = h
      blook_pd(~K, ~F, ~H, dl, hdl, t0, t1, j, h2)

# with the same centers, K's |center| agrees for kball and ksl
def kc_eq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> {N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.kball(~K, b0, e)))) == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.kball(~K, b1, e)))) : O.C(F)}:
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.kball(~K, b0, e)))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b0, e)))), kabs_eq(~K, ~F, ~H, KB.KB.c(K, KB.kball(~K, b0, e)))) : {_ == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.kball(~K, b1, e)))) : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.kball(~K, b1, e)))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b1, e)))), kabs_eq(~K, ~F, ~H, KB.KB.c(K, KB.kball(~K, b1, e)))) : {FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b0, e)))) == _ : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b0, e))), O.eval(~F, BP.cen(~K, ~F, ~H, b0), e), BP.kball_c(~K, ~F, ~H, b0, e, hh)) : {FV.fabs(~F, _) == FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b1, e)))) : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KB.KB.c(K, KB.kball(~K, b1, e))), O.eval(~F, BP.cen(~K, ~F, ~H, b1), e), BP.kball_c(~K, ~F, ~H, b1, e, hh)) : {FV.fabs(~F, O.eval(~F, BP.cen(~K, ~F, ~H, b0), e)) == FV.fabs(~F, _) : O.C(F)}
  %Equal.sym(M.Vec(~F), BP.cen(~K, ~F, ~H, b0), BP.cen(~K, ~F, ~H, b1), hcen) : {FV.fabs(~F, O.eval(~F, _, e)) == FV.fabs(~F, O.eval(~F, BP.cen(~K, ~F, ~H, b1), e)) : O.C(F)}
  {==}

def sc_eq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +i: Nat, +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> {N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.ksl(~K, i, b0, e)))) == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.ksl(~K, i, b1, e)))) : O.C(F)}:
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.ksl(~K, i, b0, e)))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b0, e)))), kabs_eq(~K, ~F, ~H, KB.KB.c(K, KB.ksl(~K, i, b0, e)))) : {_ == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.ksl(~K, i, b1, e)))) : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, KB.ksl(~K, i, b1, e)))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b1, e)))), kabs_eq(~K, ~F, ~H, KB.KB.c(K, KB.ksl(~K, i, b1, e)))) : {FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b0, e)))) == _ : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b0, e))), SL.sl(~F, i, BP.cen(~K, ~F, ~H, b0), BP.cen(~K, ~F, ~H, b0), e), BP.ksl_c(~K, ~F, ~H, i, b0, e, hh)) : {FV.fabs(~F, _) == FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b1, e)))) : O.C(F)}
  %Equal.sym(O.C(F), N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, i, b1, e))), SL.sl(~F, i, BP.cen(~K, ~F, ~H, b1), BP.cen(~K, ~F, ~H, b1), e), BP.ksl_c(~K, ~F, ~H, i, b1, e, hh)) : {FV.fabs(~F, SL.sl(~F, i, BP.cen(~K, ~F, ~H, b0), BP.cen(~K, ~F, ~H, b0), e)) == FV.fabs(~F, _) : O.C(F)}
  %Equal.sym(M.Vec(~F), BP.cen(~K, ~F, ~H, b0), BP.cen(~K, ~F, ~H, b1), hcen) : {FV.fabs(~F, SL.sl(~F, i, _, _, e)) == FV.fabs(~F, SL.sl(~F, i, BP.cen(~K, ~F, ~H, b1), BP.cen(~K, ~F, ~H, b1), e)) : O.C(F)}
  {==}

def pd_badd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), x0: KB.KB<K>, y0: KB.KB<K>, x1: KB.KB<K>, y1: KB.KB<K>, +l1: O.C(F), +l2: O.C(F), +hx: bpd(~K, ~F, ~H, dl, x0, x1, l1), +hy: bpd(~K, ~F, ~H, dl, y0, y1, l2)) -> bpd(~K, ~F, ~H, dl, KB.badd(~K, x0, y0), KB.badd(~K, x1, y1), O.add(F, l1, l2)):
  match x0 y0 x1 y1:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2} KB.KB{+d1, +s1} KB.KB{+d2, +s2}:
      %KA.ea(~K, ~F, ~H, r1, r2) : pd(~F, dl, _, N.emap(K, F, H, N.nadd(K, s1, s2)), O.add(F, l1, l2))
      %KA.ea(~K, ~F, ~H, s1, s2) : pd(~F, dl, O.add(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2)), _, O.add(F, l1, l2))
      pd_add(~F, dl, N.emap(K, F, H, r1), N.emap(K, F, H, s1), l1, N.emap(K, F, H, r2), N.emap(K, F, H, s2), l2, hx, hy)

def pd_bneg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), x0: KB.KB<K>, x1: KB.KB<K>, +l: O.C(F), +hx: bpd(~K, ~F, ~H, dl, x0, x1, l)) -> bpd(~K, ~F, ~H, dl, KB.bneg(~K, x0), KB.bneg(~K, x1), l):
  match x0 x1:
    case KB.KB{+c1, +r1} KB.KB{+d1, +s1}:
      hx

# |c| + r <= m from a grade
def gr_m(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +x: KB.KB<K>, +m: O.C(F), +l: O.C(F), +g: BP.grade(~K, ~F, ~H, rho, x, m, l)) -> O.le(~F, O.add(F, N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, x))), N.emap(K, F, H, KB.KB.r(K, x))), m):
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, x))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x))), kabs_eq(~K, ~F, ~H, KB.KB.c(K, x))) : O.le(~F, O.add(F, _, N.emap(K, F, H, KB.KB.r(K, x))), m)
  FV.le_of_sub(~F, O.add(F, FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x))), N.emap(K, F, H, KB.KB.r(K, x))), m, FM.nn_eq(~F, O.sub(~F, m, O.add(F, FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x))), N.emap(K, F, H, KB.KB.r(K, x)))), O.sub(~F, O.sub(~F, m, N.emap(K, F, H, KB.KB.r(K, x))), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x)))), FR.fring_eq(~F, [m, N.emap(K, F, H, KB.KB.r(K, x)), FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x)))], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{2n}, E.ZVar{1n}}}, {==}),
    FM.sub_nonneg(~F, FV.fabs(~F, N.emap(K, F, H, KB.KB.c(K, x))), O.sub(~F, m, N.emap(K, F, H, KB.KB.r(K, x))), FV.fabs_le(~F, N.emap(K, F, H, KB.KB.c(K, x)), O.sub(~F, m, N.emap(K, F, H, KB.KB.r(K, x))), BP.gf_c(~F, rho, N.emap(K, F, H, KB.KB.c(K, x)), N.emap(K, F, H, KB.KB.r(K, x)), m, l, g)))))

def pd_bmul(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), x0: KB.KB<K>, y0: KB.KB<K>, x1: KB.KB<K>, y1: KB.KB<K>, +l1: O.C(F), +m1: O.C(F), +l2: O.C(F), +m2: O.C(F), +lx: O.C(F), +ly: O.C(F), +ek1: {N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, x0))) == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, x1))) : O.C(F)}, +ek2: {N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, y0))) == N.emap(K, F, H, KA.kabs(~K, KB.KB.c(K, y1))) : O.C(F)}, +hx: bpd(~K, ~F, ~H, dl, x0, x1, l1), +hy: bpd(~K, ~F, ~H, dl, y0, y1, l2), +gx: BP.grade(~K, ~F, ~H, rho, x1, m1, lx), +gy: BP.grade(~K, ~F, ~H, rho, y1, m2, ly)) -> bpd(~K, ~F, ~H, dl, KB.bmul(~K, x0, y0), KB.bmul(~K, x1, y1), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1))):
  match x0 y0 x1 y1:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2} KB.KB{+d1, +s1} KB.KB{+d2, +s2}:
      %Equal.sym(O.C(F), N.emap(K, F, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2))), O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))), BP.bmul_r(~K, ~F, ~H, c1, r1, c2, r2)) : pd(~F, dl, _, N.emap(K, F, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, d1), s2), N.nmul(K, KA.kabs(~K, d2), s1)), N.nmul(K, s1, s2))), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)))
      %Equal.sym(O.C(F), N.emap(K, F, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, d1), s2), N.nmul(K, KA.kabs(~K, d2), s1)), N.nmul(K, s1, s2))), O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, d1)), N.emap(K, F, H, s2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, d2)), N.emap(K, F, H, s1))), O.mul(F, N.emap(K, F, H, s1), N.emap(K, F, H, s2))), BP.bmul_r(~K, ~F, ~H, d1, s1, d2, s2)) : pd(~F, dl, O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))), _, O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)))
      %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, KA.kabs(~K, d1)), ek1) : pd(~F, dl, O.add(F, O.add(F, O.mul(F, _, N.emap(K, F, H, r2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))), O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, d1)), N.emap(K, F, H, s2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, d2)), N.emap(K, F, H, s1))), O.mul(F, N.emap(K, F, H, s1), N.emap(K, F, H, s2))), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)))
      %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, c2)), N.emap(K, F, H, KA.kabs(~K, d2)), ek2) : pd(~F, dl, O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, d1)), N.emap(K, F, H, r2)), O.mul(F, _, N.emap(K, F, H, r1))), O.mul(F, N.emap(K, F, H, r1), N.emap(K, F, H, r2))), O.add(F, O.add(F, O.mul(F, N.emap(K, F, H, KA.kabs(~K, d1)), N.emap(K, F, H, s2)), O.mul(F, N.emap(K, F, H, KA.kabs(~K, d2)), N.emap(K, F, H, s1))), O.mul(F, N.emap(K, F, H, s1), N.emap(K, F, H, s2))), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1)))
      pd_mul(~F, dl, N.emap(K, F, H, KA.kabs(~K, d1)), N.emap(K, F, H, KA.kabs(~K, d2)), N.emap(K, F, H, r1), N.emap(K, F, H, s1), l1, m1, N.emap(K, F, H, r2), N.emap(K, F, H, s2), l2, m2, KA.kabs_nonneg(~K, ~F, ~H, d1), KA.kabs_nonneg(~K, ~F, ~H, d2), hx, hy, gr_m(~K, ~F, ~H, rho, KB.KB{d1, s1}, m1, lx, gx), gr_m(~K, ~F, ~H, rho, KB.KB{d2, s2}, m2, ly, gy))


# e's ball over the wider box: radius at most lp dl more
def kb_pd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), +bb: O.C(F), +hdl: O.le(~F, O.zero(F), dl), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +hp: bpair(~K, ~F, ~H, dl, b0, b1), +hg: BP.gbox(~K, ~F, ~H, rho, bb, b1), e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> bpd(~K, ~F, ~H, dl, KB.kball(~K, b0, e), KB.kball(~K, b1, e), BP.lp(~F, bb, e)):
  match e:
    case E.QVar{i}:
      blook_pd(~K, ~F, ~H, dl, hdl, b0, b1, i, hp)
    case E.QCst{+q}:
      pd_zero(~F, dl, N.emap(K, F, H, N.nzero(K)), KB.e0_nonneg(~K, ~F, ~H))
    case E.QAdd{+a, +b}:
      pd_badd(~K, ~F, ~H, dl, KB.kball(~K, b0, a), KB.kball(~K, b0, b), KB.kball(~K, b1, a), KB.kball(~K, b1, b), BP.lp(~F, bb, a), BP.lp(~F, bb, b), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      pd_badd(~K, ~F, ~H, dl, KB.kball(~K, b0, a), KB.bneg(~K, KB.kball(~K, b0, b)), KB.kball(~K, b1, a), KB.bneg(~K, KB.kball(~K, b1, b)), BP.lp(~F, bb, a), BP.lp(~F, bb, b), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), pd_bneg(~K, ~F, ~H, dl, KB.kball(~K, b0, b), KB.kball(~K, b1, b), BP.lp(~F, bb, b), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      +ha = KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)
      +hb2 = KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)
      pd_bmul(~K, ~F, ~H, dl, rho, KB.kball(~K, b0, a), KB.kball(~K, b0, b), KB.kball(~K, b1, a), KB.kball(~K, b1, b), BP.lp(~F, bb, a), BP.mj(~F, bb, a), BP.lp(~F, bb, b), BP.mj(~F, bb, b), BP.lp(~F, bb, a), BP.lp(~F, bb, b), kc_eq(~K, ~F, ~H, b0, b1, hcen, a, ha), kc_eq(~K, ~F, ~H, b0, b1, hcen, b, hb2), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, a, ha), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, b, hb2), BP.kball_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, a, ha), BP.kball_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, b, hb2))
    case E.QNeg{+a}:
      pd_bneg(~K, ~F, ~H, dl, KB.kball(~K, b0, a), KB.kball(~K, b1, a), BP.lp(~F, bb, a), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, a, hh))

def kind_pd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), b: Bool) -> bpd(~K, ~F, ~H, dl, KB.kind(~K, b), KB.kind(~K, b), O.zero(F)):
  match b:
    case True{}:
      pd_zero(~F, dl, N.emap(K, F, H, N.nzero(K)), KB.e0_nonneg(~K, ~F, ~H))
    case False{}:
      pd_zero(~F, dl, N.emap(K, F, H, N.nzero(K)), KB.e0_nonneg(~K, ~F, ~H))

# e's slope ball in variable i over the wider box: radius at most ls dl more
def ks_pd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), +bb: O.C(F), +hdl: O.le(~F, O.zero(F), dl), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +hp: bpair(~K, ~F, ~H, dl, b0, b1), +hg: BP.gbox(~K, ~F, ~H, rho, bb, b1), +i: Nat, e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}) -> bpd(~K, ~F, ~H, dl, KB.ksl(~K, i, b0, e), KB.ksl(~K, i, b1, e), BP.ls(~F, bb, e)):
  match e:
    case E.QVar{j}:
      kind_pd(~K, ~F, ~H, dl, KA.nateq(i, j))
    case E.QCst{q}:
      pd_zero(~F, dl, N.emap(K, F, H, N.nzero(K)), KB.e0_nonneg(~K, ~F, ~H))
    case E.QAdd{+a, +b}:
      pd_badd(~K, ~F, ~H, dl, KB.ksl(~K, i, b0, a), KB.ksl(~K, i, b0, b), KB.ksl(~K, i, b1, a), KB.ksl(~K, i, b1, b), BP.ls(~F, bb, a), BP.ls(~F, bb, b), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)))
    case E.QSub{+a, +b}:
      pd_badd(~K, ~F, ~H, dl, KB.ksl(~K, i, b0, a), KB.bneg(~K, KB.ksl(~K, i, b0, b)), KB.ksl(~K, i, b1, a), KB.bneg(~K, KB.ksl(~K, i, b1, b)), BP.ls(~F, bb, a), BP.ls(~F, bb, b), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, a, KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)), pd_bneg(~K, ~F, ~H, dl, KB.ksl(~K, i, b0, b), KB.ksl(~K, i, b1, b), BP.ls(~F, bb, b), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, b, KA.band_r(KB.held(~K, a), KB.held(~K, b), hh))))
    case E.QMul{+a, +b}:
      +ha = KA.band_l(KB.held(~K, a), KB.held(~K, b), hh)
      +hb2 = KA.band_r(KB.held(~K, a), KB.held(~K, b), hh)
      pd_badd(~K, ~F, ~H, dl, KB.bmul(~K, KB.kball(~K, b0, a), KB.ksl(~K, i, b0, b)), KB.bmul(~K, KB.kball(~K, b0, b), KB.ksl(~K, i, b0, a)), KB.bmul(~K, KB.kball(~K, b1, a), KB.ksl(~K, i, b1, b)), KB.bmul(~K, KB.kball(~K, b1, b), KB.ksl(~K, i, b1, a)), O.add(F, O.mul(F, BP.mj(~F, bb, a), BP.ls(~F, bb, b)), O.mul(F, BP.ms(~F, bb, b), BP.lp(~F, bb, a))), O.add(F, O.mul(F, BP.mj(~F, bb, b), BP.ls(~F, bb, a)), O.mul(F, BP.ms(~F, bb, a), BP.lp(~F, bb, b))),
        pd_bmul(~K, ~F, ~H, dl, rho, KB.kball(~K, b0, a), KB.ksl(~K, i, b0, b), KB.kball(~K, b1, a), KB.ksl(~K, i, b1, b), BP.lp(~F, bb, a), BP.mj(~F, bb, a), BP.ls(~F, bb, b), BP.ms(~F, bb, b), BP.lp(~F, bb, a), BP.ls(~F, bb, b), kc_eq(~K, ~F, ~H, b0, b1, hcen, a, ha), sc_eq(~K, ~F, ~H, b0, b1, hcen, i, b, hb2), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, a, ha), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, b, hb2), BP.kball_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, a, ha), BP.ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, i, b, hb2)),
        pd_bmul(~K, ~F, ~H, dl, rho, KB.kball(~K, b0, b), KB.ksl(~K, i, b0, a), KB.kball(~K, b1, b), KB.ksl(~K, i, b1, a), BP.lp(~F, bb, b), BP.mj(~F, bb, b), BP.ls(~F, bb, a), BP.ms(~F, bb, a), BP.lp(~F, bb, b), BP.ls(~F, bb, a), kc_eq(~K, ~F, ~H, b0, b1, hcen, b, hb2), sc_eq(~K, ~F, ~H, b0, b1, hcen, i, a, ha), kb_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, b, hb2), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, a, ha), BP.kball_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, b, hb2), BP.ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, b1, hg, i, a, ha)))
    case E.QNeg{+a}:
      pd_bneg(~K, ~F, ~H, dl, KB.ksl(~K, i, b0, a), KB.ksl(~K, i, b1, a), BP.ls(~F, bb, a), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, i, a, hh))

# Lists in K and F
# ----------------


def kfit_dreps(n: Nat, +r: S.D) -> {KA.kfit(~KI.dnum(), n, NU.dreps(n, r)) == NU.dreps(n, r) : List<&2, S.D>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(List<&2, S.D>, KA.kfit(~KI.dnum(), k, NU.dreps(k, r)), NU.dreps(k, r), kfit_dreps(k, r)) : {Con{r, _} == Con{r, NU.dreps(k, r)} : List<&2, S.D>}
      {==}

def kfit_nil(n: Nat) -> {KA.kfit(~KI.dnum(), n, Nil{}) == NU.dreps(n, M.d0()) : List<&2, S.D>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(List<&2, S.D>, KA.kfit(~KI.dnum(), k, Nil{}), NU.dreps(k, M.d0()), kfit_nil(k)) : {Con{M.d0(), _} == Con{M.d0(), NU.dreps(k, M.d0())} : List<&2, S.D>}
      {==}

def klen_dreps(n: Nat, +r: S.D) -> {KA.klen(~KI.dnum(), NU.dreps(n, r)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, KA.klen(~KI.dnum(), NU.dreps(k, r)), k, klen_dreps(k, r)) : {1n+_ == 1n+k : Nat}
      {==}

def klen_app(~K: N.Num, u: N.KVec(~K), +w: N.KVec(~K)) -> {KA.klen(~K, KA.kapp(~K, u, w)) == Nat.add(KA.klen(~K, u), KA.klen(~K, w)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{a, us}:
      %Equal.sym(Nat, KA.klen(~K, KA.kapp(~K, us, w)), Nat.add(KA.klen(~K, us), KA.klen(~K, w)), klen_app(~K, us, w)) : {1n+_ == 1n+Nat.add(KA.klen(~K, us), KA.klen(~K, w)) : Nat}
      {==}

# n copies of x in F
def frep(~F: O.OField, n: Nat, +x: O.C(F)) -> M.Vec(~F):
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{x, frep(~F, k, x)}

def ofdv_dreps(~F: O.OField, n: Nat, +r: S.D) -> {M.ofdv(~F, NU.dreps(n, r)) == frep(~F, n, M.ofd(~F, r)) : M.Vec(~F)}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dreps(k, r)), frep(~F, k, M.ofd(~F, r)), ofdv_dreps(~F, k, r)) : {Con{M.ofd(~F, r), _} == Con{M.ofd(~F, r), frep(~F, k, M.ofd(~F, r))} : M.Vec(~F)}
      {==}

def len_frep(~F: O.OField, n: Nat, +x: O.C(F)) -> {M.len(~F, frep(~F, n, x)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, M.len(~F, frep(~F, k, x)), k, len_frep(~F, k, x)) : {1n+_ == 1n+k : Nat}
      {==}

def frep_all(~F: O.OField, n: Nat, +x: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> M.vbnd.all(~F, frep(~F, n, x), x):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      (FV.bnd_self(~F, x, hx), frep_all(~F, k, x, hx))

def frep_nn(~F: O.OField, n: Nat, +x: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> FV.rnn(~F, frep(~F, n, x)):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      (hx, frep_nn(~F, k, x, hx))

def vn_frep(~F: O.OField, +n: Nat, +x: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> O.le(~F, NP.vn(~F, frep(~F, n, x)), x):
  FV.vmax_lub(~F, frep(~F, n, x), x, frep_all(~F, n, x, hx), hx)

def klen_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +v: List<&2, S.D>) -> {KA.klen(~KI.dnum(), v) == M.len(~F, M.ofdv(~F, v)) : Nat}:
  %AP.ofkv_d(~F, ~H, v) : {KA.klen(~KI.dnum(), v) == M.len(~F, _) : Nat}
  Equal.sym(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, v)), KA.klen(~KI.dnum(), v), CP.len_ofkv(~KI.dnum(), ~F, ~H, v))

# the centers of a zipped box are its center list
def bcen_zipb(~K: N.Num, cs: N.KVec(~K), rs: N.KVec(~K), hl: {KA.klen(~K, cs) == KA.klen(~K, rs) : Nat}) -> {KB.bcenters(~K, CK.zipb(~K, cs, rs)) == cs : N.KVec(~K)}:
  match cs rs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{r, rt}:
      FO.absurd({KB.bcenters(~K, CK.zipb(~K, Nil{}, Con{r, rt})) == Nil{} : N.KVec(~K)}, FV.zero_ne(KA.klen(~K, rt), hl))
    case Con{c, ct} Nil{}:
      FO.absurd({KB.bcenters(~K, CK.zipb(~K, Con{c, ct}, Nil{})) == Con{c, ct} : N.KVec(~K)}, FV.succ_ne(KA.klen(~K, ct), hl))
    case Con{+c, +ct} Con{+r, +rt}:
      %Equal.sym(N.KVec(~K), KB.bcenters(~K, CK.zipb(~K, ct, rt)), ct, bcen_zipb(~K, ct, rt, LN.succ_inj(KA.klen(~K, ct), KA.klen(~K, rt), hl))) : {Con{c, _} == Con{c, ct} : N.KVec(~K)}
      {==}

# a zipped box whose centers are within bb - rho and radii in [0, rho] has grade (bb, 1)
def gbox_zip(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, cs: N.KVec(~K), rs: N.KVec(~K), +rho: O.C(F), +bb: O.C(F), hc: M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, cs), O.sub(~F, bb, rho)), hn: FV.rnn(~F, N.ofkv(~K, ~F, ~H, rs)), hr: M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, rs), rho), hl: {KA.klen(~K, cs) == KA.klen(~K, rs) : Nat}) -> BP.gbox(~K, ~F, ~H, rho, bb, CK.zipb(~K, cs, rs)):
  match cs rs:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{r, rt}:
      FO.absurd(BP.gbox(~K, ~F, ~H, rho, bb, CK.zipb(~K, Nil{}, Con{r, rt})), FV.zero_ne(KA.klen(~K, rt), hl))
    case Con{c, ct} Nil{}:
      FO.absurd(BP.gbox(~K, ~F, ~H, rho, bb, CK.zipb(~K, Con{c, ct}, Nil{})), FV.succ_ne(KA.klen(~K, ct), hl))
    case Con{+c, +ct} Con{+r, +rt}:
      (hc1, hc2) = hc
      (hn1, hn2) = hn
      (hr1, hr2) = hr
      +hrl = FV.bnd_lo(~F, N.emap(K, F, H, r), rho, hr1)
      ((hn1, (FM.bnd_mono(~F, N.emap(K, F, H, c), O.sub(~F, bb, rho), O.sub(~F, bb, N.emap(K, F, H, r)), hc1, FM.nn_eq(~F, O.sub(~F, O.sub(~F, bb, N.emap(K, F, H, r)), O.sub(~F, bb, rho)), O.sub(~F, rho, N.emap(K, F, H, r)), FR.fring_eq(~F, [bb, rho, N.emap(K, F, H, r)], E.ZSub{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==}), FM.sub_nonneg(~F, N.emap(K, F, H, r), rho, hrl))), DM.le_trans(~F, N.emap(K, F, H, r), rho, O.mul(F, O.one(F), rho), hrl, AP.le_one_mul(~F, rho)))),
       gbox_zip(~K, ~F, ~H, ct, rt, rho, bb, hc2, hn2, hr2, LN.succ_inj(KA.klen(~K, ct), KA.klen(~K, rt), hl)))

# Slope radii over a graded box
# -----------------------------

def bnd_of01(~F: O.OField, +x: O.C(F), +t: O.C(F), +h0: O.le(~F, O.zero(F), x), +h1: O.le(~F, x, t)) -> M.bnd(~F, x, t):
  (FM.sub_nonneg(~F, x, t, h1), FO.nonneg_add(~F, t, x, DM.le_trans(~F, O.zero(F), x, t, h0, h1), h0))

def srad_cons(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), +t: M.Vec(~F), +s: O.C(F), +hb: M.bnd(~F, x, s), +h0: O.le(~F, O.zero(F), x), h: M.Both(M.vbnd.all(~F, t, s), FV.rnn(~F, t))) -> M.Both(M.vbnd.all(~F, Con{x, t}, s), FV.rnn(~F, Con{x, t})):
  (h1, h2) = h
  ((hb, h1), (h0, h2))

# one equation's slope radii: in [0, lam rho]
def srad_row(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}, +lam: O.C(F), +hl: O.le(~F, BP.ls(~F, bb, e), lam), +hl0: O.le(~F, O.zero(F), lam), cnt: Nat, +lo: Nat) -> M.Both(M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))), O.mul(F, lam, rho)), FV.rnn(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))))):
  match cnt:
    case 0n:
      (Unit{}, Unit{})
    case 1n++k:
      +g = BP.ksl_grade(~K, ~F, ~H, rho, bb, hr, hb, box, hg, lo, e, hh)
      +r0 = BP.gf_0(~F, rho, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, lo, box, e))), N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), BP.ms(~F, bb, e), BP.ls(~F, bb, e), g)
      +r1 = DM.le_trans(~F, N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), O.mul(F, BP.ls(~F, bb, e), rho), O.mul(F, lam, rho), BP.gf_l(~F, rho, N.emap(K, F, H, KB.KB.c(K, KB.ksl(~K, lo, box, e))), N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), BP.ms(~F, bb, e), BP.ls(~F, bb, e), g), FV.mul_le_r(~F, BP.ls(~F, bb, e), lam, rho, hr, hl))
      srad_cons(~K, ~F, ~H, N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, k, 1n+lo))), O.mul(F, lam, rho), bnd_of01(~F, N.emap(K, F, H, KB.KB.r(K, KB.ksl(~K, lo, box, e))), O.mul(F, lam, rho), r0, r1), r0, srad_row(~K, ~F, ~H, rho, bb, hr, hb, box, hg, e, hh, lam, hl, hl0, k, 1n+lo))

def srad_mcons(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +r: M.Vec(~F), +t: M.Mat(~F), +cnt: Nat, +c: O.C(F), +hr: O.le(~F, NP.rowabs(~F, r, cnt), c), +hn: FV.rnn(~F, r), h: M.Both(NP.rowsle(~F, t, cnt, c), FV.mnn(~F, t))) -> M.Both(NP.rowsle(~F, Con{r, t}, cnt, c), FV.mnn(~F, Con{r, t})):
  (h1, h2) = h
  ((hr, h1), (hn, h2))

# the slope radius matrix: rows sum to at most cnt lam rho, entries >= 0
def srad_mat(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), eqs: List<&2, E.QExpr>, +hq: AP.eqok(~F, bb, lam, ms, eqs), +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +cnt: Nat, +lo: Nat) -> M.Both(NP.rowsle(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rho))), FV.mnn(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))))):
  match eqs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+e, +es}:
      +he = KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh)
      +hes = KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh)
      +row = srad_row(~K, ~F, ~H, rho, bb, hr, hb, box, hg, e, he, lam, AP.eqok_ls(~F, bb, lam, ms, e, es, hq), hl0, cnt, lo)
      srad_mcons(~K, ~F, ~H, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))), N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, es))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rho)),
        DG.rowabs_le(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))), cnt, O.mul(F, lam, rho), AP.both_l(M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))), O.mul(F, lam, rho)), FV.rnn(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo)))), row), FO.mul_nonneg(~F, lam, rho, hl0, hr)),
        AP.both_r(M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo))), O.mul(F, lam, rho)), FV.rnn(~F, N.ofkv(~K, ~F, ~H, KB.bradii(~K, KB.krange(~K, box, e, cnt, lo)))), row),
        srad_mat(~K, ~F, ~H, rho, bb, hr, hb, box, hg, lam, ms, hl0, es, AP.eqok_tl(~F, bb, lam, ms, e, es, hq), hes, cnt, lo))

def srad_mn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +rho: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<K>>, +hg: BP.gbox(~K, ~F, ~H, rho, bb, box), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), +eqs: List<&2, E.QExpr>, +hq: AP.eqok(~F, bb, lam, ms, eqs), +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +cnt: Nat, +lo: Nat) -> O.le(~F, NP.mnorm(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rho))):
  NP.mnorm_lub(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rho)), AP.both_l(NP.rowsle(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rho))), FV.mnn(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs)))), srad_mat(~K, ~F, ~H, rho, bb, hr, hb, box, hg, lam, ms, hl0, eqs, hq, hh, cnt, lo)), AP.lr_nn(~F, cnt, lam, rho, hl0, hr))

# The checker's box
# -----------------
# CK.box(n, yc, yr, pc, pr): centers yc ++ pc, radii kfit(n, yr) ++ pr.


def klen_ckb(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +lyc: {KA.klen(~K, yc) == n : Nat}, +lpp: {KA.klen(~K, pc) == KA.klen(~K, pr) : Nat}) -> {KA.klen(~K, KA.kapp(~K, yc, pc)) == KA.klen(~K, KA.kapp(~K, KA.kfit(~K, n, yr), pr)) : Nat}:
  %Equal.sym(Nat, KA.klen(~K, KA.kapp(~K, yc, pc)), Nat.add(KA.klen(~K, yc), KA.klen(~K, pc)), klen_app(~K, yc, pc)) : {_ == KA.klen(~K, KA.kapp(~K, KA.kfit(~K, n, yr), pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~K, KA.kapp(~K, KA.kfit(~K, n, yr), pr)), Nat.add(KA.klen(~K, KA.kfit(~K, n, yr)), KA.klen(~K, pr)), klen_app(~K, KA.kfit(~K, n, yr), pr)) : {Nat.add(KA.klen(~K, yc), KA.klen(~K, pc)) == _ : Nat}
  %Equal.sym(Nat, KA.klen(~K, yc), n, lyc) : {Nat.add(_, KA.klen(~K, pc)) == Nat.add(KA.klen(~K, KA.kfit(~K, n, yr)), KA.klen(~K, pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~K, KA.kfit(~K, n, yr)), n, CP.klen_kfit(~K, n, yr)) : {Nat.add(n, KA.klen(~K, pc)) == Nat.add(_, KA.klen(~K, pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~K, pc), KA.klen(~K, pr), lpp) : {Nat.add(n, _) == Nat.add(n, KA.klen(~K, pr)) : Nat}
  {==}

# the box's centers are yc's point, whatever the radii
def cen_ckb(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +yr: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}) -> {BP.cen(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr)) == C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)) : M.Vec(~F)}:
  %Equal.sym(List<&2, S.D>, KB.bcenters(~KI.dnum(), CK.zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), KA.kfit(~KI.dnum(), n, yr), pr))), KA.kapp(~KI.dnum(), yc, pc), bcen_zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), KA.kfit(~KI.dnum(), n, yr), pr), klen_ckb(~KI.dnum(), ~F, ~H, n, yc, yr, pc, pr, lyc, lpp))) : {N.ofkv(~KI.dnum(), ~F, ~H, _) == C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), yc, pc)), C.app(~F, N.ofkv(~KI.dnum(), ~F, ~H, yc), N.ofkv(~KI.dnum(), ~F, ~H, pc)), CP.kapp_ofk(~KI.dnum(), ~F, ~H, yc, pc)) : {_ == C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, yc), M.ofdv(~F, yc), AP.ofkv_d(~F, ~H, yc)) : {C.app(~F, _, N.ofkv(~KI.dnum(), ~F, ~H, pc)) == C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, pc), M.ofdv(~F, pc), AP.ofkv_d(~F, ~H, pc)) : {C.app(~F, M.ofdv(~F, yc), _) == C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)) : M.Vec(~F)}
  {==}

def ofkv_kapp_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +u: List<&2, S.D>, +w: List<&2, S.D>) -> {N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), u, w)) == C.app(~F, M.ofdv(~F, u), M.ofdv(~F, w)) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), u, w)), C.app(~F, N.ofkv(~KI.dnum(), ~F, ~H, u), N.ofkv(~KI.dnum(), ~F, ~H, w)), CP.kapp_ofk(~KI.dnum(), ~F, ~H, u, w)) : {_ == C.app(~F, M.ofdv(~F, u), M.ofdv(~F, w)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, u), M.ofdv(~F, u), AP.ofkv_d(~F, ~H, u)) : {C.app(~F, _, N.ofkv(~KI.dnum(), ~F, ~H, w)) == C.app(~F, M.ofdv(~F, u), M.ofdv(~F, w)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, w), M.ofdv(~F, w), AP.ofkv_d(~F, ~H, w)) : {C.app(~F, M.ofdv(~F, u), _) == C.app(~F, M.ofdv(~F, u), M.ofdv(~F, w)) : M.Vec(~F)}
  {==}

def rnn_app(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F), hu: FV.rnn(~F, u), hw: FV.rnn(~F, w)) -> FV.rnn(~F, C.app(~F, u, w)):
  match u:
    case Nil{}:
      hw
    case Con{+a, +us}:
      (h1, h2) = hu
      (h1, rnn_app(~F, us, w, h2, hw))

def klen_ckw(+n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +w: S.D, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}) -> {KA.klen(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc)) == KA.klen(~KI.dnum(), KA.kapp(~KI.dnum(), NU.dreps(n, w), pr)) : Nat}:
  %Equal.sym(Nat, KA.klen(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc)), Nat.add(KA.klen(~KI.dnum(), yc), KA.klen(~KI.dnum(), pc)), klen_app(~KI.dnum(), yc, pc)) : {_ == KA.klen(~KI.dnum(), KA.kapp(~KI.dnum(), NU.dreps(n, w), pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~KI.dnum(), KA.kapp(~KI.dnum(), NU.dreps(n, w), pr)), Nat.add(KA.klen(~KI.dnum(), NU.dreps(n, w)), KA.klen(~KI.dnum(), pr)), klen_app(~KI.dnum(), NU.dreps(n, w), pr)) : {Nat.add(KA.klen(~KI.dnum(), yc), KA.klen(~KI.dnum(), pc)) == _ : Nat}
  %Equal.sym(Nat, KA.klen(~KI.dnum(), yc), n, lyc) : {Nat.add(_, KA.klen(~KI.dnum(), pc)) == Nat.add(KA.klen(~KI.dnum(), NU.dreps(n, w)), KA.klen(~KI.dnum(), pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~KI.dnum(), NU.dreps(n, w)), n, klen_dreps(n, w)) : {Nat.add(n, KA.klen(~KI.dnum(), pc)) == Nat.add(_, KA.klen(~KI.dnum(), pr)) : Nat}
  %Equal.sym(Nat, KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr), lpp) : {Nat.add(n, _) == Nat.add(n, KA.klen(~KI.dnum(), pr)) : Nat}
  {==}

# the checker's box with unknowns' radii w has grade (bb, 1) at rb
def gbox_ckb(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +yr: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +w: S.D, +hyr: {KA.kfit(~KI.dnum(), n, yr) == NU.dreps(n, w) : List<&2, S.D>}, +rb: O.C(F), +bb: O.C(F), hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hw0: O.le(~F, O.zero(F), M.ofd(~F, w)), +hw1: O.le(~F, M.ofd(~F, w), rb), hpn: FV.rnn(~F, M.ofdv(~F, pr)), hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb)) -> BP.gbox(~KI.dnum(), ~F, ~H, rb, bb, CK.box(~KI.dnum(), n, yc, yr, pc, pr)):
  %Equal.sym(List<&2, S.D>, KA.kfit(~KI.dnum(), n, yr), NU.dreps(n, w), hyr) : BP.gbox(~KI.dnum(), ~F, ~H, rb, bb, CK.zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), _, pr)))
  gbox_zip(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), NU.dreps(n, w), pr), rb, bb,
    (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), yc, pc)), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), ofkv_kapp_d(~F, ~H, yc, pc)) : M.vbnd.all(~F, _, O.sub(~F, bb, rb))
      hc),
    (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), NU.dreps(n, w), pr)), C.app(~F, M.ofdv(~F, NU.dreps(n, w)), M.ofdv(~F, pr)), ofkv_kapp_d(~F, ~H, NU.dreps(n, w), pr)) : FV.rnn(~F, _)
      (%Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dreps(n, w)), frep(~F, n, M.ofd(~F, w)), ofdv_dreps(~F, n, w)) : FV.rnn(~F, C.app(~F, _, M.ofdv(~F, pr)))
        rnn_app(~F, frep(~F, n, M.ofd(~F, w)), M.ofdv(~F, pr), frep_nn(~F, n, M.ofd(~F, w), hw0), hpn))),
    (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, KA.kapp(~KI.dnum(), NU.dreps(n, w), pr)), C.app(~F, M.ofdv(~F, NU.dreps(n, w)), M.ofdv(~F, pr)), ofkv_kapp_d(~F, ~H, NU.dreps(n, w), pr)) : M.vbnd.all(~F, _, rb)
      (%Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dreps(n, w)), frep(~F, n, M.ofd(~F, w)), ofdv_dreps(~F, n, w)) : M.vbnd.all(~F, C.app(~F, _, M.ofdv(~F, pr)), rb)
        NW.vall_app(~F, frep(~F, n, M.ofd(~F, w)), M.ofdv(~F, pr), rb, NW.vall_le(~F, frep(~F, n, M.ofd(~F, w)), M.ofd(~F, w), rb, frep_all(~F, n, M.ofd(~F, w), hw0), hw1), hpr))),
    klen_ckw(n, yc, pc, pr, w, lyc, lpp))

# radius lists pairwise: 0 <= a <= b <= a + dl
def rpair(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), rs0: N.KVec(~K), rs1: N.KVec(~K)) -> Data:
  match rs0 rs1:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{b, t1}:
      Empty
    case Con{a, t0} Nil{}:
      Empty
    case Con{a, t0} Con{b, t1}:
      M.Both(pd(~F, dl, N.emap(K, F, H, a), N.emap(K, F, H, b), O.one(F)), rpair(~K, ~F, ~H, dl, t0, t1))

def bpair_zip(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), cs: N.KVec(~K), rs0: N.KVec(~K), rs1: N.KVec(~K), hp: rpair(~K, ~F, ~H, dl, rs0, rs1), hl: {KA.klen(~K, cs) == KA.klen(~K, rs0) : Nat}) -> bpair(~K, ~F, ~H, dl, CK.zipb(~K, cs, rs0), CK.zipb(~K, cs, rs1)):
  match cs rs0 rs1:
    case Nil{} Nil{} Nil{}:
      Unit{}
    case Nil{} Nil{} Con{b, t1}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Nil{}, Nil{}), CK.zipb(~K, Nil{}, Con{b, t1})), hp)
    case Nil{} Con{a, t0} Nil{}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Nil{}, Con{a, t0}), CK.zipb(~K, Nil{}, Nil{})), hp)
    case Nil{} Con{a, t0} Con{b, t1}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Nil{}, Con{a, t0}), CK.zipb(~K, Nil{}, Con{b, t1})), FV.zero_ne(KA.klen(~K, t0), hl))
    case Con{c, ct} Nil{} Nil{}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Con{c, ct}, Nil{}), CK.zipb(~K, Con{c, ct}, Nil{})), FV.succ_ne(KA.klen(~K, ct), hl))
    case Con{c, ct} Nil{} Con{b, t1}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Con{c, ct}, Nil{}), CK.zipb(~K, Con{c, ct}, Con{b, t1})), FV.succ_ne(KA.klen(~K, ct), hl))
    case Con{c, ct} Con{a, t0} Nil{}:
      FO.absurd(bpair(~K, ~F, ~H, dl, CK.zipb(~K, Con{c, ct}, Con{a, t0}), CK.zipb(~K, Con{c, ct}, Nil{})), hp)
    case Con{+c, +ct} Con{+a, +t0} Con{+b, +t1}:
      (h1, h2) = hp
      (h1, bpair_zip(~K, ~F, ~H, dl, ct, t0, t1, h2, LN.succ_inj(KA.klen(~K, ct), KA.klen(~K, t0), hl)))

def rpair_app(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), u0: N.KVec(~K), u1: N.KVec(~K), +w: N.KVec(~K), hu: rpair(~K, ~F, ~H, dl, u0, u1), hw: rpair(~K, ~F, ~H, dl, w, w)) -> rpair(~K, ~F, ~H, dl, KA.kapp(~K, u0, w), KA.kapp(~K, u1, w)):
  match u0 u1:
    case Nil{} Nil{}:
      hw
    case Nil{} Con{b, t1}:
      FO.absurd(rpair(~K, ~F, ~H, dl, KA.kapp(~K, Nil{}, w), KA.kapp(~K, Con{b, t1}, w)), hu)
    case Con{a, t0} Nil{}:
      FO.absurd(rpair(~K, ~F, ~H, dl, KA.kapp(~K, Con{a, t0}, w), KA.kapp(~K, Nil{}, w)), hu)
    case Con{+a, +t0} Con{+b, +t1}:
      (h1, h2) = hu
      (h1, rpair_app(~K, ~F, ~H, dl, t0, t1, w, h2, hw))

def rpair_self(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +hdl: O.le(~F, O.zero(F), dl), w: N.KVec(~K), hn: FV.rnn(~F, N.ofkv(~K, ~F, ~H, w))) -> rpair(~K, ~F, ~H, dl, w, w):
  match w:
    case Nil{}:
      Unit{}
    case Con{+a, +t}:
      (h1, h2) = hn
      (pd_one(~F, dl, N.emap(K, F, H, a), h1, hdl), rpair_self(~K, ~F, ~H, dl, hdl, t, h2))

def pd_0r(~F: O.OField, +z: O.C(F), +x: O.C(F), ez: {z == O.zero(F) : O.C(F)}, +hx: O.le(~F, O.zero(F), x)) -> pd(~F, x, z, x, O.one(F)):
  %Equal.sym(O.C(F), z, O.zero(F), ez) : pd(~F, x, _, x, O.one(F))
  (FO.le_refl(~F, O.zero(F)), (hx, FV.le_of_sub(~F, O.sub(~F, x, O.zero(F)), O.mul(F, O.one(F), x), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.one(F), x), O.sub(~F, x, O.zero(F))), O.zero(F), FR.fring_eq(~F, [x], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}}, {==}), FO.le_refl(~F, O.zero(F))))))

# zeros against r's: each within H r
def rpair_dreps(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, n: Nat, +r: S.D, +hr: O.le(~F, O.zero(F), N.emap(KI.dnum(), F, H, r))) -> rpair(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), NU.dreps(n, M.d0()), NU.dreps(n, r)):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      (pd_0r(~F, N.emap(KI.dnum(), F, H, M.d0()), N.emap(KI.dnum(), F, H, r), N.e_zero(KI.dnum(), F, H), hr), rpair_dreps(~F, ~H, k, r, hr))

# the checker's boxes at radius 0 and r pair up, with dl = H r
def bpair_ckb(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +r: S.D, +hr: O.le(~F, O.zero(F), N.emap(KI.dnum(), F, H, r)), hpn: FV.rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, pr))) -> bpair(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), CK.box(~KI.dnum(), n, yc, NU.dreps(n, r), pc, pr)):
  %Equal.sym(List<&2, S.D>, KA.kfit(~KI.dnum(), n, Nil{}), NU.dreps(n, M.d0()), kfit_nil(n)) : bpair(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), CK.zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), _, pr)), CK.box(~KI.dnum(), n, yc, NU.dreps(n, r), pc, pr))
  %Equal.sym(List<&2, S.D>, KA.kfit(~KI.dnum(), n, NU.dreps(n, r)), NU.dreps(n, r), kfit_dreps(n, r)) : bpair(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), CK.zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), NU.dreps(n, M.d0()), pr)), CK.zipb(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), _, pr)))
  bpair_zip(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), KA.kapp(~KI.dnum(), yc, pc), KA.kapp(~KI.dnum(), NU.dreps(n, M.d0()), pr), KA.kapp(~KI.dnum(), NU.dreps(n, r), pr),
    rpair_app(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), NU.dreps(n, M.d0()), NU.dreps(n, r), pr, rpair_dreps(~F, ~H, n, r, hr), rpair_self(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), hr, pr, hpn)),
    klen_ckw(n, yc, pc, pr, M.d0(), lyc, lpp))

# The parameter slopes, |center| + radius, over the two boxes
# ------------------------------------------------------------
# Row k of the checker's |J0z| + Dz grows by at most ls dl, entry by entry.

def mzr(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +e: E.QExpr, +cnt: Nat, +lo: Nat) -> N.KVec(~K):
  KA.kvadd(~K, KA.kvabs(~K, KB.bcenters(~K, KB.krange(~K, box, e, cnt, lo))), KB.bradii(~K, KB.krange(~K, box, e, cnt, lo)))

def mz_ent(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +l: O.C(F), +c0: N.NC(K), +r0: N.NC(K), +c1: N.NC(K), +r1: N.NC(K), +ek: {N.emap(K, F, H, KA.kabs(~K, c0)) == N.emap(K, F, H, KA.kabs(~K, c1)) : O.C(F)}, +hp: pd(~F, dl, N.emap(K, F, H, r0), N.emap(K, F, H, r1), l)) -> M.bnd(~F, O.sub(~F, N.emap(K, F, H, N.nadd(K, KA.kabs(~K, c1), r1)), N.emap(K, F, H, N.nadd(K, KA.kabs(~K, c0), r0))), O.mul(F, l, dl)):
  %KA.ea(~K, ~F, ~H, KA.kabs(~K, c1), r1) : M.bnd(~F, O.sub(~F, _, N.emap(K, F, H, N.nadd(K, KA.kabs(~K, c0), r0))), O.mul(F, l, dl))
  %KA.ea(~K, ~F, ~H, KA.kabs(~K, c0), r0) : M.bnd(~F, O.sub(~F, O.add(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r1)), _), O.mul(F, l, dl))
  %Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, c0)), N.emap(K, F, H, KA.kabs(~K, c1)), ek) : M.bnd(~F, O.sub(~F, O.add(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r1)), O.add(F, _, N.emap(K, F, H, r0))), O.mul(F, l, dl))
  KB.bnd_val(~F, O.sub(~F, N.emap(K, F, H, r1), N.emap(K, F, H, r0)), O.sub(~F, O.add(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r1)), O.add(F, N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r0))), O.mul(F, l, dl), FR.fring_eq(~F, [N.emap(K, F, H, KA.kabs(~K, c1)), N.emap(K, F, H, r0), N.emap(K, F, H, r1)], E.ZSub{E.ZVar{2n}, E.ZVar{1n}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}}, {==}),
    bnd_of01(~F, O.sub(~F, N.emap(K, F, H, r1), N.emap(K, F, H, r0)), O.mul(F, l, dl), FM.sub_nonneg(~F, N.emap(K, F, H, r0), N.emap(K, F, H, r1), pd_1(~F, dl, N.emap(K, F, H, r0), N.emap(K, F, H, r1), l, hp)), pd_2(~F, dl, N.emap(K, F, H, r0), N.emap(K, F, H, r1), l, hp)))

def mz_row(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), +bb: O.C(F), +hdl: O.le(~F, O.zero(F), dl), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +hp: bpair(~K, ~F, ~H, dl, b0, b1), +hg: BP.gbox(~K, ~F, ~H, rho, bb, b1), +e: E.QExpr, +hh: {KB.held(~K, e) == True{} : Bool}, cnt: Nat, +lo: Nat) -> M.vbnd.all(~F, BX.vsub(~F, N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b1, e, cnt, lo)), N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b0, e, cnt, lo))), O.mul(F, BP.ls(~F, bb, e), dl)):
  match cnt:
    case 0n:
      Unit{}
    case 1n++k:
      (mz_ent(~K, ~F, ~H, dl, BP.ls(~F, bb, e), KB.KB.c(K, KB.ksl(~K, lo, b0, e)), KB.KB.r(K, KB.ksl(~K, lo, b0, e)), KB.KB.c(K, KB.ksl(~K, lo, b1, e)), KB.KB.r(K, KB.ksl(~K, lo, b1, e)), sc_eq(~K, ~F, ~H, b0, b1, hcen, lo, e, hh), ks_pd(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, lo, e, hh)),
       mz_row(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, e, hh, k, 1n+lo))

def mzm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, +eqs: List<&2, E.QExpr>) -> N.KMat(~K):
  KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))), CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs)))

def mz_rows(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), +bb: O.C(F), +hdl: O.le(~F, O.zero(F), dl), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +hp: bpair(~K, ~F, ~H, dl, b0, b1), +hg: BP.gbox(~K, ~F, ~H, rho, bb, b1), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), eqs: List<&2, E.QExpr>, +hq: AP.eqok(~F, bb, lam, ms, eqs), +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +cnt: Nat, +lo: Nat) -> NP.rowsle(~F, M.madd(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b1, cnt, lo, eqs)), M.mneg(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b0, cnt, lo, eqs)))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, dl))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      +he = KA.band_l(KB.held(~K, e), CK.allheld(~K, es), hh)
      +hes = KA.band_r(KB.held(~K, e), CK.allheld(~K, es), hh)
      (DG.rowabs_le(~F, BX.vsub(~F, N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b1, e, cnt, lo)), N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b0, e, cnt, lo))), cnt, O.mul(F, lam, dl),
         NW.vall_le(~F, BX.vsub(~F, N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b1, e, cnt, lo)), N.ofkv(~K, ~F, ~H, mzr(~K, ~F, ~H, b0, e, cnt, lo))), O.mul(F, BP.ls(~F, bb, e), dl), O.mul(F, lam, dl), mz_row(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, e, he, cnt, lo), FV.mul_le_r(~F, BP.ls(~F, bb, e), lam, dl, hdl, AP.eqok_ls(~F, bb, lam, ms, e, es, hq))),
         FO.mul_nonneg(~F, lam, dl, hl0, hdl)),
       mz_rows(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, lam, ms, hl0, es, AP.eqok_tl(~F, bb, lam, ms, e, es, hq), hes, cnt, lo))

# |(|J0z| + Dz)(box1) - (|J0z| + Dz)(box0)| <= cnt lam dl
def mz_mn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +dl: O.C(F), +rho: O.C(F), +bb: O.C(F), +hdl: O.le(~F, O.zero(F), dl), +hr: O.le(~F, O.zero(F), rho), +hb: O.le(~F, O.zero(F), bb), +b0: List<&2, KB.KB<K>>, +b1: List<&2, KB.KB<K>>, +hcen: {BP.cen(~K, ~F, ~H, b0) == BP.cen(~K, ~F, ~H, b1) : M.Vec(~F)}, +hp: bpair(~K, ~F, ~H, dl, b0, b1), +hg: BP.gbox(~K, ~F, ~H, rho, bb, b1), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), +eqs: List<&2, E.QExpr>, +hq: AP.eqok(~F, bb, lam, ms, eqs), +hh: {CK.allheld(~K, eqs) == True{} : Bool}, +cnt: Nat, +lo: Nat) -> O.le(~F, NP.mnorm(~F, M.madd(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b1, cnt, lo, eqs)), M.mneg(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b0, cnt, lo, eqs)))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, dl))):
  NP.mnorm_lub(~F, M.madd(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b1, cnt, lo, eqs)), M.mneg(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, b0, cnt, lo, eqs)))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, dl)), mz_rows(~K, ~F, ~H, dl, rho, bb, hdl, hr, hb, b0, b1, hcen, hp, hg, lam, ms, hl0, eqs, hq, hh, cnt, lo), AP.lr_nn(~F, cnt, lam, dl, hl0, hdl))

# K's |M| entrywise has F norm at most M's
# -----------------------------------------

def kabs_ent(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: N.NC(K)) -> O.le(~F, FV.fabs(~F, N.emap(K, F, H, KA.kabs(~K, x))), FV.fabs(~F, N.emap(K, F, H, x))):
  FV.fabs_le(~F, N.emap(K, F, H, KA.kabs(~K, x)), FV.fabs(~F, N.emap(K, F, H, x)),
    (%Equal.sym(O.C(F), N.emap(K, F, H, KA.kabs(~K, x)), FV.fabs(~F, N.emap(K, F, H, x)), kabs_eq(~K, ~F, ~H, x)) : M.bnd(~F, _, FV.fabs(~F, N.emap(K, F, H, x)))
      FV.bnd_self(~F, FV.fabs(~F, N.emap(K, F, H, x)), FV.fabs_nn(~F, N.emap(K, F, H, x)))))

def kabs_row(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, r: N.KVec(~K), n: Nat) -> O.le(~F, NP.rowabs(~F, N.ofkv(~K, ~F, ~H, KA.kvabs(~K, r)), n), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, r), n)):
  match r n:
    case Nil{} 0n:
      FO.le_refl(~F, O.zero(F))
    case Nil{} 1n++k:
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +t} 0n:
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +t} 1n++k:
      FV.le_add2(~F, FV.fabs(~F, N.emap(K, F, H, KA.kabs(~K, x))), FV.fabs(~F, N.emap(K, F, H, x)), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, KA.kvabs(~K, t)), k), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, t), k), kabs_ent(~K, ~F, ~H, x), kabs_row(~K, ~F, ~H, t, k))

def kabs_rows(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K), +n: Nat, +c: O.C(F), +hc: O.le(~F, NP.mnorm(~F, N.ofkm(~K, ~F, ~H, a), n), c)) -> NP.rowsle(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, a)), n, c):
  match a:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (DM.le_trans(~F, NP.rowabs(~F, N.ofkv(~K, ~F, ~H, KA.kvabs(~K, r)), n), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, r), n), c, kabs_row(~K, ~F, ~H, r, n), DM.le_trans(~F, NP.rowabs(~F, N.ofkv(~K, ~F, ~H, r), n), NP.mnorm(~F, N.ofkm(~K, ~F, ~H, Con{r, t}), n), c, AP.mnorm_ge_r(~F, N.ofkv(~K, ~F, ~H, r), N.ofkm(~K, ~F, ~H, t), n), hc)),
       kabs_rows(~K, ~F, ~H, t, n, c, DM.le_trans(~F, NP.mnorm(~F, N.ofkm(~K, ~F, ~H, t), n), NP.mnorm(~F, N.ofkm(~K, ~F, ~H, Con{r, t}), n), c, AP.mnorm_ge_t(~F, N.ofkv(~K, ~F, ~H, r), N.ofkm(~K, ~F, ~H, t), n), hc)))

def kabs_mn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.KMat(~K), +n: Nat, +c: O.C(F), +hc0: O.le(~F, O.zero(F), c), +hc: O.le(~F, NP.mnorm(~F, N.ofkm(~K, ~F, ~H, a), n), c)) -> O.le(~F, NP.mnorm(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, a)), n), c):
  NP.mnorm_lub(~F, N.ofkm(~K, ~F, ~H, KA.kmabs(~K, a)), n, c, kabs_rows(~K, ~F, ~H, a, n, c, hc), hc0)

# the checker's I - A B in F
def ofkm_imm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +n: Nat, +a: N.KMat(~K), +b: N.KMat(~K)) -> {N.ofkm(~K, ~F, ~H, CK.imm(~K, n, a, b)) == M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)))) : M.Mat(~F)}:
  %KA.kmadd_ofk(~K, ~F, ~H, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, a, b))) : {_ == M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)))) : M.Mat(~F)}
  %KA.kident_ofk(~K, ~F, ~H, n) : {M.madd(~F, _, N.ofkm(~K, ~F, ~H, KA.kmneg(~K, KA.kmatmul(~K, a, b)))) == M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)))) : M.Mat(~F)}
  %KA.kmneg_ofk(~K, ~F, ~H, KA.kmatmul(~K, a, b)) : {M.madd(~F, M.ident(~F, n), _) == M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)))) : M.Mat(~F)}
  %KA.kmatmul_ofk(~K, ~F, ~H, a, b) : {M.madd(~F, M.ident(~F, n), M.mneg(~F, _)) == M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)))) : M.Mat(~F)}
  {==}

# The window
# ----------
# Every radius r with 2S <= r and r + rho <= rb passes the checker, given
# |Y| <= yn, |I - Y Jc| <= thL, |I - Jc Y| <= thR < 1 and the smallness
# thL + yn n lam rb + yn m lam rho <= 1/2 (S the largest entry of the
# self-map bound at radius 0).


def nrows_srm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>) -> {GJ.nrows(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, eqs)))) == CK.eqlen(eqs) : Nat}:
  match eqs:
    case Nil{}:
      {==}
    case Con{e, es}:
      %Equal.sym(Nat, GJ.nrows(~F, N.ofkm(~K, ~F, ~H, CK.mradii(~K, CK.srows(~K, box, cnt, lo, es)))), CK.eqlen(es), nrows_srm(~K, ~F, ~H, box, cnt, lo, es)) : {1n+_ == 1n+CK.eqlen(es) : Nat}
      {==}

def rf_eq(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +r: S.D) -> {N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)) == frep(~F, n, M.ofd(~F, r)) : M.Vec(~F)}:
  Equal.trans(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), M.ofdv(~F, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), AP.ofkv_d(~F, ~H, NU.dreps(n, r)), ofdv_dreps(~F, n, r))

def lrf(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +r: S.D) -> {M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r))) == n : Nat}:
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), rf_eq(~F, ~H, n, r)) : {M.len(~F, _) == n : Nat}
  len_frep(~F, n, M.ofd(~F, r))

def vnrf(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r))) -> O.le(~F, NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r))), M.ofd(~F, r)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), rf_eq(~F, ~H, n, r)) : O.le(~F, NP.vn(~F, _), M.ofd(~F, r))
  vn_frep(~F, n, M.ofd(~F, r), hr0)

# the checker's Jacobian centers at its box: Jc
def jc_ckb(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +yr: List<&2, S.D>) -> {N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))) == NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))) : M.Mat(~F)}:
  %cen_ckb(~F, ~H, n, yc, yr, pc, pr, lyc, lpp) : {N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))) == DV.jac(~F, _, eqs, ST.iota(n, 0n)) : M.Mat(~F)}
  BP.mcen_jac(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), n, 0n, eqs, hh)

# |I - Y J0y| in the checker's numbers is at most thL
def imm_mn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +yr: List<&2, S.D>) -> O.le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, CK.imm(~KI.dnum(), n, ym, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)))), n), thL):
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, CK.imm(~KI.dnum(), n, ym, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)))), M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)))))), ofkm_imm(~KI.dnum(), ~F, ~H, n, ym, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)))) : O.le(~F, NP.mnorm(~F, _, n), thL)
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, ym), M.ofdm(~F, ym), AP.ofkm_d(~F, ~H, ym)) : O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, _, N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)))))), n), thL)
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), jc_ckb(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, yr)) : O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), _))), n), thL)
  hthl

def ym_mn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL)) -> O.le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n), yn):
  kabs_mn(~KI.dnum(), ~F, ~H, ym, n, yn, hyn0, (%Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, ym), M.ofdm(~F, ym), AP.ofkm_d(~F, ~H, ym)) : O.le(~F, NP.mnorm(~F, _, n), yn)
    hyn))

# the contraction vector at radius r: |g| <= thL r + yn n lam rb r
def gvec_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r)), +hr1: O.le(~F, M.ofd(~F, r), rb)) -> O.le(~F, NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), O.add(F, O.mul(F, thL, M.ofd(~F, r)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r))))):
  +yrr = NU.dreps(n, r)
  +rF = N.ofkv(~KI.dnum(), ~F, ~H, yrr)
  +aK = CK.imm(~KI.dnum(), n, ym, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yrr, pc, pr)))
  +dK = CK.mradii(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yrr, pc, pr))
  +pP = M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), rF)
  +qQ = M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF))
  +ldk = Equal.trans(Nat, M.len(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), GJ.nrows(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK)), n, Equal.sym(Nat, GJ.nrows(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK)), M.len(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), GJ.len_matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), Equal.trans(Nat, GJ.nrows(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK)), CK.eqlen(eqs), n, nrows_srm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yrr, pc, pr), n, 0n, eqs), hn))
  +gb = gbox_ckb(~F, ~H, n, yc, yrr, pc, pr, lyc, lpp, r, kfit_dreps(n, r), rb, bb, hc, hr0, hr1, hpn, hpr)
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, yrr, ym, pc, pr)), M.vadd(~F, pP, qQ), CP.gF_ok(~KI.dnum(), ~F, ~H, eqs, n, yc, yrr, ym, pc, pr)) : O.le(~F, NP.vn(~F, _), O.add(F, O.mul(F, thL, M.ofd(~F, r)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)))))
  DM.le_trans(~F, NP.vn(~F, M.vadd(~F, pP, qQ)), O.add(F, NP.vn(~F, pP), NP.vn(~F, qQ)), O.add(F, O.mul(F, thL, M.ofd(~F, r)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)))),
    AP.vn_add(~F, pP, qQ),
    FV.le_add2(~F, NP.vn(~F, pP), O.mul(F, thL, M.ofd(~F, r)), NP.vn(~F, qQ), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r))),
      DM.le_trans(~F, NP.vn(~F, pP), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n), NP.vn(~F, rF)), O.mul(F, thL, M.ofd(~F, r)), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n, rF, lrf(~F, ~H, n, r)),
        NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n), thL, NP.vn(~F, rF), M.ofd(~F, r), FV.vmax_nn(~F, rF), hthl0, kabs_mn(~KI.dnum(), ~F, ~H, aK, n, thL, hthl0, imm_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, yrr)), vnrf(~F, ~H, n, r, hr0))),
      DM.le_trans(~F, NP.vn(~F, qQ), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n), NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r))), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF), ldk),
        NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n), yn, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)), FV.vmax_nn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), hyn0, ym_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0),
          DM.le_trans(~F, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n), NP.vn(~F, rF)), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n, rF, lrf(~F, ~H, n, r)),
            NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), NP.vn(~F, rF), M.ofd(~F, r), FV.vmax_nn(~F, rF), AP.lr_nn(~F, n, lam, rb, hl0, hrb), srad_mn(~KI.dnum(), ~F, ~H, rb, bb, hrb, hb, CK.box(~KI.dnum(), n, yc, yrr, pc, pr), gb, lam, ms, hl0, eqs, hq, hh, n, 0n), vnrf(~F, ~H, n, r, hr0)))))))

# Lengths
# -------

def klen_kvadd(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K), +n: Nat, hu: {KA.klen(~K, u) == n : Nat}, hw: {KA.klen(~K, w) == n : Nat}) -> {KA.klen(~K, KA.kvadd(~K, u, w)) == n : Nat}:
  match u w n:
    case Nil{} w n:
      hw
    case Con{a, us} Nil{} n:
      hu
    case Con{+a, +us} Con{+b, +ws} 0n:
      FO.absurd({KA.klen(~K, KA.kvadd(~K, Con{a, us}, Con{b, ws})) == 0n : Nat}, FV.succ_ne(KA.klen(~K, us), hu))
    case Con{+a, +us} Con{+b, +ws} 1n++k:
      %Equal.sym(Nat, KA.klen(~K, KA.kvadd(~K, us, ws)), k, klen_kvadd(~K, us, ws, k, LN.succ_inj(KA.klen(~K, us), k, hu), LN.succ_inj(KA.klen(~K, ws), k, hw))) : {1n+_ == 1n+k : Nat}
      {==}

def klen_kmatvec(~K: N.Num, a: N.KMat(~K), +v: N.KVec(~K)) -> {KA.klen(~K, KA.kmatvec(~K, a, v)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, KA.klen(~K, KA.kmatvec(~K, rs, v)), CK.mlen(~K, rs), klen_kmatvec(~K, rs, v)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def klen_kvabs(~K: N.Num, u: N.KVec(~K)) -> {KA.klen(~K, KA.kvabs(~K, u)) == KA.klen(~K, u) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{a, us}:
      %Equal.sym(Nat, KA.klen(~K, KA.kvabs(~K, us)), KA.klen(~K, us), klen_kvabs(~K, us)) : {1n+_ == 1n+KA.klen(~K, us) : Nat}
      {==}

def mlen_kmabs(~K: N.Num, a: N.KMat(~K)) -> {CK.mlen(~K, KA.kmabs(~K, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, CK.mlen(~K, KA.kmabs(~K, rs)), CK.mlen(~K, rs), mlen_kmabs(~K, rs)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def mlen_kmneg(~K: N.Num, a: N.KMat(~K)) -> {CK.mlen(~K, KA.kmneg(~K, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, CK.mlen(~K, KA.kmneg(~K, rs)), CK.mlen(~K, rs), mlen_kmneg(~K, rs)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def mlen_kmatmul(~K: N.Num, a: N.KMat(~K), +b: N.KMat(~K)) -> {CK.mlen(~K, KA.kmatmul(~K, a, b)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, CK.mlen(~K, KA.kmatmul(~K, rs, b)), CK.mlen(~K, rs), mlen_kmatmul(~K, rs, b)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def mlen_kshift(~K: N.Num, a: N.KMat(~K)) -> {CK.mlen(~K, KA.kshift(~K, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, CK.mlen(~K, KA.kshift(~K, rs)), CK.mlen(~K, rs), mlen_kshift(~K, rs)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def mlen_kident(~K: N.Num, n: Nat) -> {CK.mlen(~K, KA.kident(~K, n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, CK.mlen(~K, KA.kshift(~K, KA.kident(~K, k))), CK.mlen(~K, KA.kident(~K, k)), mlen_kshift(~K, KA.kident(~K, k))) : {1n+_ == 1n+k : Nat}
      %Equal.sym(Nat, CK.mlen(~K, KA.kident(~K, k)), k, mlen_kident(~K, k)) : {1n+_ == 1n+k : Nat}
      {==}

def mlen_kmadd(~K: N.Num, a: N.KMat(~K), b: N.KMat(~K), +n: Nat, ha: {CK.mlen(~K, a) == n : Nat}, hb: {CK.mlen(~K, b) == n : Nat}) -> {CK.mlen(~K, KA.kmadd(~K, a, b)) == n : Nat}:
  match a b n:
    case Nil{} b n:
      hb
    case Con{r, rs} Nil{} n:
      ha
    case Con{+r, +rs} Con{+t, +ts} 0n:
      FO.absurd({CK.mlen(~K, KA.kmadd(~K, Con{r, rs}, Con{t, ts})) == 0n : Nat}, FV.succ_ne(CK.mlen(~K, rs), ha))
    case Con{+r, +rs} Con{+t, +ts} 1n++k:
      %Equal.sym(Nat, CK.mlen(~K, KA.kmadd(~K, rs, ts)), k, mlen_kmadd(~K, rs, ts, k, LN.succ_inj(CK.mlen(~K, rs), k, ha), LN.succ_inj(CK.mlen(~K, ts), k, hb))) : {1n+_ == 1n+k : Nat}
      {==}

def mlen_imm(~K: N.Num, +n: Nat, +a: N.KMat(~K), +b: N.KMat(~K), +ha: {CK.mlen(~K, a) == n : Nat}) -> {CK.mlen(~K, CK.imm(~K, n, a, b)) == n : Nat}:
  mlen_kmadd(~K, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, a, b)), n, mlen_kident(~K, n), Equal.trans(Nat, CK.mlen(~K, KA.kmneg(~K, KA.kmatmul(~K, a, b))), CK.mlen(~K, KA.kmatmul(~K, a, b)), n, mlen_kmneg(~K, KA.kmatmul(~K, a, b)), Equal.trans(Nat, CK.mlen(~K, KA.kmatmul(~K, a, b)), CK.mlen(~K, a), n, mlen_kmatmul(~K, a, b), ha)))

def mlen_mcen(~K: N.Num, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>) -> {CK.mlen(~K, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, eqs))) == CK.eqlen(eqs) : Nat}:
  match eqs:
    case Nil{}:
      {==}
    case Con{e, es}:
      %Equal.sym(Nat, CK.mlen(~K, CK.mcenters(~K, CK.srows(~K, box, cnt, lo, es))), CK.eqlen(es), mlen_mcen(~K, box, cnt, lo, es)) : {1n+_ == 1n+CK.eqlen(es) : Nat}
      {==}

def nrows_ofkm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> {GJ.nrows(~F, N.ofkm(~K, ~F, ~H, a)) == CK.mlen(~K, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, GJ.nrows(~F, N.ofkm(~K, ~F, ~H, rs)), CK.mlen(~K, rs), nrows_ofkm(~K, ~F, ~H, rs)) : {1n+_ == 1n+CK.mlen(~K, rs) : Nat}
      {==}

def nrows_mzm(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>) -> {GJ.nrows(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, box, cnt, lo, eqs))) == CK.eqlen(eqs) : Nat}:
  match eqs:
    case Nil{}:
      {==}
    case Con{e, es}:
      %Equal.sym(Nat, GJ.nrows(~F, N.ofkm(~K, ~F, ~H, mzm(~K, ~F, ~H, box, cnt, lo, es))), CK.eqlen(es), nrows_mzm(~K, ~F, ~H, box, cnt, lo, es)) : {1n+_ == 1n+CK.eqlen(es) : Nat}
      {==}

# the checker's vectors have n entries (Y has n rows)
def klen_gvec(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +hym: {CK.mlen(~K, ym) == n : Nat}) -> {KA.klen(~K, CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr)) == n : Nat}:
  +aK = CK.imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)))
  +dK = CK.mradii(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))
  klen_kvadd(~K, KA.kmatvec(~K, KA.kmabs(~K, aK), yr), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, dK, yr)), n,
    Equal.trans(Nat, KA.klen(~K, KA.kmatvec(~K, KA.kmabs(~K, aK), yr)), CK.mlen(~K, KA.kmabs(~K, aK)), n, klen_kmatvec(~K, KA.kmabs(~K, aK), yr), Equal.trans(Nat, CK.mlen(~K, KA.kmabs(~K, aK)), CK.mlen(~K, aK), n, mlen_kmabs(~K, aK), mlen_imm(~K, n, ym, CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr)), hym))),
    Equal.trans(Nat, KA.klen(~K, KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, dK, yr))), CK.mlen(~K, KA.kmabs(~K, ym)), n, klen_kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, dK, yr)), Equal.trans(Nat, CK.mlen(~K, KA.kmabs(~K, ym)), CK.mlen(~K, ym), n, mlen_kmabs(~K, ym), hym)))

def klen_svec(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +hym: {CK.mlen(~K, ym) == n : Nat}) -> {KA.klen(~K, CK.svec(~K, eqs, n, yc, yr, ym, pc, pr)) == n : Nat}:
  +fv = KA.kmatvec(~K, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs))
  +zv = KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, CK.mcenters(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), CK.mradii(~K, CK.rowsz(~K, eqs, n, yc, yr, pc, pr))), pr)
  klen_kvadd(~K, KA.kvadd(~K, KA.kvabs(~K, fv), KA.kmatvec(~K, KA.kmabs(~K, ym), zv)), CK.gvec(~K, eqs, n, yc, yr, ym, pc, pr), n,
    klen_kvadd(~K, KA.kvabs(~K, fv), KA.kmatvec(~K, KA.kmabs(~K, ym), zv), n,
      Equal.trans(Nat, KA.klen(~K, KA.kvabs(~K, fv)), KA.klen(~K, fv), n, klen_kvabs(~K, fv), Equal.trans(Nat, KA.klen(~K, fv), CK.mlen(~K, ym), n, klen_kmatvec(~K, ym, CK.kvals(~K, KA.kapp(~K, yc, pc), eqs)), hym)),
      Equal.trans(Nat, KA.klen(~K, KA.kmatvec(~K, KA.kmabs(~K, ym), zv)), CK.mlen(~K, KA.kmabs(~K, ym)), n, klen_kmatvec(~K, KA.kmabs(~K, ym), zv), Equal.trans(Nat, CK.mlen(~K, KA.kmabs(~K, ym)), CK.mlen(~K, ym), n, mlen_kmabs(~K, ym), hym))),
    klen_gvec(~K, eqs, n, yc, yr, ym, pc, pr, hym))

def klen_ivec(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +hn: {CK.eqlen(eqs) == n : Nat}, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> {KA.klen(~K, CK.ivec(~K, eqs, n, yc, yr, ym, pc, pr)) == n : Nat}:
  +mc = CK.mcenters(~K, CK.rowsy(~K, eqs, n, yc, yr, pc, pr))
  Equal.trans(Nat, KA.klen(~K, CK.ivec(~K, eqs, n, yc, yr, ym, pc, pr)), CK.mlen(~K, KA.kmabs(~K, CK.imm(~K, n, mc, ym))), n, klen_kmatvec(~K, KA.kmabs(~K, CK.imm(~K, n, mc, ym)), KA.kones(~K, n)),
    Equal.trans(Nat, CK.mlen(~K, KA.kmabs(~K, CK.imm(~K, n, mc, ym))), CK.mlen(~K, CK.imm(~K, n, mc, ym)), n, mlen_kmabs(~K, CK.imm(~K, n, mc, ym)), mlen_imm(~K, n, mc, ym, Equal.trans(Nat, CK.mlen(~K, mc), CK.eqlen(eqs), n, mlen_mcen(~K, CK.box(~K, n, yc, yr, pc, pr), n, 0n, eqs), hn))))

# The self-map at r against r = 0
# --------------------------------
# svec = |Y f| + B + G: |Y f| is the same at both radii, B grows by at
# most |Y| (m lam r) rho, G(r) is first order in r and G(0) = 0. With
# s0's entries at most S = dvmax(s0) <= r/2, every entry of svec(r) is
# at most r.

def dvmax_nn(~F: O.OField, xs: List<&2, S.D>) -> O.le(~F, O.zero(F), M.ofd(~F, NU.dvmax(xs))):
  match xs:
    case Nil{}:
      %DM.ofd_zero(~F) : O.le(~F, O.zero(F), _)
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +t}:
      DM.le_trans(~F, O.zero(F), M.ofd(~F, NU.dvmax(t)), M.ofd(~F, NU.dmax(x, NU.dvmax(t))), dvmax_nn(~F, t), DG.ndmax_r(~F, x, NU.dvmax(t)))

def dvmax_at(~F: O.OField, xs: List<&2, S.D>, k: Nat) -> O.le(~F, O.lookup(~F, M.ofdv(~F, xs), k), M.ofd(~F, NU.dvmax(xs))):
  match xs k:
    case Nil{} k:
      dvmax_nn(~F, Nil{})
    case Con{+x, +t} 0n:
      DG.ndmax_l(~F, x, NU.dvmax(t))
    case Con{+x, +t} 1n++j:
      DM.le_trans(~F, O.lookup(~F, M.ofdv(~F, t), j), M.ofd(~F, NU.dvmax(t)), M.ofd(~F, NU.dmax(x, NU.dvmax(t))), dvmax_at(~F, t, j), DG.ndmax_r(~F, x, NU.dvmax(t)))

# n entries, each at most t: below n copies of t
def rle_of_all(~F: O.OField, u: M.Vec(~F), +n: Nat, +t: O.C(F), +h: GJ.All(~(k => O.le(~F, O.lookup(~F, u, k), t)), M.len(~F, u)), lu: {M.len(~F, u) == n : Nat}) -> FV.rle(~F, u, frep(~F, n, t)):
  match u n:
    case Nil{} 0n:
      Unit{}
    case Nil{} 1n++k:
      FO.absurd(FV.rle(~F, Nil{}, frep(~F, 1n+k, t)), FV.zero_ne(k, lu))
    case Con{+a, +us} 0n:
      FO.absurd(FV.rle(~F, Con{a, us}, frep(~F, 0n, t)), FV.succ_ne(M.len(~F, us), lu))
    case Con{+a, +us} 1n++k:
      (GJ.all_at(~(j => O.le(~F, O.lookup(~F, Con{a, us}, j), t)), 1n+M.len(~F, us), h, 0n, {==}),
       rle_of_all(~F, us, k, t, DG.all_shift(~(j => O.le(~F, O.lookup(~F, Con{a, us}, j), t)), M.len(~F, us), h), LN.succ_inj(M.len(~F, us), k, lu)))

def rle_rep(~F: O.OField, ~u: M.Vec(~F), ~t: O.C(F), ~f: @k: Nat -> O.le(~F, O.lookup(~F, u, k), t), +n: Nat, lu: {M.len(~F, u) == n : Nat}) -> FV.rle(~F, u, frep(~F, n, t)):
  rle_of_all(~F, u, n, t, GJ.all_mk(~M.len(~F, u), ~(k => O.le(~F, O.lookup(~F, u, k), t)), ~(k => hk => f(k)), M.len(~F, u), KA.natle_refl(M.len(~F, u))), lu)

def lk3(~F: O.OField, +a: M.Vec(~F), +b: M.Vec(~F), +g: M.Vec(~F), +k: Nat) -> {O.lookup(~F, M.vadd(~F, M.vadd(~F, a, b), g), k) == O.add(F, O.add(F, O.lookup(~F, a, k), O.lookup(~F, b, k)), O.lookup(~F, g, k)) : O.C(F)}:
  %GJ.look_vadd(~F, M.vadd(~F, a, b), g, k) : {_ == O.add(F, O.add(F, O.lookup(~F, a, k), O.lookup(~F, b, k)), O.lookup(~F, g, k)) : O.C(F)}
  %GJ.look_vadd(~F, a, b, k) : {O.add(F, _, O.lookup(~F, g, k)) == O.add(F, O.add(F, O.lookup(~F, a, k), O.lookup(~F, b, k)), O.lookup(~F, g, k)) : O.C(F)}
  {==}

# a + br + gr <= sd + d1 + d2 + d3 from a + b0 + g0 <= sd, |br - b0| <= d1, |gr| <= d2, |g0| <= d3
def cs_ent(~F: O.OField, +a: O.C(F), +br: O.C(F), +gr: O.C(F), +b0: O.C(F), +g0: O.C(F), +sd: O.C(F), +d1: O.C(F), +d2: O.C(F), +d3: O.C(F), +hy: O.le(~F, O.add(F, O.add(F, a, b0), g0), sd), h1: M.bnd(~F, O.sub(~F, br, b0), d1), h2: M.bnd(~F, gr, d2), h3: M.bnd(~F, g0, d3)) -> O.le(~F, O.add(F, O.add(F, a, br), gr), O.add(F, O.add(F, O.add(F, sd, d1), d2), d3)):
  (p1, q1) = h1
  (p2, q2) = h2
  (p3, q3) = h3
  FV.le_of_sub(~F, O.add(F, O.add(F, a, br), gr), O.add(F, O.add(F, O.add(F, sd, d1), d2), d3), FM.nn_eq(~F, O.sub(~F, O.add(F, O.add(F, O.add(F, sd, d1), d2), d3), O.add(F, O.add(F, a, br), gr)), O.add(F, O.add(F, O.add(F, O.sub(~F, sd, O.add(F, O.add(F, a, b0), g0)), O.sub(~F, d1, O.sub(~F, br, b0))), O.sub(~F, d2, gr)), O.add(F, d3, g0)),
    FR.fring_eq(~F, [a, br, gr, b0, g0, sd, d1, d2, d3], E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{5n}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZSub{E.ZVar{6n}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZSub{E.ZVar{7n}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{8n}, E.ZVar{4n}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{5n}, E.ZVar{6n}}, E.ZVar{7n}}, E.ZVar{8n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, sd, O.add(F, O.add(F, a, b0), g0)), O.sub(~F, d1, O.sub(~F, br, b0))), O.sub(~F, d2, gr)), O.add(F, d3, g0), FO.nonneg_add(~F, O.add(F, O.sub(~F, sd, O.add(F, O.add(F, a, b0), g0)), O.sub(~F, d1, O.sub(~F, br, b0))), O.sub(~F, d2, gr), FO.nonneg_add(~F, O.sub(~F, sd, O.add(F, O.add(F, a, b0), g0)), O.sub(~F, d1, O.sub(~F, br, b0)), FM.sub_nonneg(~F, O.add(F, O.add(F, a, b0), g0), sd, hy), p1), p2), q3)))

# the same, entry k of the vectors
def cs_at(~F: O.OField, +a: M.Vec(~F), +br: M.Vec(~F), +gr: M.Vec(~F), +b0: M.Vec(~F), +g0: M.Vec(~F), +sd: O.C(F), +k: Nat, +hy: O.le(~F, O.lookup(~F, M.vadd(~F, M.vadd(~F, a, b0), g0), k), sd)) -> O.le(~F, O.lookup(~F, M.vadd(~F, M.vadd(~F, a, br), gr), k), O.add(F, O.add(F, O.add(F, sd, NP.vn(~F, BX.vsub(~F, br, b0))), NP.vn(~F, gr)), NP.vn(~F, g0))):
  %Equal.sym(O.C(F), O.lookup(~F, M.vadd(~F, M.vadd(~F, a, br), gr), k), O.add(F, O.add(F, O.lookup(~F, a, k), O.lookup(~F, br, k)), O.lookup(~F, gr, k)), lk3(~F, a, br, gr, k)) : O.le(~F, _, O.add(F, O.add(F, O.add(F, sd, NP.vn(~F, BX.vsub(~F, br, b0))), NP.vn(~F, gr)), NP.vn(~F, g0)))
  cs_ent(~F, O.lookup(~F, a, k), O.lookup(~F, br, k), O.lookup(~F, gr, k), O.lookup(~F, b0, k), O.lookup(~F, g0, k), sd, NP.vn(~F, BX.vsub(~F, br, b0)), NP.vn(~F, gr), NP.vn(~F, g0),
    RL.le_rw_l(~F, O.lookup(~F, M.vadd(~F, M.vadd(~F, a, b0), g0), k), O.add(F, O.add(F, O.lookup(~F, a, k), O.lookup(~F, b0, k)), O.lookup(~F, g0, k)), sd, lk3(~F, a, b0, g0, k), hy),
    (%DG.look_diff(~F, br, b0, k) : M.bnd(~F, _, NP.vn(~F, BX.vsub(~F, br, b0)))
      AP.lkb(~F, BX.vsub(~F, br, b0), k)),
    AP.lkb(~F, gr, k), AP.lkb(~F, g0, k))

def vall_z(~F: O.OField, +v: M.Vec(~F), +c: O.C(F), h: M.vbnd.all(~F, v, O.mul(F, c, O.zero(F)))) -> M.vbnd.all(~F, v, O.zero(F)):
  %FR.fring_eq(~F, [c], E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==}) : M.vbnd.all(~F, v, _)
  h

def vn_z(~F: O.OField, +v: M.Vec(~F), h: M.vbnd.all(~F, v, O.zero(F))) -> O.le(~F, NP.vn(~F, v), O.zero(F)):
  FV.vmax_lub(~F, v, O.zero(F), h, FO.le_refl(~F, O.zero(F)))


# G at radius 0 (no unknowns' radii) is 0
def g0_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>) -> O.le(~F, NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.zero(F)):
  +aK = CK.imm(~KI.dnum(), n, ym, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, Nil{}, pc, pr)))
  +dK = CK.mradii(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, Nil{}, pc, pr))
  +pP = M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), N.ofkv(~KI.dnum(), ~F, ~H, Nil{}))
  +dv = M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), N.ofkv(~KI.dnum(), ~F, ~H, Nil{}))
  +qQ = M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), dv)
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), M.vadd(~F, pP, qQ), CP.gF_ok(~KI.dnum(), ~F, ~H, eqs, n, yc, Nil{}, ym, pc, pr)) : O.le(~F, NP.vn(~F, _), O.zero(F))
  DM.le_trans(~F, NP.vn(~F, M.vadd(~F, pP, qQ)), O.add(F, NP.vn(~F, pP), NP.vn(~F, qQ)), O.zero(F), AP.vn_add(~F, pP, qQ),
    FV.le_rw_r(~F, O.add(F, NP.vn(~F, pP), NP.vn(~F, qQ)), O.add(F, O.zero(F), O.zero(F)), O.zero(F), FR.fring_eq(~F, [O.zero(F)], E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==}),
      FV.le_add2(~F, NP.vn(~F, pP), O.zero(F), NP.vn(~F, qQ), O.zero(F),
        vn_z(~F, pP, vall_z(~F, pP, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, Nil{}))), NP.mv_le(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), N.ofkv(~KI.dnum(), ~F, ~H, Nil{}), O.zero(F), Unit{}, FO.le_refl(~F, O.zero(F))))),
        vn_z(~F, qQ, vall_z(~F, qQ, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.len(~F, dv)), NP.mv_le(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), dv, O.zero(F), vall_z(~F, dv, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, Nil{}))), NP.mv_le(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), N.ofkv(~KI.dnum(), ~F, ~H, Nil{}), O.zero(F), Unit{}, FO.le_refl(~F, O.zero(F)))), FO.le_refl(~F, O.zero(F))))))))

# |Y f(center)|, and B = |Y| ((|J0z| + Dz) rho) over the box with unknowns' radii yr
def ayf(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>) -> N.KVec(~KI.dnum()):
  KA.kvabs(~KI.dnum(), KA.kmatvec(~KI.dnum(), ym, CK.kvals(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), eqs)))

def bk(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +yr: List<&2, S.D>) -> N.KVec(~KI.dnum()):
  KA.kmatvec(~KI.dnum(), KA.kmabs(~KI.dnum(), ym), KA.kmatvec(~KI.dnum(), mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs), pr))

def svec_f(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +yr: List<&2, S.D>) -> {N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr)) == M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr))) : M.Vec(~F)}:
  %KA.kvadd_ofk(~KI.dnum(), ~F, ~H, KA.kvadd(~KI.dnum(), ayf(~F, ~H, n, eqs, yc, pc, pr, ym), bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr)), CK.gvec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr)) : {_ == M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr))) : M.Vec(~F)}
  %KA.kvadd_ofk(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym), bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr)) : {M.vadd(~F, _, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr))) == M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, yr, ym, pc, pr))) : M.Vec(~F)}
  {==}

def bf_eq(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +yr: List<&2, S.D>) -> {N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, yr)) == M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr))) : M.Vec(~F)}:
  %KA.kmatvec_ofk(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym), KA.kmatvec(~KI.dnum(), mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs), pr)) : {_ == M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr))) : M.Vec(~F)}
  %KA.kmatvec_ofk(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs), pr) : {M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), _) == M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, yr, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr))) : M.Vec(~F)}
  {==}

def e0_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +r: S.D, hr0: O.le(~F, O.zero(F), M.ofd(~F, r))) -> O.le(~F, O.zero(F), N.emap(KI.dnum(), F, H, r)):
  %Equal.sym(O.C(F), N.emap(KI.dnum(), F, H, r), M.ofd(~F, r), AP.hofd(~F, ~H, r)) : O.le(~F, O.zero(F), _)
  hr0

def rnn_kv(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +v: List<&2, S.D>, h: FV.rnn(~F, M.ofdv(~F, v))) -> FV.rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, v)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, v), M.ofdv(~F, v), AP.ofkv_d(~F, ~H, v)) : FV.rnn(~F, _)
  h


# B(r) - B(0): |Y| ((Mz(r) - Mz(0)) rho), at most yn (m lam r) rb
def bdiff_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r)), +hr1: O.le(~F, M.ofd(~F, r), rb)) -> O.le(~F, NP.vn(~F, BX.vsub(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb))):
  +b0 = CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr)
  +b1 = CK.box(~KI.dnum(), n, yc, NU.dreps(n, r), pc, pr)
  +m = KA.klen(~KI.dnum(), pc)
  +ya = N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym))
  +m0 = N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, b0, m, n, eqs))
  +m1 = N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, b1, m, n, eqs))
  +pv = N.ofkv(~KI.dnum(), ~F, ~H, pr)
  +md = M.madd(~F, m1, M.mneg(~F, m0))
  +w = M.matvec(~F, md, pv)
  +he0 = e0_of(~F, ~H, r, hr0)
  +hpk = rnn_kv(~F, ~H, pr, hpn)
  +hcen = Equal.trans(M.Vec(~F), BP.cen(~KI.dnum(), ~F, ~H, b0), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), BP.cen(~KI.dnum(), ~F, ~H, b1), cen_ckb(~F, ~H, n, yc, Nil{}, pc, pr, lyc, lpp), Equal.sym(M.Vec(~F), BP.cen(~KI.dnum(), ~F, ~H, b1), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), cen_ckb(~F, ~H, n, yc, NU.dreps(n, r), pc, pr, lyc, lpp)))
  +hp = bpair_ckb(~F, ~H, n, yc, pc, pr, lyc, lpp, r, he0, hpk)
  +hg = gbox_ckb(~F, ~H, n, yc, NU.dreps(n, r), pc, pr, lyc, lpp, r, kfit_dreps(n, r), rb, bb, hc, hr0, hr1, hpn, hpr)
  +lw = Equal.trans(Nat, M.len(~F, w), GJ.nrows(~F, md), n, Equal.sym(Nat, GJ.nrows(~F, md), M.len(~F, w), GJ.len_matvec(~F, md, pv)), NW.nrows_madd(~F, m1, M.mneg(~F, m0), n, Equal.trans(Nat, GJ.nrows(~F, m1), CK.eqlen(eqs), n, nrows_mzm(~KI.dnum(), ~F, ~H, b1, m, n, eqs), hn), Equal.trans(Nat, GJ.nrows(~F, M.mneg(~F, m0)), GJ.nrows(~F, m0), n, NW.nrows_mneg(~F, m0), Equal.trans(Nat, GJ.nrows(~F, m0), CK.eqlen(eqs), n, nrows_mzm(~KI.dnum(), ~F, ~H, b0, m, n, eqs), hn))))
  +lp = Equal.trans(Nat, M.len(~F, pv), KA.klen(~KI.dnum(), pr), m, CP.len_ofkv(~KI.dnum(), ~F, ~H, pr), Equal.sym(Nat, KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr), lpp))
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), M.matvec(~F, ya, M.matvec(~F, m1, pv)), bf_eq(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))) : O.le(~F, NP.vn(~F, BX.vsub(~F, _, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb)))
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), M.matvec(~F, ya, M.matvec(~F, m0, pv)), bf_eq(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})) : O.le(~F, NP.vn(~F, BX.vsub(~F, M.matvec(~F, ya, M.matvec(~F, m1, pv)), _)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb)))
  %AP.mv_vsub(~F, ya, M.matvec(~F, m1, pv), M.matvec(~F, m0, pv)) : O.le(~F, NP.vn(~F, _), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb)))
  %CP.sj_ok(~F, m1, m0, pv) : O.le(~F, NP.vn(~F, M.matvec(~F, ya, _)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb)))
  DM.le_trans(~F, NP.vn(~F, M.matvec(~F, ya, w)), O.mul(F, NP.mnorm(~F, ya, n), NP.vn(~F, w)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, M.ofd(~F, r))), rb)), NP.mv_n(~F, ya, n, w, lw),
    NW.mm_le(~F, NP.mnorm(~F, ya, n), yn, NP.vn(~F, w), O.mul(F, O.mul(F, FR.ofn(~F, m), O.mul(F, lam, M.ofd(~F, r))), rb), FV.vmax_nn(~F, w), hyn0, ym_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0),
      DM.le_trans(~F, NP.vn(~F, w), O.mul(F, NP.mnorm(~F, md, m), NP.vn(~F, pv)), O.mul(F, O.mul(F, FR.ofn(~F, m), O.mul(F, lam, M.ofd(~F, r))), rb), NP.mv_n(~F, md, m, pv, lp),
        NW.mm_le(~F, NP.mnorm(~F, md, m), O.mul(F, FR.ofn(~F, m), O.mul(F, lam, M.ofd(~F, r))), NP.vn(~F, pv), rb, FV.vmax_nn(~F, pv), AP.lr_nn(~F, m, lam, M.ofd(~F, r), hl0, hr0),
          (%AP.hofd(~F, ~H, r) : O.le(~F, NP.mnorm(~F, md, m), O.mul(F, FR.ofn(~F, m), O.mul(F, lam, _)))
            mz_mn(~KI.dnum(), ~F, ~H, N.emap(KI.dnum(), F, H, r), rb, bb, he0, hrb, hb, b0, b1, hcen, hp, hg, lam, ms, hl0, eqs, hq, hh, m, n)),
          (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, pr), M.ofdv(~F, pr), AP.ofkv_d(~F, ~H, pr)) : O.le(~F, NP.vn(~F, _), rb)
            FV.vmax_lub(~F, M.ofdv(~F, pr), rb, hpr, hrb))))))

# ofd(1/2) twice is 1
def half_two(~F: O.OField) -> {O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())) == O.one(F) : O.C(F)}:
  FO.eq_of_sub(~F, O.add(F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(1n)))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(1n))))), O.one(F), FO.cert1(~F, O.sub(~F, O.add(F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(1n)))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(1n))))), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, O.ofp(~F, S.Pos.pow2(1n)))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(1n)))], E.ZSub{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(1n))))

# sd + db + dg + d0 <= R from sd <= q R, the bounds on db, dg and d0,
# and the window condition cw <= q (q + q = 1)
def cs_fin(~F: O.OField, +sd: O.C(F), +db: O.C(F), +dg: O.C(F), +d0: O.C(F), +R: O.C(F), +q: O.C(F), +thL: O.C(F), +yn: O.C(F), +nn: O.C(F), +mm: O.C(F), +lam: O.C(F), +rb: O.C(F), +hS: O.le(~F, sd, O.mul(F, q, R)), +hdb: O.le(~F, db, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb))), +hdg: O.le(~F, dg, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R)))), +hd0: O.le(~F, d0, O.zero(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb)))), q), +hR: O.le(~F, O.zero(F), R), +hq2: {O.add(F, q, q) == O.one(F) : O.C(F)}) -> O.le(~F, O.add(F, O.add(F, O.add(F, sd, db), dg), d0), R):
  FV.le_rw_r(~F, O.add(F, O.add(F, O.add(F, sd, db), dg), d0), O.mul(F, O.add(F, q, q), R), R,
    (%Equal.sym(O.C(F), O.add(F, q, q), O.one(F), hq2) : {O.mul(F, _, R) == R : O.C(F)}
      FR.fring_eq(~F, [R], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})),
    FV.le_of_sub(~F, O.add(F, O.add(F, O.add(F, sd, db), dg), d0), O.mul(F, O.add(F, q, q), R), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, q, q), R), O.add(F, O.add(F, O.add(F, sd, db), dg), d0)), O.add(F, O.add(F, O.add(F, O.add(F, O.sub(~F, O.mul(F, q, R), sd), O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R)), O.sub(~F, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb)), db)), O.sub(~F, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), dg)), O.sub(~F, O.zero(F), d0)),
      FR.fring_eq(~F, [sd, db, dg, d0, R, q, thL, yn, nn, mm, lam, rb], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{4n}}, E.ZVar{0n}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZAdd{E.ZAdd{E.ZVar{6n}, E.ZMul{E.ZVar{7n}, E.ZMul{E.ZVar{8n}, E.ZMul{E.ZVar{10n}, E.ZVar{11n}}}}}, E.ZMul{E.ZVar{7n}, E.ZMul{E.ZVar{9n}, E.ZMul{E.ZVar{10n}, E.ZVar{11n}}}}}}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZVar{7n}, E.ZMul{E.ZMul{E.ZVar{9n}, E.ZMul{E.ZVar{10n}, E.ZVar{4n}}}, E.ZVar{11n}}}, E.ZVar{1n}}}, E.ZSub{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{4n}}, E.ZMul{E.ZVar{7n}, E.ZMul{E.ZMul{E.ZVar{8n}, E.ZMul{E.ZVar{10n}, E.ZVar{11n}}}, E.ZVar{4n}}}}, E.ZVar{2n}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{5n}, E.ZVar{5n}}, E.ZVar{4n}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{3n}}}, {==}),
      FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.sub(~F, O.mul(F, q, R), sd), O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R)), O.sub(~F, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb)), db)), O.sub(~F, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), dg)), O.sub(~F, O.zero(F), d0),
        FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, O.mul(F, q, R), sd), O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R)), O.sub(~F, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb)), db)), O.sub(~F, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), dg),
          FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, q, R), sd), O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R)), O.sub(~F, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb)), db),
            FO.nonneg_add(~F, O.sub(~F, O.mul(F, q, R), sd), O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R), FM.sub_nonneg(~F, sd, O.mul(F, q, R), hS), FO.mul_nonneg(~F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R, FM.sub_nonneg(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb)))), q, hw), hR)),
            FM.sub_nonneg(~F, db, O.mul(F, yn, O.mul(F, O.mul(F, mm, O.mul(F, lam, R)), rb)), hdb)),
          FM.sub_nonneg(~F, dg, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), hdg)),
        FM.sub_nonneg(~F, d0, O.zero(F), hd0)))))

# The window's three bound conditions
# -----------------------------------


def lk_le(~F: O.OField, +v: M.Vec(~F), +k: Nat) -> O.le(~F, O.lookup(~F, v, k), NP.vn(~F, v)):
  FV.bnd_lo(~F, O.lookup(~F, v, k), NP.vn(~F, v), AP.lkb(~F, v, k))

# entry k of svec(r) is at most r
def cs_k(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +r: S.D, +k: Nat, +hT: O.le(~F, O.add(F, O.add(F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}))))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), M.ofd(~F, r))) -> O.le(~F, O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), k), M.ofd(~F, r)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r)))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), svec_f(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))) : O.le(~F, O.lookup(~F, _, k), M.ofd(~F, r))
  DM.le_trans(~F, O.lookup(~F, M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r)))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), k), O.add(F, O.add(F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}))))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), M.ofd(~F, r),
    cs_at(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), k,
      (%svec_f(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}) : O.le(~F, O.lookup(~F, _, k), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))
        (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), M.ofdv(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), AP.ofkv_d(~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))) : O.le(~F, O.lookup(~F, _, k), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))
          dvmax_at(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr), k)))),
    hT)

# the self-map condition at r, from S <= r/2 and the window cw <= 1/2
def cself_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r)), +hr1: O.le(~F, M.ofd(~F, r), rb), +hS: O.le(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r))), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half()))) -> {CK.cself(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr) == True{} : Bool}:
  +hT = cs_fin(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, NU.dreps(n, r))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, r), M.ofd(~F, NU.half()), thL, yn, FR.ofn(~F, n), FR.ofn(~F, KA.klen(~KI.dnum(), pc)), lam, rb, hS, bdiff_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, r, hr0, hr1), gvec_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, r, hr0, hr1), g0_bnd(~F, ~H, n, eqs, yc, pc, pr, ym), hw, hr0, half_two(~F))
  +lsr = Equal.trans(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), KA.klen(~KI.dnum(), CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), klen_svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr, hym))
  AP.kvle_of(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), NU.dreps(n, r),
    (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), rf_eq(~F, ~H, n, r)) : FV.rle(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), _)
      rle_rep(~F, ~N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), ~M.ofd(~F, r), ~(k => cs_k(~F, ~H, n, eqs, yc, pc, pr, ym, r, k, hT)), n, lsr)))

def vscale_frep(~F: O.OField, n: Nat, +c: O.C(F), +x: O.C(F)) -> {frep(~F, n, O.mul(F, c, x)) == M.vscale(~F, c, frep(~F, n, x)) : M.Vec(~F)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %vscale_frep(~F, k, c, x) : {Con{O.mul(F, c, x), frep(~F, k, O.mul(F, c, x))} == Con{O.mul(F, c, x), _} : M.Vec(~F)}
      {==}

# thL r + yn (n lam rb) r <= q r
def cg_le(~F: O.OField, +R: O.C(F), +q: O.C(F), +thL: O.C(F), +yn: O.C(F), +nn: O.C(F), +mm: O.C(F), +lam: O.C(F), +rb: O.C(F), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb)))), q), +hR: O.le(~F, O.zero(F), R), +hyn: O.le(~F, O.zero(F), yn), +hmm: O.le(~F, O.zero(F), mm), +hl: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb)) -> O.le(~F, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), O.mul(F, q, R)):
  FV.le_of_sub(~F, O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R))), O.mul(F, q, R), FM.nn_eq(~F, O.sub(~F, O.mul(F, q, R), O.add(F, O.mul(F, thL, R), O.mul(F, yn, O.mul(F, O.mul(F, nn, O.mul(F, lam, rb)), R)))), O.add(F, O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R), O.mul(F, O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))), R)),
    FR.fring_eq(~F, [R, q, thL, yn, nn, mm, lam, rb], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}}, E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}}}, E.ZVar{0n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, E.ZMul{E.ZVar{3n}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}, E.ZVar{0n}}}}}, {==}),
    FO.nonneg_add(~F, O.mul(F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R), O.mul(F, O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))), R),
      FO.mul_nonneg(~F, O.sub(~F, q, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))))), R, FM.sub_nonneg(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, nn, O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb)))), q, hw), hR),
      FO.mul_nonneg(~F, O.mul(F, yn, O.mul(F, mm, O.mul(F, lam, rb))), R, FO.mul_nonneg(~F, yn, O.mul(F, mm, O.mul(F, lam, rb)), hyn, FO.mul_nonneg(~F, mm, O.mul(F, lam, rb), hmm, FO.mul_nonneg(~F, lam, rb, hl, hrb))), hR))))

# the contraction condition at r (q = 1/2)
def ccon_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r)), +hr1: O.le(~F, M.ofd(~F, r), rb), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half()))) -> {CK.ccon(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), NU.half(), ym, pc, pr) == True{} : Bool}:
  +lg = Equal.trans(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), KA.klen(~KI.dnum(), CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), klen_gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr, hym))
  +hG = DM.le_trans(~F, NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), O.add(F, O.mul(F, thL, M.ofd(~F, r)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), gvec_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, r, hr0, hr1), cg_le(~F, M.ofd(~F, r), M.ofd(~F, NU.half()), thL, yn, FR.ofn(~F, n), FR.ofn(~F, KA.klen(~KI.dnum(), pc)), lam, rb, hw, hr0, hyn0, DG.ofn_nn(~F, KA.klen(~KI.dnum(), pc)), hl0, hrb))
  AP.kvle_of(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), KA.kvscale(~KI.dnum(), NU.half(), NU.dreps(n, r)),
    (%KA.kvscale_ofk(~KI.dnum(), ~F, ~H, NU.half(), NU.dreps(n, r)) : FV.rle(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), _)
      (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), rf_eq(~F, ~H, n, r)) : FV.rle(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), M.vscale(~F, N.emap(KI.dnum(), F, H, NU.half()), _))
        (%vscale_frep(~F, n, N.emap(KI.dnum(), F, H, NU.half()), M.ofd(~F, r)) : FV.rle(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), _)
          (%Equal.sym(O.C(F), N.emap(KI.dnum(), F, H, NU.half()), M.ofd(~F, NU.half()), AP.hofd(~F, ~H, NU.half())) : FV.rle(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), frep(~F, n, O.mul(F, _, M.ofd(~F, r))))
            rle_rep(~F, ~N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), ~O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), ~(k => DM.le_trans(~F, O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), k), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), lk_le(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr)), k), hG)), n, lg))))))

def klen_kones(~K: N.Num, n: Nat) -> {KA.klen(~K, KA.kones(~K, n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, KA.klen(~K, KA.kones(~K, k)), k, klen_kones(~K, k)) : {1n+_ == 1n+k : Nat}
      {==}

def vall_k1(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat) -> M.vbnd.all(~F, N.ofkv(~K, ~F, ~H, KA.kones(~K, n)), O.one(F)):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      ((%Equal.sym(O.C(F), N.emap(K, F, H, N.none(K)), O.one(F), N.e_one(K, F, H)) : M.bnd(~F, _, O.one(F))
         FV.bnd_self(~F, O.one(F), FO.one_nn(~F))),
       vall_k1(~K, ~F, ~H, k))

def vn_ones(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +n: Nat) -> O.le(~F, NP.vn(~F, N.ofkv(~K, ~F, ~H, KA.kones(~K, n))), O.one(F)):
  FV.vmax_lub(~F, N.ofkv(~K, ~F, ~H, KA.kones(~K, n)), O.one(F), vall_k1(~K, ~F, ~H, n), FO.one_nn(~F))

# entries below t from |v| < t
def vlt_of_vn(~F: O.OField, v: M.Vec(~F), +t: O.C(F), +h: O.lt(F, NP.vn(~F, v), t)) -> FV.vlt_all(~F, v, t):
  match v:
    case Nil{}:
      Unit{}
    case Con{+a, +as}:
      (FO.le_lt_trans(~F, a, NP.vn(~F, Con{a, as}), t, lk_le(~F, Con{a, as}, 0n), h),
       vlt_of_vn(~F, as, t, FO.le_lt_trans(~F, NP.vn(~F, as), NP.vn(~F, Con{a, as}), t, FV.fmax_r(~F, FV.fabs(~F, a), NP.vn(~F, as)), h)))


# |I - J0y Y| in the checker's numbers is at most thR
def imr_mn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +thR: O.C(F), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +yr: List<&2, S.D>) -> O.le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, CK.imm(~KI.dnum(), n, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)), ym)), n), thR):
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, CK.imm(~KI.dnum(), n, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)), ym)), M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))), N.ofkm(~KI.dnum(), ~F, ~H, ym)))), ofkm_imm(~KI.dnum(), ~F, ~H, n, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr)), ym)) : O.le(~F, NP.mnorm(~F, _, n), thR)
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, ym), M.ofdm(~F, ym), AP.ofkm_d(~F, ~H, ym)) : O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))), _))), n), thR)
  %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, yr, pc, pr))), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), jc_ckb(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, yr)) : O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, _, M.ofdm(~F, ym)))), n), thR)
  hthr

# the injectivity condition at r, from |I - J0y Y| <= thR < 1
def cinj_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +r: S.D) -> {CK.cinj(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr) == True{} : Bool}:
  +mc = CK.mcenters(~KI.dnum(), CK.rowsy(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), pc, pr))
  +xa = N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), CK.imm(~KI.dnum(), n, mc, ym)))
  +on = N.ofkv(~KI.dnum(), ~F, ~H, KA.kones(~KI.dnum(), n))
  +lon = Equal.trans(Nat, M.len(~F, on), KA.klen(~KI.dnum(), KA.kones(~KI.dnum(), n)), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, KA.kones(~KI.dnum(), n)), klen_kones(~KI.dnum(), n))
  AP.kvlt_ones_of(~KI.dnum(), ~F, ~H, CK.ivec(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), n, klen_ivec(~KI.dnum(), eqs, n, hn, yc, NU.dreps(n, r), ym, pc, pr),
    (%KA.kmatvec_ofk(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), CK.imm(~KI.dnum(), n, mc, ym)), KA.kones(~KI.dnum(), n)) : FV.vlt_all(~F, _, O.one(F))
      vlt_of_vn(~F, M.matvec(~F, xa, on), O.one(F),
        FO.le_lt_trans(~F, NP.vn(~F, M.matvec(~F, xa, on)), O.mul(F, NP.mnorm(~F, xa, n), NP.vn(~F, on)), O.one(F), NP.mv_n(~F, xa, n, on, lon),
          FO.le_lt_trans(~F, O.mul(F, NP.mnorm(~F, xa, n), NP.vn(~F, on)), O.mul(F, thR, O.one(F)), O.one(F), NW.mm_le(~F, NP.mnorm(~F, xa, n), thR, NP.vn(~F, on), O.one(F), FV.vmax_nn(~F, on), hthr0, kabs_mn(~KI.dnum(), ~F, ~H, CK.imm(~KI.dnum(), n, mc, ym), n, thR, hthr0, imr_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, thR, hthr, NU.dreps(n, r))), vn_ones(~KI.dnum(), ~F, ~H, n)),
            (%FR.fring_eq(~F, [thR], E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, {==}) : O.lt(F, _, O.one(F))
              hthr1))))))

# Shape
# -----

def rle_nil_rep(~F: O.OField, n: Nat, +x: O.C(F), +hx: O.le(~F, O.zero(F), x)) -> FV.rle(~F, Nil{}, frep(~F, n, x)):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      (hx, rle_nil_rep(~F, k, x, hx))

def rle_nil_rnn(~F: O.OField, v: M.Vec(~F), h: FV.rnn(~F, v)) -> FV.rle(~F, Nil{}, v):
  match v:
    case Nil{}:
      Unit{}
    case Con{a, as}:
      (h1, h2) = h
      (h1, rle_nil_rnn(~F, as, h2))

def shape_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r))) -> {CK.shape(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr) == True{} : Bool}:
  KA.band_i(KA.nateq(CK.eqlen(eqs), n), KA.band(KA.nateq(CK.mlen(~KI.dnum(), ym), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), yc), n), KA.band(KA.natle(KA.klen(~KI.dnum(), NU.dreps(n, r)), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr)), KA.band(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs)))))))), KA.nateq_of(CK.eqlen(eqs), n, hn),
  KA.band_i(KA.nateq(CK.mlen(~KI.dnum(), ym), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), yc), n), KA.band(KA.natle(KA.klen(~KI.dnum(), NU.dreps(n, r)), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr)), KA.band(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs))))))), KA.nateq_of(CK.mlen(~KI.dnum(), ym), n, hym),
  KA.band_i(KA.nateq(KA.klen(~KI.dnum(), yc), n), KA.band(KA.natle(KA.klen(~KI.dnum(), NU.dreps(n, r)), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr)), KA.band(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs)))))), KA.nateq_of(KA.klen(~KI.dnum(), yc), n, lyc),
  KA.band_i(KA.natle(KA.klen(~KI.dnum(), NU.dreps(n, r)), n), KA.band(KA.nateq(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr)), KA.band(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs))))),
    (%Equal.sym(Nat, KA.klen(~KI.dnum(), NU.dreps(n, r)), n, klen_dreps(n, r)) : {KA.natle(_, n) == True{} : Bool}
      KA.natle_refl(n)),
  KA.band_i(KA.nateq(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr)), KA.band(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs)))), KA.nateq_of(KA.klen(~KI.dnum(), pc), KA.klen(~KI.dnum(), pr), lpp),
  KA.band_i(KA.kvle(~KI.dnum(), Nil{}, NU.dreps(n, r)), KA.band(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs))),
    AP.kvle_of(~KI.dnum(), ~F, ~H, Nil{}, NU.dreps(n, r),
      (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, NU.dreps(n, r)), frep(~F, n, M.ofd(~F, r)), rf_eq(~F, ~H, n, r)) : FV.rle(~F, Nil{}, _)
        rle_nil_rep(~F, n, M.ofd(~F, r), hr0))),
  KA.band_i(KA.kvle(~KI.dnum(), Nil{}, pr), KA.band(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs)),
    AP.kvle_of(~KI.dnum(), ~F, ~H, Nil{}, pr, rle_nil_rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, pr), rnn_kv(~F, ~H, pr, hpn))),
  KA.band_i(CK.allheld(~KI.dnum(), eqs), CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs), hh, hab))))))))

# The window: every r with S <= r/2, r <= rb passes the block checker
def window_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +r: S.D, +hr0: O.le(~F, O.zero(F), M.ofd(~F, r)), +hr1: O.le(~F, M.ofd(~F, r), rb), +hS: O.le(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)))) -> {NU.okr(eqs, n, yc, r, ym, pc, pr) == True{} : Bool}:
  KA.band_i(CK.shape(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), CK.rest1(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), NU.half(), ym, pc, pr), shape_ok(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, r, hr0),
  KA.band_i(CK.factor(~KI.dnum(), NU.half()), CK.rest2(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), NU.half(), ym, pc, pr), {==},
  KA.band_i(CK.ccon(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), NU.half(), ym, pc, pr), CK.rest3(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), ccon_ok(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, r, hr0, hr1, hw),
  KA.band_i(CK.cself(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), CK.cinj(~KI.dnum(), eqs, n, yc, NU.dreps(n, r), ym, pc, pr), cself_ok(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, r, hr0, hr1, hS, hw), cinj_ok(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, thR, hthr0, hthr, hthr1, r)))))

# The radius search
# -----------------
# r0 = (65/64) S rounded up at 8 bits, each step r (17/16) rounded up. A
# radius that fails is below 2S (it is at most U <= rb, so the window
# would pass it), so the next is at most U = (17/16)(1 + 2^-7) 2S; and
# each failing step adds at least S/16, so after 16 steps r >= 2S: the
# search (fuel 64) returns a passing r with (65/64) S <= r <= U.


# dyadic constants compared in K
def dle(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +a: S.D, +b: S.D, h: {KA.kle(~KI.dnum(), a, b) == True{} : Bool}) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, b)):
  %AP.hofd(~F, ~H, a) : O.le(~F, _, M.ofd(~F, b))
  %AP.hofd(~F, ~H, b) : O.le(~F, N.emap(KI.dnum(), F, H, a), _)
  KA.kle_ok(~KI.dnum(), ~F, ~H, a, b, h)

def dnn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +b: S.D, h: {KA.kle(~KI.dnum(), M.d0(), b) == True{} : Bool}) -> O.le(~F, O.zero(F), M.ofd(~F, b)):
  %Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F)) : O.le(~F, _, M.ofd(~F, b))
  dle(~F, ~H, M.d0(), b, h)

def one_le(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +b: S.D, h: {KA.kle(~KI.dnum(), M.d1(), b) == True{} : Bool}) -> O.le(~F, O.one(F), M.ofd(~F, b)):
  %Equal.sym(O.C(F), O.one(F), M.ofd(~F, M.d1()), DM.ofd_one(~F)) : O.le(~F, _, M.ofd(~F, b))
  dle(~F, ~H, M.d1(), b, h)

def c17_eq(~F: O.OField) -> {M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}) == O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})) : O.C(F)}:
  FO.eq_of_sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))), O.add(F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(4n))))), FO.cert1(~F, O.sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))), O.add(F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))))), O.one(F), O.sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))], E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}}, E.ZVar{0n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(4n))))

def n16_eq(~F: O.OField) -> {O.mul(F, FR.ofn(~F, 16n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})) == O.one(F) : O.C(F)}:
  FO.eq_of_sub(~F, O.mul(F, O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.zero(F))))))))))))))))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(4n))))), O.one(F), FO.cert1(~F, O.sub(~F, O.mul(F, O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, O.one(F), O.zero(F))))))))))))))))), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(4n))))), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}), O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(4n)))], E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Z0{}}}}}}}}}}}}}}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(4n))))

def c65_le(~F: O.OField, ~H: N.Emb<KI.dnum(), F>) -> O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}))):
  %Equal.sym(O.C(F), O.add(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), M.ofd(~F, S.D.add(S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), DM.ofd_add(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})) : O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), _)
  dle(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}, S.D.add(S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), {==})

def c65_nn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>) -> O.le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})):
  DM.le_trans(~F, O.zero(F), O.one(F), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), FO.one_nn(~F), one_le(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}, {==}))

def qq_r(~F: O.OField, +x: O.C(F)) -> {O.mul(F, O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), x) == x : O.C(F)}:
  %Equal.sym(O.C(F), O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), O.one(F), half_two(~F)) : {O.mul(F, _, x) == x : O.C(F)}
  FR.fring_eq(~F, [x], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})

# S + S <= R gives S <= R/2, and R/2 < S gives R <= S + S
def half_le(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +s: O.C(F), +R: O.C(F), +h: O.le(~F, O.add(F, s, s), R)) -> O.le(~F, s, O.mul(F, M.ofd(~F, NU.half()), R)):
  %qq_r(~F, s) : O.le(~F, _, O.mul(F, M.ofd(~F, NU.half()), R))
  FV.le_of_sub(~F, O.mul(F, O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), s), O.mul(F, M.ofd(~F, NU.half()), R), FM.nn_eq(~F, O.sub(~F, O.mul(F, M.ofd(~F, NU.half()), R), O.mul(F, O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), s)), O.mul(F, M.ofd(~F, NU.half()), O.sub(~F, R, O.add(F, s, s))), FR.fring_eq(~F, [M.ofd(~F, NU.half()), s, R], E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{2n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{1n}}}, {==}), FO.mul_nonneg(~F, M.ofd(~F, NU.half()), O.sub(~F, R, O.add(F, s, s)), dnn(~F, ~H, NU.half(), {==}), FM.sub_nonneg(~F, O.add(F, s, s), R, h))))

def lt2(~F: O.OField, +s: O.C(F), +R: O.C(F), +g: O.lt(F, O.mul(F, M.ofd(~F, NU.half()), R), s)) -> O.le(~F, R, O.add(F, s, s)):
  %qq_r(~F, R) : O.le(~F, _, O.add(F, s, s))
  FV.le_of_sub(~F, O.mul(F, O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), R), O.add(F, s, s), FM.nn_eq(~F, O.sub(~F, O.add(F, s, s), O.mul(F, O.add(F, M.ofd(~F, NU.half()), M.ofd(~F, NU.half())), R)), O.add(F, O.sub(~F, s, O.mul(F, M.ofd(~F, NU.half()), R)), O.sub(~F, s, O.mul(F, M.ofd(~F, NU.half()), R))), FR.fring_eq(~F, [M.ofd(~F, NU.half()), s, R], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, s, O.mul(F, M.ofd(~F, NU.half()), R)), O.sub(~F, s, O.mul(F, M.ofd(~F, NU.half()), R)), FM.sub_nonneg(~F, O.mul(F, M.ofd(~F, NU.half()), R), s, FO.lt_le(~F, O.mul(F, M.ofd(~F, NU.half()), R), s, g)), FM.sub_nonneg(~F, O.mul(F, M.ofd(~F, NU.half()), R), s, FO.lt_le(~F, O.mul(F, M.ofd(~F, NU.half()), R), s, g)))))

# a c rounded up at 8 bits: between a c and a c (1 + 2^-7), for a, c >= 0
def dsig_lo(~F: O.OField, +a: S.D, +c: S.D) -> O.le(~F, O.mul(F, M.ofd(~F, a), M.ofd(~F, c)), M.ofd(~F, NU.dsigup(S.D.mul(a, c), 8n))):
  %Equal.sym(O.C(F), O.mul(F, M.ofd(~F, a), M.ofd(~F, c)), M.ofd(~F, S.D.mul(a, c)), DM.ofd_mul(~F, a, c)) : O.le(~F, _, M.ofd(~F, NU.dsigup(S.D.mul(a, c), 8n)))
  AP.both_l(O.le(~F, M.ofd(~F, S.D.mul(a, c)), M.ofd(~F, NU.dsigup(S.D.mul(a, c), 8n))), O.le(~F, O.sub(~F, M.ofd(~F, NU.dsigup(S.D.mul(a, c), 8n)), M.ofd(~F, S.D.mul(a, c))), O.mul(F, M.ofd(~F, M.dabs(S.D.mul(a, c))), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), RP.dsigup_ok(~F, S.D.mul(a, c), 8n))

def dmul_nn(~F: O.OField, +a: S.D, +c: S.D, +ha: O.le(~F, O.zero(F), M.ofd(~F, a)), +hc: O.le(~F, O.zero(F), M.ofd(~F, c))) -> O.le(~F, O.zero(F), M.ofd(~F, S.D.mul(a, c))):
  %DM.ofd_mul(~F, a, c) : O.le(~F, O.zero(F), _)
  FO.mul_nonneg(~F, M.ofd(~F, a), M.ofd(~F, c), ha, hc)

def dsig_hi(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +a: S.D, +c: S.D, +ha: O.le(~F, O.zero(F), M.ofd(~F, a)), +hc: O.le(~F, O.zero(F), M.ofd(~F, c))) -> O.le(~F, M.ofd(~F, NU.dsigup(S.D.mul(a, c), 8n)), O.mul(F, O.mul(F, M.ofd(~F, a), M.ofd(~F, c)), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})))):
  +x = S.D.mul(a, c)
  +hx = dmul_nn(~F, a, c, ha, hc)
  %Equal.sym(O.C(F), O.mul(F, M.ofd(~F, a), M.ofd(~F, c)), M.ofd(~F, x), DM.ofd_mul(~F, a, c)) : O.le(~F, M.ofd(~F, NU.dsigup(x, 8n)), O.mul(F, _, O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))))
  FV.le_of_sub(~F, M.ofd(~F, NU.dsigup(x, 8n)), O.mul(F, M.ofd(~F, x), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), FM.nn_eq(~F, O.sub(~F, O.mul(F, M.ofd(~F, x), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), M.ofd(~F, NU.dsigup(x, 8n))), O.sub(~F, O.mul(F, M.ofd(~F, x), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), O.sub(~F, M.ofd(~F, NU.dsigup(x, 8n)), M.ofd(~F, x))),
    FR.fring_eq(~F, [M.ofd(~F, x), M.ofd(~F, NU.dsigup(x, 8n)), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}, E.ZVar{1n}}, {==}),
    FM.sub_nonneg(~F, O.sub(~F, M.ofd(~F, NU.dsigup(x, 8n)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, x), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})),
      DM.le_trans(~F, O.sub(~F, M.ofd(~F, NU.dsigup(x, 8n)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), O.mul(F, M.ofd(~F, x), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})),
        AP.both_r(O.le(~F, M.ofd(~F, x), M.ofd(~F, NU.dsigup(x, 8n))), O.le(~F, O.sub(~F, M.ofd(~F, NU.dsigup(x, 8n)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), RP.dsigup_ok(~F, x, 8n)),
        FV.mul_le_r(~F, M.ofd(~F, M.dabs(x)), M.ofd(~F, x), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), dnn(~F, ~H, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}, {==}), DG.dabs_le(~F, x, M.ofd(~F, x), FV.bnd_self(~F, M.ofd(~F, x), hx)))))))

# the next radius is at least r (1 + 1/16)
def grow_lo(~F: O.OField, +r: S.D) -> O.le(~F, O.mul(F, M.ofd(~F, r), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}))), M.ofd(~F, NU.grow(r))):
  %c17_eq(~F) : O.le(~F, O.mul(F, M.ofd(~F, r), _), M.ofd(~F, NU.grow(r)))
  dsig_lo(~F, r, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})

def s_le_sc(~F: O.OField, +x: O.C(F), +c: O.C(F), +hx: O.le(~F, O.zero(F), x), +hc: O.le(~F, O.one(F), c)) -> O.le(~F, x, O.mul(F, x, c)):
  FV.le_of_sub(~F, x, O.mul(F, x, c), FM.nn_eq(~F, O.sub(~F, O.mul(F, x, c), x), O.mul(F, x, O.sub(~F, c, O.one(F))), FR.fring_eq(~F, [x, c], E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}, {==}), FO.mul_nonneg(~F, x, O.sub(~F, c, O.one(F)), hx, FM.sub_nonneg(~F, O.one(F), c, hc))))

def r_le(~F: O.OField, +x: O.C(F), +t: O.C(F), +hx: O.le(~F, O.zero(F), x), +ht: O.le(~F, O.zero(F), t)) -> O.le(~F, x, O.mul(F, x, O.add(F, O.one(F), t))):
  FV.le_of_sub(~F, x, O.mul(F, x, O.add(F, O.one(F), t)), FM.nn_eq(~F, O.sub(~F, O.mul(F, x, O.add(F, O.one(F), t)), x), O.mul(F, x, t), FR.fring_eq(~F, [x, t], E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}}, E.ZVar{0n}}, {==}), FO.mul_nonneg(~F, x, t, hx, ht)))

# one failing step: S + S <= R + (1 + o) S/16 gives S + S <= G + o S/16
def step_inv(~F: O.OField, +G: O.C(F), +R: O.C(F), +s: O.C(F), +t: O.C(F), +o: O.C(F), +hG: O.le(~F, O.mul(F, R, O.add(F, O.one(F), t)), G), +hinv: O.le(~F, O.add(F, s, s), O.add(F, R, O.mul(F, O.mul(F, O.add(F, O.one(F), o), t), s))), +hRS: O.le(~F, s, R), +ht: O.le(~F, O.zero(F), t)) -> O.le(~F, O.add(F, s, s), O.add(F, G, O.mul(F, O.mul(F, o, t), s))):
  FV.le_of_sub(~F, O.add(F, s, s), O.add(F, G, O.mul(F, O.mul(F, o, t), s)), FM.nn_eq(~F, O.sub(~F, O.add(F, G, O.mul(F, O.mul(F, o, t), s)), O.add(F, s, s)), O.add(F, O.add(F, O.sub(~F, G, O.mul(F, R, O.add(F, O.one(F), t))), O.sub(~F, O.add(F, R, O.mul(F, O.mul(F, O.add(F, O.one(F), o), t), s)), O.add(F, s, s))), O.mul(F, t, O.sub(~F, R, s))),
    FR.fring_eq(~F, [G, R, s, t, o], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{4n}}, E.ZVar{3n}}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.sub(~F, G, O.mul(F, R, O.add(F, O.one(F), t))), O.sub(~F, O.add(F, R, O.mul(F, O.mul(F, O.add(F, O.one(F), o), t), s)), O.add(F, s, s))), O.mul(F, t, O.sub(~F, R, s)), FO.nonneg_add(~F, O.sub(~F, G, O.mul(F, R, O.add(F, O.one(F), t))), O.sub(~F, O.add(F, R, O.mul(F, O.mul(F, O.add(F, O.one(F), o), t), s)), O.add(F, s, s)), FM.sub_nonneg(~F, O.mul(F, R, O.add(F, O.one(F), t)), G, hG), FM.sub_nonneg(~F, O.add(F, s, s), O.add(F, R, O.mul(F, O.mul(F, O.add(F, O.one(F), o), t), s)), hinv)), FO.mul_nonneg(~F, t, O.sub(~F, R, s), ht, FM.sub_nonneg(~F, s, R, hRS)))))

# R <= S + S keeps the next radius below U
def ub_step(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +R: O.C(F), +s: O.C(F), +h: O.le(~F, R, O.add(F, s, s))) -> O.le(~F, O.mul(F, O.mul(F, R, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s))):
  FV.le_of_sub(~F, O.mul(F, O.mul(F, R, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s)), O.mul(F, O.mul(F, R, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.sub(~F, O.add(F, s, s), R)),
    FR.fring_eq(~F, [R, s, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})], E.ZMul{E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}}, {==}),
    FO.mul_nonneg(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.sub(~F, O.add(F, s, s), R), FO.mul_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), dnn(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, {==}), FO.nonneg_add(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), FO.one_nn(~F), dnn(~F, ~H, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}, {==}))), FM.sub_nonneg(~F, R, O.add(F, s, s), h))))

# r0 is below U
def ub0(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +s: O.C(F), +hs: O.le(~F, O.zero(F), s)) -> O.le(~F, O.mul(F, O.mul(F, s, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s))):
  FV.le_of_sub(~F, O.mul(F, O.mul(F, s, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, s, s)), O.mul(F, O.mul(F, s, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})))), O.mul(F, O.mul(F, O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), s), O.sub(~F, O.add(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}))),
    FR.fring_eq(~F, [s, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})], E.ZMul{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}, E.ZVar{0n}}, E.ZSub{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}}}, {==}),
    FO.mul_nonneg(~F, O.mul(F, O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), s), O.sub(~F, O.add(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), FO.mul_nonneg(~F, O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n})), s, FO.nonneg_add(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}), FO.one_nn(~F), dnn(~F, ~H, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}, {==})), hs), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), c65_le(~F, ~H)))))

def rgood(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, m: Maybe<&2, S.D>) -> Data:
  match m:
    case None{}:
      Empty
    case Some{+r}:
      M.Both({NU.okr(eqs, n, yc, r, ym, pc, pr) == True{} : Bool}, M.Both(O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r)), O.le(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))))))


def r_nn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb), +r: S.D, +hlo: O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r))) -> O.le(~F, O.zero(F), M.ofd(~F, r)):
  DM.le_trans(~F, O.zero(F), O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r), FO.mul_nonneg(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), dvmax_nn(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), c65_nn(~F, ~H)), hlo)

# a radius that passes the window but failed: impossible
def no_fail(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb), +r: S.D, +eok: {NU.okr(eqs, n, yc, r, ym, pc, pr) == False{} : Bool}, +hlo: O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r)), +hhi: O.le(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))))), hS: O.le(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)))) -> Empty:
  KA.ft(Equal.trans(Bool, False{}, NU.okr(eqs, n, yc, r, ym, pc, pr), True{}, Equal.sym(Bool, NU.okr(eqs, n, yc, r, ym, pc, pr), False{}, eok), window_ok(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, r, r_nn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, hlo), DM.le_trans(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb, hhi, hU), hS)))

def fail_lt.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb), +r: S.D, +eok: {NU.okr(eqs, n, yc, r, ym, pc, pr) == False{} : Bool}, +hlo: O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r)), +hhi: O.le(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))))), t: Or(O.lt(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r))), Or({M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))) == O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)) : O.C(F)}, O.lt(F, O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))))) -> O.lt(F, O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))):
  match t:
    case Inl{l}:
      FO.absurd(O.lt(F, O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), no_fail(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi, Inl{l}))
    case Inr{Inl{e}}:
      FO.absurd(O.lt(F, O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), no_fail(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi, Inr{e}))
    case Inr{Inr{+g}}:
      g

# a failing radius is at most S + S
def fail_le(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb), +r: S.D, +eok: {NU.okr(eqs, n, yc, r, ym, pc, pr) == False{} : Bool}, +hlo: O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r)), +hhi: O.le(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))))) -> O.le(~F, M.ofd(~F, r), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))):
  lt2(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, r), fail_lt.go(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi, O.lt_total(F)(M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.half()), M.ofd(~F, r)))))


# the search from r with fuel k, m steps (m <= k) from certain success
def rs_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, k: Nat, ok: Bool, m: Nat, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb), +r: S.D, eok: {NU.okr(eqs, n, yc, r, ym, pc, pr) == ok : Bool}, +hlo: O.le(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r)), +hhi: O.le(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))))), hm: {KA.natle(m, k) == True{} : Bool}, hinv: O.le(~F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), O.add(F, M.ofd(~F, r), O.mul(F, O.mul(F, FR.ofn(~F, m), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))))) -> rgood(~F, ~H, n, eqs, yc, pc, pr, ym, NU.rsearch(k, ok, eqs, n, yc, r, ym, pc, pr)):
  match k ok m:
    case 0n True{} m:
      (eok, (hlo, hhi))
    case 1n+j True{} m:
      (eok, (hlo, hhi))
    case 0n False{} 0n:
      FO.absurd(rgood(~F, ~H, n, eqs, yc, pc, pr, ym, NU.rsearch(0n, False{}, eqs, n, yc, r, ym, pc, pr)), no_fail(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi, half_le(~F, ~H, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, r), FV.le_rw_r(~F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), O.add(F, M.ofd(~F, r), O.mul(F, O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), M.ofd(~F, r), FR.fring_eq(~F, [M.ofd(~F, r), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZVar{0n}, {==}), hinv))))
    case 0n False{} 1n+mm:
      FO.absurd(rgood(~F, ~H, n, eqs, yc, pc, pr, ym, NU.rsearch(0n, False{}, eqs, n, yc, r, ym, pc, pr)), KA.ft(hm))
    case 1n+j False{} 0n:
      FO.absurd(rgood(~F, ~H, n, eqs, yc, pc, pr, ym, NU.rsearch(1n+j, False{}, eqs, n, yc, r, ym, pc, pr)), no_fail(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi, half_le(~F, ~H, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, r), FV.le_rw_r(~F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), O.add(F, M.ofd(~F, r), O.mul(F, O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), M.ofd(~F, r), FR.fring_eq(~F, [M.ofd(~F, r), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZVar{0n}, {==}), hinv))))
    case 1n++j False{} 1n++mm:
      +R = M.ofd(~F, r)
      +G = M.ofd(~F, NU.grow(r))
      +hR0 = r_nn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, hlo)
      +hG = grow_lo(~F, r)
      +hRS = DM.le_trans(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), R, s_le_sc(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), dvmax_nn(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), one_le(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}, {==})), hlo)
      +hlo2 = DM.le_trans(~F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), R, G, hlo, DM.le_trans(~F, R, O.mul(F, R, O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}))), G, r_le(~F, R, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}), hR0, dnn(~F, ~H, S.D{S.Zpos{S.XH{}}, 4n}, {==})), hG))
      +hhi2 = DM.le_trans(~F, G, O.mul(F, O.mul(F, R, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), dsig_hi(~F, ~H, r, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, hR0, dnn(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}, {==})), ub_step(~F, ~H, R, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), fail_le(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, eok, hlo, hhi)))
      rs_ok(~F, ~H, j, NU.okr(eqs, n, yc, NU.grow(r), ym, pc, pr), mm, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, NU.grow(r), {==}, hlo2, hhi2, hm, step_inv(~F, G, R, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n}), FR.ofn(~F, mm), hG, hinv, hRS, dnn(~F, ~H, S.D{S.Zpos{S.XH{}}, 4n}, {==})))

# the solver's search from r0 returns a passing radius between (65/64) S and U
def rs_init(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +lpp: {KA.klen(~KI.dnum(), pc) == KA.klen(~KI.dnum(), pr) : Nat}, +ym: List<&2, List<&2, S.D>>, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +rb: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hrb: O.le(~F, O.zero(F), rb), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hc: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rb)), +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rb), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +hym: {CK.mlen(~KI.dnum(), ym) == n : Nat}, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +thR: O.C(F), +hthr0: O.le(~F, O.zero(F), thR), +hthr: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), M.ofdm(~F, ym)))), n), thR), +hthr1: O.lt(F, thR, O.one(F)), +hw: O.le(~F, O.add(F, O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)))), O.mul(F, yn, O.mul(F, FR.ofn(~F, KA.klen(~KI.dnum(), pc)), O.mul(F, lam, rb)))), M.ofd(~F, NU.half())), +hU: O.le(~F, O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), rb)) -> rgood(~F, ~H, n, eqs, yc, pc, pr, ym, NU.rsearch(64n, NU.okr(eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr), ym, pc, pr), eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr), ym, pc, pr)):
  +r = NU.r0(eqs, n, yc, ym, pc, pr)
  +hS0 = dvmax_nn(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))
  +hlo = dsig_lo(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})
  +hRS = DM.le_trans(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), M.ofd(~F, r), s_le_sc(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), hS0, one_le(~F, ~H, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}, {==})), hlo)
  rs_ok(~F, ~H, 64n, NU.okr(eqs, n, yc, r, ym, pc, pr), 16n, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, hym, hab, thR, hthr0, hthr, hthr1, hw, hU, r, {==}, hlo,
    DM.le_trans(~F, M.ofd(~F, r), O.mul(F, O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.mul(F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), O.add(F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, 8n}))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), dsig_hi(~F, ~H, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}, hS0, c65_nn(~F, ~H)), ub0(~F, ~H, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), hS0)),
    {==},
    (%Equal.sym(O.C(F), O.mul(F, FR.ofn(~F, 16n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 4n})), O.one(F), n16_eq(~F)) : O.le(~F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), O.add(F, M.ofd(~F, r), O.mul(F, _, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))))
      FV.le_of_sub(~F, O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), O.add(F, M.ofd(~F, r), O.mul(F, O.one(F), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), FM.nn_eq(~F, O.sub(~F, O.add(F, M.ofd(~F, r), O.mul(F, O.one(F), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))), O.sub(~F, M.ofd(~F, r), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))), FR.fring_eq(~F, [M.ofd(~F, r), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, {==}), FM.sub_nonneg(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, r), hRS)))))

# In the box
# ----------
# With e = yc - x_b and f(x_b ++ x_z) = 0, along the path
# yc ++ pc -> yc ++ x_z -> x_b ++ x_z: e = (e - Y S' e) + Y f(Z) with
# S' e = f(Z) (unknowns' slopes, parameters at x_z), and
# Y f(Z) = Y f(P) + Y (f(Z) - f(P)), the last over the radius-0 box (only
# the parameters move), so its entries are at most B(0)'s. Hence
# |e| <= S + |e - Y S' e| <= S + (thL + yn n lam rad) |e|, and |e| <= (65/64) S.

def vz_at(~F: O.OField, +v: M.Vec(~F), +n: Nat, +k: Nat) -> {O.lookup(~F, BX.vsub(~F, v, GJ.zeros(~F, n)), k) == O.lookup(~F, v, k) : O.C(F)}:
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, v, GJ.zeros(~F, n)), k), O.sub(~F, O.lookup(~F, v, k), O.lookup(~F, GJ.zeros(~F, n), k)), DG.look_diff(~F, v, GJ.zeros(~F, n), k)) : {_ == O.lookup(~F, v, k) : O.C(F)}
  %GJ.look_zeros(~F, n, k) : {O.sub(~F, O.lookup(~F, v, k), _) == O.lookup(~F, v, k) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, v, k)], E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})

def vsub_zeros(~F: O.OField, +v: M.Vec(~F), +n: Nat, +lv: {M.len(~F, v) == n : Nat}) -> {BX.vsub(~F, v, GJ.zeros(~F, n)) == v : M.Vec(~F)}:
  AP.vext(~F, ~BX.vsub(~F, v, GJ.zeros(~F, n)), ~v, ~(k => vz_at(~F, v, n, k)), n, CP.len_vsub(~F, v, GJ.zeros(~F, n), n, lv, GJ.len_zeros_eq(~F, n)), lv)

def rnn_at(~F: O.OField, r: M.Vec(~F), +k: Nat, h: FV.rnn(~F, r)) -> O.le(~F, O.zero(F), O.lookup(~F, r, k)):
  match r k:
    case Nil{} k:
      FO.le_refl(~F, O.zero(F))
    case Con{a, rs} 0n:
      (h1, h2) = h
      h1
    case Con{a, rs} 1n+j:
      (h1, h2) = h
      rnn_at(~F, rs, j, h2)

def bnd_z(~F: O.OField, +a: O.C(F), +s: O.C(F), ha: M.bnd(~F, a, O.zero(F)), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, a, s):
  FM.bnd_mono(~F, a, O.zero(F), s, ha, FM.nn_eq(~F, O.sub(~F, s, O.zero(F)), s, FR.fring_eq(~F, [s], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==}), hs))

# entry k of an entrywise bound
def rbnd_at(~F: O.OField, d: M.Vec(~F), +r: M.Vec(~F), +k: Nat, h: BX.rbnd(~F, d, r), hr: FV.rnn(~F, r)) -> M.bnd(~F, O.lookup(~F, d, k), O.lookup(~F, r, k)):
  match d r k:
    case Nil{} r k:
      bnd_z(~F, O.zero(F), O.lookup(~F, r, k), FV.bnd_self(~F, O.zero(F), FO.le_refl(~F, O.zero(F))), rnn_at(~F, r, k, hr))
    case Con{a, ds} Nil{} 0n:
      (h1, h2) = h
      h1
    case Con{a, ds} Nil{} 1n+j:
      (h1, h2) = h
      rbnd_at(~F, ds, Nil{}, j, h2, Unit{})
    case Con{a, ds} Con{s, rs} 0n:
      (h1, h2) = h
      h1
    case Con{a, ds} Con{s, rs} 1n+j:
      (h1, h2) = h
      (g1, g2) = hr
      rbnd_at(~F, ds, rs, j, h2, g2)

def bnd_add0(~F: O.OField, +a: O.C(F), +w: O.C(F), +s: O.C(F), ha: M.bnd(~F, a, O.zero(F)), hw: M.bnd(~F, w, s)) -> M.bnd(~F, O.add(F, a, w), s):
  %FR.fring_eq(~F, [s], E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{0n}, {==}) : M.bnd(~F, O.add(F, a, w), _)
  FM.bnd_add(~F, a, O.zero(F), w, s, ha, hw)

def rbnd_of_z(~F: O.OField, u: M.Vec(~F), r: M.Vec(~F), hu: M.vbnd.all(~F, u, O.zero(F)), hr: FV.rnn(~F, r)) -> BX.rbnd(~F, u, r):
  match u r:
    case Nil{} r:
      Unit{}
    case Con{a, us} Nil{}:
      (h1, h2) = hu
      (h1, rbnd_of_z(~F, us, Nil{}, h2, Unit{}))
    case Con{a, us} Con{s, rs}:
      (h1, h2) = hu
      (g1, g2) = hr
      (bnd_z(~F, a, s, h1, g1), rbnd_of_z(~F, us, rs, h2, g2))

# a vector of zeros (to within 0) added: the same bound
def rbnd_add0(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), r: M.Vec(~F), hu: M.vbnd.all(~F, u, O.zero(F)), hw: BX.rbnd(~F, w, r), hr: FV.rnn(~F, r)) -> BX.rbnd(~F, M.vadd(~F, u, w), r):
  match u w r:
    case Nil{} w r:
      hw
    case Con{+a, +us} Nil{} r:
      rbnd_of_z(~F, Con{a, us}, r, hu, hr)
    case Con{a, us} Con{b, ws} Nil{}:
      (h1, h2) = hu
      (k1, k2) = hw
      (bnd_add0(~F, a, b, O.zero(F), h1, k1), rbnd_add0(~F, us, ws, Nil{}, h2, k2, Unit{}))
    case Con{a, us} Con{b, ws} Con{s, rs}:
      (h1, h2) = hu
      (k1, k2) = hw
      (g1, g2) = hr
      (bnd_add0(~F, a, b, s, h1, k1), rbnd_add0(~F, us, ws, rs, h2, k2, g2))

# |ek| <= S + D, from |ek - yz| <= D, |yz - yp| <= b, |yp| <= a, a + b + g <= S, |g| <= gb <= 0
def in_ent(~F: O.OField, +ek: O.C(F), +yz: O.C(F), +yp: O.C(F), +a: O.C(F), +b: O.C(F), +g: O.C(F), +s: O.C(F), +dd: O.C(F), +gb: O.C(F), hq: M.bnd(~F, O.sub(~F, ek, yz), dd), ht: M.bnd(~F, O.sub(~F, yz, yp), b), ha: M.bnd(~F, yp, a), +hs: O.le(~F, O.add(F, O.add(F, a, b), g), s), +hg: M.bnd(~F, g, gb), +hgb: O.le(~F, gb, O.zero(F))) -> M.bnd(~F, ek, O.add(F, s, dd)):
  (q1, q2) = hq
  (t1, t2) = ht
  (a1, a2) = ha
  +g2 = AP.both_r(O.le(~F, O.zero(F), O.sub(~F, gb, g)), O.le(~F, O.zero(F), O.add(F, gb, g)), hg)
  +hs2 = FM.sub_nonneg(~F, O.add(F, O.add(F, a, b), g), s, hs)
  +hgb2 = FM.sub_nonneg(~F, gb, O.zero(F), hgb)
  (FM.nn_eq(~F, O.sub(~F, O.add(F, s, dd), ek), O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp))), O.sub(~F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g)), O.sub(~F, O.zero(F), gb)),
     FR.fring_eq(~F, [ek, yz, yp, a, b, g, s, dd, gb], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{7n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{4n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{6n}, E.ZAdd{E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{5n}}}}, E.ZAdd{E.ZVar{8n}, E.ZVar{5n}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{8n}}}, E.ZSub{E.ZAdd{E.ZVar{6n}, E.ZVar{7n}}, E.ZVar{0n}}, {==}),
     FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.add(F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp))), O.sub(~F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g)), O.sub(~F, O.zero(F), gb), FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp))), O.sub(~F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g), FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp))), O.sub(~F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g)), FO.nonneg_add(~F, O.add(F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp))), O.sub(~F, a, yp), FO.nonneg_add(~F, O.sub(~F, dd, O.sub(~F, ek, yz)), O.sub(~F, b, O.sub(~F, yz, yp)), q1, t1), a1), hs2), g2), hgb2)),
   FM.nn_eq(~F, O.add(F, O.add(F, s, dd), ek), O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp))), O.add(F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g)), O.sub(~F, O.zero(F), gb)),
     FR.fring_eq(~F, [ek, yz, yp, a, b, g, s, dd, gb], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{7n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZVar{4n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZAdd{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{6n}, E.ZAdd{E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{5n}}}}, E.ZAdd{E.ZVar{8n}, E.ZVar{5n}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{8n}}}, E.ZAdd{E.ZAdd{E.ZVar{6n}, E.ZVar{7n}}, E.ZVar{0n}}, {==}),
     FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.add(F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp))), O.add(F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g)), O.sub(~F, O.zero(F), gb), FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp))), O.add(F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g))), O.add(F, gb, g), FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp))), O.add(F, a, yp)), O.sub(~F, s, O.add(F, O.add(F, a, b), g)), FO.nonneg_add(~F, O.add(F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp))), O.add(F, a, yp), FO.nonneg_add(~F, O.add(F, dd, O.sub(~F, ek, yz)), O.add(F, b, O.sub(~F, yz, yp)), q2, t2), a2), hs2), g2), hgb2)))

# E <= S + D, D <= (thL + yn nl) E and c65 (thL + yn nl) <= c65 - 1 give E <= S c65
def in_fin(~F: O.OField, +ee: O.C(F), +s: O.C(F), +dd: O.C(F), +thL: O.C(F), +yn: O.C(F), +nl: O.C(F), +c65: O.C(F), +hE: O.le(~F, ee, O.add(F, s, dd)), +hD: O.le(~F, dd, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee)))), +hk: O.le(~F, O.mul(F, c65, O.add(F, thL, O.mul(F, yn, nl))), O.sub(~F, c65, O.one(F))), +hc0: O.le(~F, O.zero(F), c65), +hE0: O.le(~F, O.zero(F), ee)) -> O.le(~F, ee, O.mul(F, s, c65)):
  FV.le_of_sub(~F, ee, O.mul(F, s, c65), FM.nn_eq(~F, O.sub(~F, O.mul(F, s, c65), ee), O.add(F, O.add(F, O.mul(F, c65, O.sub(~F, O.add(F, s, dd), ee)), O.mul(F, c65, O.sub(~F, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee))), dd))), O.mul(F, O.sub(~F, O.sub(~F, c65, O.one(F)), O.mul(F, c65, O.add(F, thL, O.mul(F, yn, nl)))), ee)),
    FR.fring_eq(~F, [ee, s, dd, thL, yn, nl, c65], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{0n}}}, E.ZMul{E.ZVar{6n}, E.ZSub{E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZVar{0n}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{5n}, E.ZVar{0n}}}}, E.ZVar{2n}}}}, E.ZMul{E.ZSub{E.ZSub{E.ZVar{6n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{6n}, E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{6n}}, E.ZVar{0n}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.mul(F, c65, O.sub(~F, O.add(F, s, dd), ee)), O.mul(F, c65, O.sub(~F, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee))), dd))), O.mul(F, O.sub(~F, O.sub(~F, c65, O.one(F)), O.mul(F, c65, O.add(F, thL, O.mul(F, yn, nl)))), ee),
      FO.nonneg_add(~F, O.mul(F, c65, O.sub(~F, O.add(F, s, dd), ee)), O.mul(F, c65, O.sub(~F, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee))), dd)), FO.mul_nonneg(~F, c65, O.sub(~F, O.add(F, s, dd), ee), hc0, FM.sub_nonneg(~F, ee, O.add(F, s, dd), hE)), FO.mul_nonneg(~F, c65, O.sub(~F, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee))), dd), hc0, FM.sub_nonneg(~F, dd, O.add(F, O.mul(F, thL, ee), O.mul(F, yn, O.mul(F, nl, ee))), hD))),
      FO.mul_nonneg(~F, O.sub(~F, O.sub(~F, c65, O.one(F)), O.mul(F, c65, O.add(F, thL, O.mul(F, yn, nl)))), ee, FM.sub_nonneg(~F, O.mul(F, c65, O.add(F, thL, O.mul(F, yn, nl))), O.sub(~F, c65, O.one(F)), hk), hE0))))


def lyc_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}) -> {M.len(~F, M.ofdv(~F, yc)) == n : Nat}:
  Equal.trans(Nat, M.len(~F, M.ofdv(~F, yc)), KA.klen(~KI.dnum(), yc), n, Equal.sym(Nat, KA.klen(~KI.dnum(), yc), M.len(~F, M.ofdv(~F, yc)), klen_d(~F, ~H, yc)), lyc)

def fit_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}) -> {C.fit(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc)) == M.ofdv(~F, yc) : M.Vec(~F)}:
  Equal.trans(M.Vec(~F), C.fit(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc)), N.ofkv(~KI.dnum(), ~F, ~H, yc), M.ofdv(~F, yc), FV.fit_len(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc), Equal.trans(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, yc)), KA.klen(~KI.dnum(), yc), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, yc), lyc)), AP.ofkv_d(~F, ~H, yc))

# a point with unknowns yc and parameters in the balls lies in the radius-0 box
def inb_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +z: M.Vec(~F), +hz: BX.rbnd(~F, BX.vsub(~F, z, N.ofkv(~KI.dnum(), ~F, ~H, pc)), N.ofkv(~KI.dnum(), ~F, ~H, pr)), +hnp: FV.rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, pr))) -> KB.inbox(~KI.dnum(), ~F, ~H, C.app(~F, M.ofdv(~F, yc), z), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr)):
  %fit_d(~F, ~H, n, yc, lyc) : KB.inbox(~KI.dnum(), ~F, ~H, C.app(~F, _, z), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr))
  CP.box_in(~KI.dnum(), ~F, ~H, n, N.ofkv(~KI.dnum(), ~F, ~H, yc), z, yc, Nil{}, pc, pr, FV.rbnd_self(~F, N.ofkv(~KI.dnum(), ~F, ~H, yc), N.ofkv(~KI.dnum(), ~F, ~H, Nil{}), Unit{}), Equal.trans(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, yc)), KA.klen(~KI.dnum(), yc), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, yc), lyc), lyc, Unit{}, hz, hnp)

def zr_k(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +xz: M.Vec(~F), +pc: List<&2, S.D>, +pr: List<&2, S.D>, +h: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), N.ofkv(~KI.dnum(), ~F, ~H, pr)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, pr), M.ofdv(~F, pr), AP.ofkv_d(~F, ~H, pr)) : BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), _)
  h

def zr_kk(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +xz: M.Vec(~F), +pc: List<&2, S.D>, +pr: List<&2, S.D>, +h: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> BX.rbnd(~F, BX.vsub(~F, xz, N.ofkv(~KI.dnum(), ~F, ~H, pc)), N.ofkv(~KI.dnum(), ~F, ~H, pr)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, pc), M.ofdv(~F, pc), AP.ofkv_d(~F, ~H, pc)) : BX.rbnd(~F, BX.vsub(~F, xz, _), N.ofkv(~KI.dnum(), ~F, ~H, pr))
  zr_k(~F, ~H, xz, pc, pr, h)

def zr_p(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hnp: FV.rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, pr))) -> BX.rbnd(~F, BX.vsub(~F, M.ofdv(~F, pc), N.ofkv(~KI.dnum(), ~F, ~H, pc)), N.ofkv(~KI.dnum(), ~F, ~H, pr)):
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, pc), M.ofdv(~F, pc), AP.ofkv_d(~F, ~H, pc)) : BX.rbnd(~F, BX.vsub(~F, M.ofdv(~F, pc), _), N.ofkv(~KI.dnum(), ~F, ~H, pr))
  FV.rbnd_self(~F, M.ofdv(~F, pc), N.ofkv(~KI.dnum(), ~F, ~H, pr), hnp)


# the unknowns' slopes at x_z carry e to f(Z)
def se_eq(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> {M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)) == C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)) : M.Vec(~F)}:
  %CP.fvecs_con(~F, M.ofdv(~F, yc), xb, xz, eqs, n, KA.klen(~KI.dnum(), pc), hab, lyc_d(~F, ~H, n, yc, lyc), lxb) : {_ == C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), C.fvals(~F, eqs, C.app(~F, xb, xz)), GJ.zeros(~F, n), hz) : {BX.vsub(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), _) == C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)) : M.Vec(~F)}
  vsub_zeros(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), n, Equal.trans(Nat, M.len(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz))), CK.eqlen(eqs), n, CP.len_fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), hn))

# |Y f(P)| entrywise is the checker's first term
def yf_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym))):
  %fit_d(~F, ~H, n, yc, lyc) : BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, _, M.ofdv(~F, pc)))), N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)))
  %AP.ofkv_d(~F, ~H, pc) : BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, C.fit(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc)), _))), N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)))
  FV.rbnd_rw(~F, N.ofkv(~KI.dnum(), ~F, ~H, KA.kmatvec(~KI.dnum(), ym, CK.kvals(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), eqs))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, C.fit(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc)), N.ofkv(~KI.dnum(), ~F, ~H, pc)))), N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)),
    Equal.sym(M.Vec(~F), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, C.fit(~F, n, N.ofkv(~KI.dnum(), ~F, ~H, yc)), N.ofkv(~KI.dnum(), ~F, ~H, pc)))), N.ofkv(~KI.dnum(), ~F, ~H, KA.kmatvec(~KI.dnum(), ym, CK.kvals(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), eqs))), CP.yft_ok(~KI.dnum(), ~F, ~H, eqs, n, yc, ym, pc, hh, Equal.trans(Nat, M.len(~F, N.ofkv(~KI.dnum(), ~F, ~H, yc)), KA.klen(~KI.dnum(), yc), n, CP.len_ofkv(~KI.dnum(), ~F, ~H, yc), lyc))),
    KA.kvabs_bnd(~KI.dnum(), ~F, ~H, KA.kmatvec(~KI.dnum(), ym, CK.kvals(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), eqs))))

def b0_nn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> FV.rnn(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}))):
  +inP = inb_d(~F, ~H, n, yc, pc, pr, lyc, M.ofdv(~F, pc), zr_p(~F, ~H, pc, pr, rnn_kv(~F, ~H, pr, hpn)), rnn_kv(~F, ~H, pr, hpn))
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr))), bf_eq(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})) : FV.rnn(~F, _)
  FV.matvec_nonneg(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr)), KA.kmabs_nn(~KI.dnum(), ~F, ~H, ym), FV.matvec_nonneg(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), N.ofkv(~KI.dnum(), ~F, ~H, pr), CP.mat_nnz(~KI.dnum(), ~F, ~H, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), eqs, KA.klen(~KI.dnum(), pc), n, hh, inP, inP), rnn_kv(~F, ~H, pr, hpn)))

# the parameter step, over the radius-0 box: |Y (f(Z) - f(P))| <= B(0) entrywise
def bz_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), BX.vsub(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}))):
  +m = KA.klen(~KI.dnum(), pc)
  +pk = N.ofkv(~KI.dnum(), ~F, ~H, pr)
  +hpk = rnn_kv(~F, ~H, pr, hpn)
  +sy0 = CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), eqs, n, 0n)
  +sz0 = CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), eqs, m, n)
  +inZ = inb_d(~F, ~H, n, yc, pc, pr, lyc, xz, zr_kk(~F, ~H, xz, pc, pr, hzr), hpk)
  +inP = inb_d(~F, ~H, n, yc, pc, pr, lyc, M.ofdv(~F, pc), zr_p(~F, ~H, pc, pr, hpk), hpk)
  +hmzn = CP.mat_nnz(~KI.dnum(), ~F, ~H, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), eqs, m, n, hh, inZ, inP)
  +hW = FV.mbnd_matvec(~F, sz0, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), BX.vsub(~F, xz, M.ofdv(~F, pc)), pk, CP.mat_bndz(~KI.dnum(), ~F, ~H, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), eqs, m, n, hh, inZ, inP), zr_k(~F, ~H, xz, pc, pr, hzr), hmzn, hpk)
  +hA0 = vall_z(~F, M.matvec(~F, sy0, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc))), NP.mnorm(~F, sy0, M.len(~F, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc)))), NP.mv_le(~F, sy0, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc)), O.zero(F), NW.vall_self(~F, M.ofdv(~F, yc), O.zero(F), FO.le_refl(~F, O.zero(F))), FO.le_refl(~F, O.zero(F))))
  +hAW = rbnd_add0(~F, M.matvec(~F, sy0, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc))), M.matvec(~F, sz0, BX.vsub(~F, xz, M.ofdv(~F, pc))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk), hA0, hW, FV.matvec_nonneg(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk, hmzn, hpk))
  %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk)), bf_eq(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})) : BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), BX.vsub(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), _)
  %Equal.sym(M.Vec(~F), BX.vsub(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), M.vadd(~F, M.matvec(~F, sy0, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc))), M.matvec(~F, sz0, BX.vsub(~F, xz, M.ofdv(~F, pc)))), CP.fvecs_self(~F, M.ofdv(~F, yc), M.ofdv(~F, yc), xz, M.ofdv(~F, pc), eqs, n, m, hab, lyc_d(~F, ~H, n, yc, lyc), lyc_d(~F, ~H, n, yc, lyc))) : BX.rbnd(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), _), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk)))
  FV.mbnd_matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), M.vadd(~F, M.matvec(~F, sy0, BX.vsub(~F, M.ofdv(~F, yc), M.ofdv(~F, yc))), M.matvec(~F, sz0, BX.vsub(~F, xz, M.ofdv(~F, pc)))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk), KA.kmabs_bnd(~KI.dnum(), ~F, ~H, ym), hAW, KA.kmabs_nn(~KI.dnum(), ~F, ~H, ym), FV.matvec_nonneg(~F, N.ofkm(~KI.dnum(), ~F, ~H, mzm(~KI.dnum(), ~F, ~H, CK.box(~KI.dnum(), n, yc, Nil{}, pc, pr), KA.klen(~KI.dnum(), pc), n, eqs)), pk, hmzn, hpk))

def hq_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +k: Nat) -> M.bnd(~F, O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz))), k)), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))))):
  %se_eq(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr) : M.bnd(~F, O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), _), k)), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))))
  %DG.look_diff(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k) : M.bnd(~F, _, NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))))
  AP.lkb(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k)

def ht_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +k: Nat) -> M.bnd(~F, O.sub(~F, O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), k)), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k)):
  %DG.look_diff(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), k) : M.bnd(~F, _, O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k))
  %AP.mv_vsub(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))) : M.bnd(~F, O.lookup(~F, _, k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k))
  rbnd_at(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), BX.vsub(~F, C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz)), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k, bz_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr), b0_nn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr))

def hs_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +k: Nat) -> O.le(~F, O.add(F, O.add(F, O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k)), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), k)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)))):
  RL.le_rw_l(~F, O.lookup(~F, M.vadd(~F, M.vadd(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}))), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), k), O.add(F, O.add(F, O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k)), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), k)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), lk3(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), k),
    (%svec_f(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{}) : O.le(~F, O.lookup(~F, _, k), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))
      (%Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), M.ofdv(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), AP.ofkv_d(~F, ~H, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))) : O.le(~F, O.lookup(~F, _, k), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))))
        dvmax_at(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr), k))))

# entry k: |e_k| <= S + |e - Y S' e|
def in_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +k: Nat) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))))):
  in_ent(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), xz))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, bk(~F, ~H, n, eqs, yc, pc, pr, ym, Nil{})), k), O.lookup(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), k), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))), NP.vn(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))),
    hq_at(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, k), ht_at(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, k),
    rbnd_at(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), C.fvals(~F, eqs, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))), N.ofkv(~KI.dnum(), ~F, ~H, ayf(~F, ~H, n, eqs, yc, pc, pr, ym)), k, yf_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr), KA.kvabs_nn(~KI.dnum(), ~F, ~H, KA.kmatvec(~KI.dnum(), ym, CK.kvals(~KI.dnum(), KA.kapp(~KI.dnum(), yc, pc), eqs)))),
    hs_at(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, k), AP.lkb(~F, N.ofkv(~KI.dnum(), ~F, ~H, CK.gvec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), k), g0_bnd(~F, ~H, n, eqs, yc, pc, pr, ym))


# e - Y S' e = (e - Y Jc e) - Y (S' - Jc) e
def qv_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +k: Nat) -> {O.lookup(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k) == O.sub(~F, O.lookup(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : O.C(F)}:
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k), O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), DG.look_diff(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : {_ == O.sub(~F, O.lookup(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : O.C(F)}
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k), O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), DG.look_diff(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : {O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) == O.sub(~F, _, O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : O.C(F)}
  %Equal.sym(M.Vec(~F), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb)), BX.vsub(~F, M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), CP.sj_ok(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))) : {O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) == O.sub(~F, O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), _), k)) : O.C(F)}
  %Equal.sym(M.Vec(~F), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), BX.vsub(~F, M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), BX.vsub(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), AP.mv_vsub(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))) : {O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) == O.sub(~F, O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), O.lookup(~F, _, k)) : O.C(F)}
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), k), O.sub(~F, O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), DG.look_diff(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) : {O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)) == O.sub(~F, O.sub(~F, O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)), _) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))), k), O.lookup(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))), k)], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, {==})

def add_cong(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, ha: {a == a2 : Nat}, hb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %Equal.sym(Nat, a, a2, ha) : {Nat.add(_, b) == Nat.add(a2, b2) : Nat}
  %Equal.sym(Nat, b, b2, hb) : {Nat.add(a2, _) == Nat.add(a2, b2) : Nat}
  {==}

def lapp_eq(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +w1: M.Vec(~F), +w2: M.Vec(~F), h1: {M.len(~F, u1) == M.len(~F, u2) : Nat}, h2: {M.len(~F, w1) == M.len(~F, w2) : Nat}) -> {M.len(~F, C.app(~F, u1, w1)) == M.len(~F, C.app(~F, u2, w2)) : Nat}:
  Equal.trans(Nat, M.len(~F, C.app(~F, u1, w1)), Nat.add(M.len(~F, u1), M.len(~F, w1)), M.len(~F, C.app(~F, u2, w2)), NW.len_app(~F, u1, w1),
    Equal.trans(Nat, Nat.add(M.len(~F, u1), M.len(~F, w1)), Nat.add(M.len(~F, u2), M.len(~F, w2)), M.len(~F, C.app(~F, u2, w2)), add_cong(M.len(~F, u1), M.len(~F, u2), M.len(~F, w1), M.len(~F, w2), h1, h2), Equal.sym(Nat, M.len(~F, C.app(~F, u2, w2)), Nat.add(M.len(~F, u2), M.len(~F, w2)), NW.len_app(~F, u2, w2))))


def le_ee(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr))) -> {M.len(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)) == n : Nat}:
  CP.len_vsub(~F, M.ofdv(~F, yc), xb, n, lyc_d(~F, ~H, n, yc, lyc), lxb)

def vp_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hq: AP.eqok(~F, bb, lam, ms, eqs), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +rad: O.C(F), +hr0: O.le(~F, O.zero(F), rad), +hgb: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rad)), +hZr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad), +hBr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad)) -> O.le(~F, NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))))), O.mul(F, thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)))):
  %AP.imv(~F, n, N.ofkm(~KI.dnum(), ~F, ~H, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb), le_ee(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr)) : O.le(~F, NP.vn(~F, _), O.mul(F, thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))))
  DM.le_trans(~F, NP.vn(~F, M.matvec(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), O.mul(F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), O.mul(F, thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), NP.mv_n(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n, BX.vsub(~F, M.ofdv(~F, yc), xb), le_ee(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr)),
    FV.mul_le_r(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)), FV.vmax_nn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)),
      (%Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, ym), M.ofdm(~F, ym), AP.ofkm_d(~F, ~H, ym)) : O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, _, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL)
        hthl)))

# |S' - Jc| <= n lam rad, both points in the F-box of radius rad at P
def md_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hq: AP.eqok(~F, bb, lam, ms, eqs), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +rad: O.C(F), +hr0: O.le(~F, O.zero(F), rad), +hgb: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rad)), +hZr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad), +hBr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad)) -> O.le(~F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), n), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad))):
  +lyy = Equal.trans(Nat, M.len(~F, M.ofdv(~F, yc)), n, M.len(~F, M.ofdv(~F, yc)), lyc_d(~F, ~H, n, yc, lyc), Equal.sym(Nat, M.len(~F, M.ofdv(~F, yc)), n, lyc_d(~F, ~H, n, yc, lyc)))
  +lzz = Equal.trans(Nat, M.len(~F, xz), KA.klen(~KI.dnum(), pc), M.len(~F, M.ofdv(~F, pc)), lxz, klen_d(~F, ~H, pc))
  +lbb = Equal.trans(Nat, M.len(~F, xb), n, M.len(~F, M.ofdv(~F, yc)), lxb, Equal.sym(Nat, M.len(~F, M.ofdv(~F, yc)), n, lyc_d(~F, ~H, n, yc, lyc)))
  %AP.cen_fbx(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), rad) : O.le(~F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, DV.jac(~F, _, eqs, ST.iota(n, 0n)))), n), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)))
  AP.smat_lip_mn(~F, rad, bb, hr0, hb, AP.fbx(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), rad), AP.gbox_fbx(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), rad, bb, hr0, hgb), C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), AP.inbox_fbx(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), rad, hZr, lapp_eq(~F, M.ofdv(~F, yc), M.ofdv(~F, yc), xz, M.ofdv(~F, pc), lyy, lzz)), AP.inbox_fbx(~F, C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), rad, hBr, lapp_eq(~F, xb, M.ofdv(~F, yc), xz, M.ofdv(~F, pc), lbb, lzz)), lam, ms, hl0, eqs, hq, n, 0n)

def qq_bnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hq: AP.eqok(~F, bb, lam, ms, eqs), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +rad: O.C(F), +hr0: O.le(~F, O.zero(F), rad), +hgb: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rad)), +hZr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad), +hBr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad)) -> O.le(~F, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))))):
  +w = M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))
  +lw = Equal.trans(Nat, M.len(~F, w), GJ.nrows(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n, Equal.sym(Nat, GJ.nrows(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), M.len(~F, w), GJ.len_matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), NW.nrows_sj(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), eqs, n, hn))
  DM.le_trans(~F, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), w)), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), n), NP.vn(~F, w)), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)))), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), n, w, lw),
    NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), n), yn, NP.vn(~F, w), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), FV.vmax_nn(~F, w), hyn0,
      (%Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, ym), M.ofdm(~F, ym), AP.ofkm_d(~F, ~H, ym)) : O.le(~F, NP.mnorm(~F, _, n), yn)
        hyn),
      DM.le_trans(~F, NP.vn(~F, w), O.mul(F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), n), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), NP.mv_n(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), n, BX.vsub(~F, M.ofdv(~F, yc), xb), le_ee(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr)), FV.mul_le_r(~F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), n), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)), FV.vmax_nn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)), md_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, bb, lam, ms, hb, hl0, hq, yn, thL, hyn, hthl, hyn0, hthl0, rad, hr0, hgb, hZr, hBr)))))

# x_b lies within (65/64) S of yc, given c65 (thL + yn n lam rad) <= c65 - 1
def inbox_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +hab: {CK.allbelow(Nat.add(n, KA.klen(~KI.dnum(), pc)), eqs) == True{} : Bool}, +lyc: {KA.klen(~KI.dnum(), yc) == n : Nat}, +ym: List<&2, List<&2, S.D>>, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == KA.klen(~KI.dnum(), pc) : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +hb: O.le(~F, O.zero(F), bb), +hl0: O.le(~F, O.zero(F), lam), +hq: AP.eqok(~F, bb, lam, ms, eqs), +yn: O.C(F), +thL: O.C(F), +hyn: O.le(~F, NP.mnorm(~F, M.ofdm(~F, ym), n), yn), +hthl: O.le(~F, NP.mnorm(~F, M.madd(~F, M.ident(~F, n), M.mneg(~F, M.matmul(~F, M.ofdm(~F, ym), NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)))))), n), thL), +hyn0: O.le(~F, O.zero(F), yn), +hthl0: O.le(~F, O.zero(F), thL), +rad: O.C(F), +hr0: O.le(~F, O.zero(F), rad), +hgb: M.vbnd.all(~F, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc)), O.sub(~F, bb, rad)), +hZr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad), +hBr: M.vbnd.all(~F, BX.vsub(~F, C.app(~F, xb, xz), C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), rad), +hk: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.add(F, thL, O.mul(F, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad))))), O.sub(~F, M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), O.one(F)))) -> O.le(~F, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)), O.mul(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}))):
  +hE = FV.vmax_lub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))))), DG.vall_by(~F, ~BX.vsub(~F, M.ofdv(~F, yc), xb), ~O.add(F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))))), ~(k => in_at(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, k))), FO.nonneg_add(~F, M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))), dvmax_nn(~F, CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), FV.vmax_nn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))))))
  +hD = DM.le_trans(~F, NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))), O.add(F, NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))))), NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))))), O.add(F, O.mul(F, thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))))), NW.vn_by2s(~F, ~BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb)))), ~BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), ~M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb))), ~(k => qv_at(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, k))), FV.le_add2(~F, NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))), BX.vsub(~F, M.ofdv(~F, yc), xb))))), O.mul(F, thL, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb))), NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, M.madd(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), M.mneg(~F, NW.jc(~F, eqs, n, C.app(~F, M.ofdv(~F, yc), M.ofdv(~F, pc))))), BX.vsub(~F, M.ofdv(~F, yc), xb)))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)))), vp_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, bb, lam, ms, hb, hl0, hq, yn, thL, hyn, hthl, hyn0, hthl0, rad, hr0, hgb, hZr, hBr), qq_bnd(~F, ~H, n, eqs, hn, hh, yc, pc, pr, hab, lyc, ym, hpn, xb, xz, lxb, lxz, hz, hzr, bb, lam, ms, hb, hl0, hq, yn, thL, hyn, hthl, hyn0, hthl0, rad, hr0, hgb, hZr, hBr)))
  in_fin(~F, NP.vn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)), M.ofd(~F, NU.dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr))), NP.vn(~F, BX.vsub(~F, BX.vsub(~F, M.ofdv(~F, yc), xb), M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, ym), M.matvec(~F, CP.smat(~F, C.app(~F, M.ofdv(~F, yc), xz), C.app(~F, xb, xz), eqs, n, 0n), BX.vsub(~F, M.ofdv(~F, yc), xb))))), thL, yn, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), M.ofd(~F, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), hE, hD, hk, c65_nn(~F, ~H), FV.vmax_nn(~F, BX.vsub(~F, M.ofdv(~F, yc), xb)))
