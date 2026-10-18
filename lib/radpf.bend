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
   (RP.le_add2(~F, a0, a1, b0, b1, pd_1(~F, dl, a0, a1, l1, ha), pd_1(~F, dl, b0, b1, l2, hb)),
    FV.le_rw_r(~F, O.sub(~F, O.add(F, a1, b1), O.add(F, a0, b0)), O.add(F, O.mul(F, l1, dl), O.mul(F, l2, dl)), O.mul(F, O.add(F, l1, l2), dl), FR.fring_eq(~F, [l1, l2, dl], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}),
      RL.le_rw_l(~F, O.add(F, O.sub(~F, a1, a0), O.sub(~F, b1, b0)), O.sub(~F, O.add(F, a1, b1), O.add(F, a0, b0)), O.add(F, O.mul(F, l1, dl), O.mul(F, l2, dl)), FR.fring_eq(~F, [a0, a1, b0, b1], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}),
        RP.le_add2(~F, O.sub(~F, a1, a0), O.mul(F, l1, dl), O.sub(~F, b1, b0), O.mul(F, l2, dl), pd_2(~F, dl, a0, a1, l1, ha), pd_2(~F, dl, b0, b1, l2, hb))))))

def sub_nn(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.le(~F, a, b)) -> O.le(~F, O.zero(F), O.sub(~F, b, a)):
  FM.sub_nonneg(~F, a, b, h)

# a product: |c1| = k1, |c2| = k2 (both boxes' centers agree), with
# k1 + a1 <= m1 and k2 + b1 <= m2 (the second box's grades)
def pd_mul(~F: O.OField, +dl: O.C(F), +k1: O.C(F), +k2: O.C(F), +a0: O.C(F), +a1: O.C(F), +l1: O.C(F), +m1: O.C(F), +b0: O.C(F), +b1: O.C(F), +l2: O.C(F), +m2: O.C(F), +hk1: O.le(~F, O.zero(F), k1), +hk2: O.le(~F, O.zero(F), k2), +ha: pd(~F, dl, a0, a1, l1), +hb: pd(~F, dl, b0, b1, l2), +hm1: O.le(~F, O.add(F, k1, a1), m1), +hm2: O.le(~F, O.add(F, k2, b1), m2)) -> pd(~F, dl, O.add(F, O.add(F, O.mul(F, k1, b0), O.mul(F, k2, a0)), O.mul(F, a0, b0)), O.add(F, O.add(F, O.mul(F, k1, b1), O.mul(F, k2, a1)), O.mul(F, a1, b1)), O.add(F, O.mul(F, m1, l2), O.mul(F, m2, l1))):
  +ha0 = pd_0(~F, dl, a0, a1, l1, ha)
  +hb0 = pd_0(~F, dl, b0, b1, l2, hb)
  +da = sub_nn(~F, a0, a1, pd_1(~F, dl, a0, a1, l1, ha))
  +db = sub_nn(~F, b0, b1, pd_1(~F, dl, b0, b1, l2, hb))
  +ea_ = sub_nn(~F, O.sub(~F, a1, a0), O.mul(F, l1, dl), pd_2(~F, dl, a0, a1, l1, ha))
  +eb_ = sub_nn(~F, O.sub(~F, b1, b0), O.mul(F, l2, dl), pd_2(~F, dl, b0, b1, l2, hb))
  +ha1 = DM.le_trans(~F, O.zero(F), a0, a1, ha0, pd_1(~F, dl, a0, a1, l1, ha))
  +hb1 = DM.le_trans(~F, O.zero(F), b0, b1, hb0, pd_1(~F, dl, b0, b1, l2, hb))
  +fm1 = sub_nn(~F, O.add(F, k1, a1), m1, hm1)
  +fm2 = DM.le_trans(~F, O.zero(F), O.sub(~F, m2, O.add(F, k2, b1)), O.sub(~F, m2, O.add(F, k2, b0)), sub_nn(~F, O.add(F, k2, b1), m2, hm2), FV.le_of_sub(~F, O.sub(~F, m2, O.add(F, k2, b1)), O.sub(~F, m2, O.add(F, k2, b0)), FM.nn_eq(~F, O.sub(~F, O.sub(~F, m2, O.add(F, k2, b0)), O.sub(~F, m2, O.add(F, k2, b1))), O.sub(~F, b1, b0), FR.fring_eq(~F, [m2, k2, b0, b1], E.ZSub{E.ZVar{3n}, E.ZVar{2n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}}, {==}), db)))
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
      %Equal.sym(N.KVec(~K), KB.bcenters(~K, CK.zipb(~K, ct, rt)), ct, bcen_zipb(~K, ct, rt, FV.succ_inj(KA.klen(~K, ct), KA.klen(~K, rt), hl))) : {Con{c, _} == Con{c, ct} : N.KVec(~K)}
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
      +hrl = NP.bnd_lo(~F, N.emap(K, F, H, r), rho, hr1)
      ((hn1, (FM.bnd_mono(~F, N.emap(K, F, H, c), O.sub(~F, bb, rho), O.sub(~F, bb, N.emap(K, F, H, r)), hc1, FM.nn_eq(~F, O.sub(~F, O.sub(~F, bb, N.emap(K, F, H, r)), O.sub(~F, bb, rho)), O.sub(~F, rho, N.emap(K, F, H, r)), FR.fring_eq(~F, [bb, rho, N.emap(K, F, H, r)], E.ZSub{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==}), FM.sub_nonneg(~F, N.emap(K, F, H, r), rho, hrl))), DM.le_trans(~F, N.emap(K, F, H, r), rho, O.mul(F, O.one(F), rho), hrl, AP.le_one_mul(~F, rho)))),
       gbox_zip(~K, ~F, ~H, ct, rt, rho, bb, hc2, hn2, hr2, FV.succ_inj(KA.klen(~K, ct), KA.klen(~K, rt), hl)))

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
      (h1, bpair_zip(~K, ~F, ~H, dl, ct, t0, t1, h2, FV.succ_inj(KA.klen(~K, ct), KA.klen(~K, t0), hl)))

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
      RP.le_add2(~F, FV.fabs(~F, N.emap(K, F, H, KA.kabs(~K, x))), FV.fabs(~F, N.emap(K, F, H, x)), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, KA.kvabs(~K, t)), k), NP.rowabs(~F, N.ofkv(~K, ~F, ~H, t), k), kabs_ent(~K, ~F, ~H, x), kabs_row(~K, ~F, ~H, t, k))

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
    RP.le_add2(~F, NP.vn(~F, pP), O.mul(F, thL, M.ofd(~F, r)), NP.vn(~F, qQ), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r))),
      DM.le_trans(~F, NP.vn(~F, pP), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n), NP.vn(~F, rF)), O.mul(F, thL, M.ofd(~F, r)), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n, rF, lrf(~F, ~H, n, r)),
        NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), aK)), n), thL, NP.vn(~F, rF), M.ofd(~F, r), FV.vmax_nn(~F, rF), hthl0, kabs_mn(~KI.dnum(), ~F, ~H, aK, n, thL, hthl0, imm_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0, yrr)), vnrf(~F, ~H, n, r, hr0))),
      DM.le_trans(~F, NP.vn(~F, qQ), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n), NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF))), O.mul(F, yn, O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r))), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF), ldk),
        NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, KA.kmabs(~KI.dnum(), ym)), n), yn, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)), FV.vmax_nn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), hyn0, ym_mn(~F, ~H, n, eqs, hn, hh, yc, pc, pr, lyc, lpp, ym, bb, lam, ms, rb, hb, hl0, hrb, hq, hc, hpn, hpr, yn, thL, hyn, hthl, hyn0, hthl0),
          DM.le_trans(~F, NP.vn(~F, M.matvec(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), rF)), O.mul(F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n), NP.vn(~F, rF)), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), M.ofd(~F, r)), NP.mv_n(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n, rF, lrf(~F, ~H, n, r)),
            NW.mm_le(~F, NP.mnorm(~F, N.ofkm(~KI.dnum(), ~F, ~H, dK), n), O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rb)), NP.vn(~F, rF), M.ofd(~F, r), FV.vmax_nn(~F, rF), AP.lr_nn(~F, n, lam, rb, hl0, hrb), srad_mn(~KI.dnum(), ~F, ~H, rb, bb, hrb, hb, CK.box(~KI.dnum(), n, yc, yrr, pc, pr), gb, lam, ms, hl0, eqs, hq, hh, n, 0n), vnrf(~F, ~H, n, r, hr0)))))))
