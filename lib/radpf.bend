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
