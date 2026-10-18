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
