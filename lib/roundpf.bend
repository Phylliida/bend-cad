# bend-cad: rounding, for solve_complete (DESIGN §10.4, C3b). Proofs only.
#
# What the solver's rounding (lib/numer.bend) does to a number's value in
# every ordered field F. Underneath: Euclid's division (QRD.div, which
# lib/qreduce.bend leaves unproven because reduce checks its answer) gives
# n = q d + r with 0 <= r < d, so zfloor is a floor; pshr is a floor by
# 2^k; and size p is p's binary length, 2^(size p) <= 2p and
# p < 2^(size p). Then:
#   dround_err: |dround(x, p) - x| <= 2^-(p+1)
#   dsig_err:   |dsig(x, b) - x| <= |x| 2^-b
#   qsig_err:   |qsig(q, b) - q| <= |q| 2^-b
#   dsigup_ok:  x <= dsigup(x, b) <= x + |x| 2^-b
# Integers live in F through ofz and ofp: an integer fact a < b becomes
# a + 1 <= b there, so floors are stated as f d <= n and n + 1 <= (f + 1) d.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./zord.bend as ZO
import ./qreduce.bend as QRD
import ./numer.bend as NU
import ./karith.bend as KA
import ./dyadic.bend as DY
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./qemb.bend as QE
import ./kball.bend as KB
import ./dmat.bend as DM
import ./nat.bend as LN

# Order helpers
# -------------

# a <= b gives a + a <= b + b
def le_dbl(~F: O.OField, +a: O.C(F), +b: O.C(F), +h: O.le(~F, a, b)) -> O.le(~F, O.add(F, a, a), O.add(F, b, b)):
  FV.le_add2(~F, a, b, a, b, h, h)

# Positive integers in F
# ----------------------

# 2^k in F
def t2(~F: O.OField, k: Nat) -> O.C(F):
  O.ofp(~F, S.Pos.pow2(k))

def ofp_ge1(~F: O.OField, p: S.Pos) -> O.le(~F, O.one(F), O.ofp(~F, p)):
  match p:
    case S.XH{}:
      FO.le_refl(~F, O.one(F))
    case S.XO{+q}:
      +s = FM.sub_nonneg(~F, O.one(F), O.ofp(~F, q), ofp_ge1(~F, q))
      FV.le_of_sub(~F, O.one(F), O.ofp(~F, S.XO{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XO{q}), O.one(F)), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.one(F), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F)), s, s), FO.one_nn(~F))))
    case S.XI{+q}:
      +s = FM.sub_nonneg(~F, O.one(F), O.ofp(~F, q), ofp_ge1(~F, q))
      FV.le_of_sub(~F, O.one(F), O.ofp(~F, S.XI{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XI{q}), O.one(F)), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.add(F, O.one(F), O.one(F))), FR.fring_eq(~F, [O.ofp(~F, q)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.add(F, O.one(F), O.one(F)), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F)), s, s), FO.nonneg_add(~F, O.one(F), O.one(F), FO.one_nn(~F), FO.one_nn(~F)))))

def ofp_nn(~F: O.OField, +p: S.Pos) -> O.le(~F, O.zero(F), O.ofp(~F, p)):
  FO.lt_le(~F, O.zero(F), O.ofp(~F, p), QE.ofp_pos(~F, p))

# 2^a 2^b = 2^(a + b)
def t2_add(~F: O.OField, +a: Nat, +b: Nat) -> {O.mul(F, t2(~F, a), t2(~F, b)) == t2(~F, Nat.add(a, b)) : O.C(F)}:
  Equal.trans(O.C(F), O.mul(F, t2(~F, a), t2(~F, b)), O.ofp(~F, S.Pos.mul(S.Pos.pow2(a), S.Pos.pow2(b))), t2(~F, Nat.add(a, b)), FR.ofz_mul(~F, S.Zpos{S.Pos.pow2(a)}, S.Zpos{S.Pos.pow2(b)}), Equal.cong(S.Pos, O.C(F), q => O.ofp(~F, q), S.Pos.mul(S.Pos.pow2(a), S.Pos.pow2(b)), S.Pos.pow2(Nat.add(a, b)), DY.pow2_add(a, b)))

# p + q in F
def ofp_add(~F: O.OField, +a: S.Pos, +b: S.Pos) -> {O.add(F, O.ofp(~F, a), O.ofp(~F, b)) == O.ofp(~F, S.Pos.add(a, b)) : O.C(F)}:
  FR.ofz_add(~F, S.Zpos{a}, S.Zpos{b})

# 2^(size p) <= 2 p
def size_lo(~F: O.OField, p: S.Pos) -> O.le(~F, t2(~F, QRD.size(p)), O.add(F, O.ofp(~F, p), O.ofp(~F, p))):
  match p:
    case S.XH{}:
      FO.le_refl(~F, O.add(F, O.one(F), O.one(F)))
    case S.XO{+q}:
      le_dbl(~F, t2(~F, QRD.size(q)), O.ofp(~F, S.XO{q}), size_lo(~F, q))
    case S.XI{+q}:
      le_dbl(~F, t2(~F, QRD.size(q)), O.ofp(~F, S.XI{q}), FV.le_of_sub(~F, t2(~F, QRD.size(q)), O.ofp(~F, S.XI{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XI{q}), t2(~F, QRD.size(q))), O.add(F, O.sub(~F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), t2(~F, QRD.size(q))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q), t2(~F, QRD.size(q))], E.ZAdd{E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), t2(~F, QRD.size(q))), O.one(F), FM.sub_nonneg(~F, t2(~F, QRD.size(q)), O.add(F, O.ofp(~F, q), O.ofp(~F, q)), size_lo(~F, q)), FO.one_nn(~F)))))

# p + 1 <= 2^(size p)
def size_hi(~F: O.OField, p: S.Pos) -> O.le(~F, O.add(F, O.ofp(~F, p), O.one(F)), t2(~F, QRD.size(p))):
  match p:
    case S.XH{}:
      FO.le_refl(~F, O.add(F, O.one(F), O.one(F)))
    case S.XO{+q}:
      FV.le_of_sub(~F, O.add(F, O.ofp(~F, S.XO{q}), O.one(F)), t2(~F, QRD.size(S.XO{q})), FM.nn_eq(~F, O.sub(~F, t2(~F, QRD.size(S.XO{q})), O.add(F, O.ofp(~F, S.XO{q}), O.one(F))), O.add(F, O.sub(~F, O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F)))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q), t2(~F, QRD.size(q))], E.ZAdd{E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F)))), O.one(F), FM.sub_nonneg(~F, O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F))), O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), le_dbl(~F, O.add(F, O.ofp(~F, q), O.one(F)), t2(~F, QRD.size(q)), size_hi(~F, q))), FO.one_nn(~F))))
    case S.XI{+q}:
      FV.le_of_sub(~F, O.add(F, O.ofp(~F, S.XI{q}), O.one(F)), t2(~F, QRD.size(S.XI{q})), FM.nn_eq(~F, O.sub(~F, t2(~F, QRD.size(S.XI{q})), O.add(F, O.ofp(~F, S.XI{q}), O.one(F))), O.sub(~F, O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F)))), FR.fring_eq(~F, [O.ofp(~F, q), t2(~F, QRD.size(q))], E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FM.sub_nonneg(~F, O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F))), O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), le_dbl(~F, O.add(F, O.ofp(~F, q), O.one(F)), t2(~F, QRD.size(q)), size_hi(~F, q)))))

# Integers in F
# -------------

# a positive integer is at least 1
def pos_ge1(~F: O.OField, s: S.Z, h: ZO.pos(s)) -> O.le(~F, O.one(F), O.ofz(~F, s)):
  match s:
    case S.Z0{}:
      FO.absurd(O.le(~F, O.one(F), O.zero(F)), h)
    case S.Zpos{p}:
      ofp_ge1(~F, p)
    case S.Zneg{p}:
      FO.absurd(O.le(~F, O.one(F), O.neg(F, O.ofp(~F, p))), h)

def ofz_sub(~F: O.OField, +a: S.Z, +b: S.Z) -> {O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)) == O.ofz(~F, S.Z.sub(b, a)) : O.C(F)}:
  %FR.ofz_add(~F, b, S.Z.neg(a)) : {O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)) == _ : O.C(F)}
  %FR.ofz_neg(~F, a) : {O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)) == O.add(F, O.ofz(~F, b), _) : O.C(F)}
  {==}

# a + 1 <= b gives a <= b
def le_of_succ(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.le(~F, O.add(F, a, O.one(F)), b)) -> O.le(~F, a, b):
  FV.le_of_sub(~F, a, b, FM.nn_eq(~F, O.sub(~F, b, a), O.add(F, O.sub(~F, b, O.add(F, a, O.one(F))), O.one(F)), FR.fring_eq(~F, [a, b], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, {==}), FO.nonneg_add(~F, O.sub(~F, b, O.add(F, a, O.one(F))), O.one(F), FM.sub_nonneg(~F, O.add(F, a, O.one(F)), b, h), FO.one_nn(~F))))

# a < b in Z: a + 1 <= b in F
def zlt(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == LT{} : Cmp}) -> O.le(~F, O.add(F, O.ofz(~F, a), O.one(F)), O.ofz(~F, b)):
  FV.le_of_sub(~F, O.add(F, O.ofz(~F, a), O.one(F)), O.ofz(~F, b), FM.nn_eq(~F, O.sub(~F, O.ofz(~F, b), O.add(F, O.ofz(~F, a), O.one(F))), O.sub(~F, O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, a), O.ofz(~F, b)], E.ZSub{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FM.sub_nonneg(~F, O.one(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), (%Equal.sym(O.C(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.ofz(~F, S.Z.sub(b, a)), ofz_sub(~F, a, b)) : O.le(~F, O.one(F), _)
    pos_ge1(~F, S.Z.sub(b, a), ZO.lt_pos(a, b, h))))))

# a = b in Z
def zeq(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == EQ{} : Cmp}) -> {O.ofz(~F, b) == O.ofz(~F, a) : O.C(F)}:
  FO.eq_of_sub(~F, O.ofz(~F, b), O.ofz(~F, a), Equal.trans(O.C(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.ofz(~F, S.Z.sub(b, a)), O.zero(F), ofz_sub(~F, a, b), Equal.cong(S.Z, O.C(F), z => O.ofz(~F, z), S.Z.sub(b, a), S.Z0{}, ZO.eq_zero(a, b, h))))

def zgt_eq(~F: O.OField, +a: S.Z, +b: S.Z) -> {O.sub(~F, O.ofz(~F, S.Z.neg(S.Z.sub(b, a))), O.one(F)) == O.sub(~F, O.ofz(~F, a), O.add(F, O.ofz(~F, b), O.one(F))) : O.C(F)}:
  %FR.ofz_neg(~F, S.Z.sub(b, a)) : {O.sub(~F, _, O.one(F)) == O.sub(~F, O.ofz(~F, a), O.add(F, O.ofz(~F, b), O.one(F))) : O.C(F)}
  %ofz_sub(~F, a, b) : {O.sub(~F, O.neg(F, _), O.one(F)) == O.sub(~F, O.ofz(~F, a), O.add(F, O.ofz(~F, b), O.one(F))) : O.C(F)}
  FR.fring_eq(~F, [O.ofz(~F, a), O.ofz(~F, b)], E.ZSub{E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, {==})

# a > b in Z: b + 1 <= a in F
def zgt(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == GT{} : Cmp}) -> O.le(~F, O.add(F, O.ofz(~F, b), O.one(F)), O.ofz(~F, a)):
  FV.le_of_sub(~F, O.add(F, O.ofz(~F, b), O.one(F)), O.ofz(~F, a), FM.nn_eq(~F, O.sub(~F, O.ofz(~F, a), O.add(F, O.ofz(~F, b), O.one(F))), O.sub(~F, O.ofz(~F, S.Z.neg(S.Z.sub(b, a))), O.one(F)), zgt_eq(~F, a, b), FM.sub_nonneg(~F, O.one(F), O.ofz(~F, S.Z.neg(S.Z.sub(b, a))), pos_ge1(~F, S.Z.neg(S.Z.sub(b, a)), ZO.gt_pos(a, b, h)))))

def ofz_double(~F: O.OField, x: S.Z) -> {O.ofz(~F, S.Z.double(x)) == O.add(F, O.ofz(~F, x), O.ofz(~F, x)) : O.C(F)}:
  match x:
    case S.Z0{}:
      Equal.sym(O.C(F), O.add(F, O.zero(F), O.zero(F)), O.zero(F), O.add_zero(F)(O.zero(F)))
    case S.Zpos{p}:
      {==}
    case S.Zneg{+p}:
      Equal.sym(O.C(F), O.add(F, O.neg(F, O.ofp(~F, p)), O.neg(F, O.ofp(~F, p))), O.neg(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p))), FL.neg_add(~F, O.ofp(~F, p), O.ofp(~F, p)))

def pd_ok(~F: O.OField, p: S.Pos) -> {O.add(F, O.ofp(~F, S.Pos.pred_double(p)), O.one(F)) == O.add(F, O.ofp(~F, p), O.ofp(~F, p)) : O.C(F)}:
  match p:
    case S.XH{}:
      {==}
    case S.XO{+q}:
      FO.eq_of_sub(~F, O.add(F, O.add(F, O.add(F, O.ofp(~F, S.Pos.pred_double(q)), O.ofp(~F, S.Pos.pred_double(q))), O.one(F)), O.one(F)), O.add(F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), O.add(F, O.ofp(~F, q), O.ofp(~F, q))), FO.cert1(~F, O.sub(~F, O.add(F, O.add(F, O.add(F, O.ofp(~F, S.Pos.pred_double(q)), O.ofp(~F, S.Pos.pred_double(q))), O.one(F)), O.one(F)), O.add(F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), O.add(F, O.ofp(~F, q), O.ofp(~F, q)))), O.add(F, O.one(F), O.one(F)), O.sub(~F, O.add(F, O.ofp(~F, S.Pos.pred_double(q)), O.one(F)), O.add(F, O.ofp(~F, q), O.ofp(~F, q))), FR.fring_eq(~F, [O.ofp(~F, S.Pos.pred_double(q)), O.ofp(~F, q)], E.ZSub{E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, {==}), FO.sub_of_eq(~F, O.add(F, O.ofp(~F, S.Pos.pred_double(q)), O.one(F)), O.add(F, O.ofp(~F, q), O.ofp(~F, q)), pd_ok(~F, q))))
    case S.XI{+q}:
      FR.fring_eq(~F, [O.ofp(~F, q)], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==})

def ofz_sdouble(~F: O.OField, x: S.Z) -> {O.ofz(~F, S.Z.succ_double(x)) == O.add(F, O.add(F, O.ofz(~F, x), O.ofz(~F, x)), O.one(F)) : O.C(F)}:
  match x:
    case S.Z0{}:
      FR.fring_eq(~F, [O.zero(F)], E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==})
    case S.Zpos{p}:
      {==}
    case S.Zneg{+p}:
      FO.eq_of_sub(~F, O.neg(F, O.ofp(~F, S.Pos.pred_double(p))), O.add(F, O.add(F, O.neg(F, O.ofp(~F, p)), O.neg(F, O.ofp(~F, p))), O.one(F)), FO.cert1(~F, O.sub(~F, O.neg(F, O.ofp(~F, S.Pos.pred_double(p))), O.add(F, O.add(F, O.neg(F, O.ofp(~F, p)), O.neg(F, O.ofp(~F, p))), O.one(F))), O.neg(F, O.one(F)), O.sub(~F, O.add(F, O.ofp(~F, S.Pos.pred_double(p)), O.one(F)), O.add(F, O.ofp(~F, p), O.ofp(~F, p))), FR.fring_eq(~F, [O.ofp(~F, S.Pos.pred_double(p)), O.ofp(~F, p)], E.ZSub{E.ZNeg{E.ZVar{0n}}, E.ZAdd{E.ZAdd{E.ZNeg{E.ZVar{1n}}, E.ZNeg{E.ZVar{1n}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, {==}), FO.sub_of_eq(~F, O.add(F, O.ofp(~F, S.Pos.pred_double(p)), O.one(F)), O.add(F, O.ofp(~F, p), O.ofp(~F, p)), pd_ok(~F, p))))

# Euclid's division
# -----------------

# n = q d + r with 0 <= r < d (read through the projections, so that it
# applies to a division not yet computed)
def dvok(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv) -> Data:
  M.Both({O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v))) : O.C(F)}, M.Both(O.le(~F, O.zero(F), O.ofz(~F, QRD.Dv.r(v))), O.le(~F, O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F)), O.ofp(~F, d))))

def dv_mk(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv, he: {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v))) : O.C(F)}, h0: O.le(~F, O.zero(F), O.ofz(~F, QRD.Dv.r(v))), h1: O.le(~F, O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F)), O.ofp(~F, d))) -> dvok(~F, n, d, v):
  (he, (h0, h1))

def dv_e(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv, h: dvok(~F, n, d, v)) -> {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v))) : O.C(F)}:
  (a, b) = h
  a

def dv_b(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv, h: dvok(~F, n, d, v)) -> M.Both(O.le(~F, O.zero(F), O.ofz(~F, QRD.Dv.r(v))), O.le(~F, O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F)), O.ofp(~F, d))):
  (a, b) = h
  b

def dv_0.go(~F: O.OField, +d: S.Pos, +r: S.Z, h: M.Both(O.le(~F, O.zero(F), O.ofz(~F, r)), O.le(~F, O.add(F, O.ofz(~F, r), O.one(F)), O.ofp(~F, d)))) -> O.le(~F, O.zero(F), O.ofz(~F, r)):
  (a, b) = h
  a

def dv_1.go(~F: O.OField, +d: S.Pos, +r: S.Z, h: M.Both(O.le(~F, O.zero(F), O.ofz(~F, r)), O.le(~F, O.add(F, O.ofz(~F, r), O.one(F)), O.ofp(~F, d)))) -> O.le(~F, O.add(F, O.ofz(~F, r), O.one(F)), O.ofp(~F, d)):
  (a, b) = h
  b

def dv_0(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv, h: dvok(~F, n, d, v)) -> O.le(~F, O.zero(F), O.ofz(~F, QRD.Dv.r(v))):
  dv_0.go(~F, d, QRD.Dv.r(v), dv_b(~F, n, d, v, h))

def dv_1(~F: O.OField, +n: S.Pos, +d: S.Pos, +v: QRD.Dv, h: dvok(~F, n, d, v)) -> O.le(~F, O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F)), O.ofp(~F, d)):
  dv_1.go(~F, d, QRD.Dv.r(v), dv_b(~F, n, d, v, h))

def adj_e(~F: O.OField, +n: S.Pos, +q2: S.Z, +r2: S.Z, +d: S.Pos, he: {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, q2), O.ofp(~F, d)), O.ofz(~F, r2)) : O.C(F)}) -> {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, S.Z.add(q2, S.Zpos{S.XH{}})), O.ofp(~F, d)), O.ofz(~F, S.Z.sub(r2, S.Zpos{d}))) : O.C(F)}:
  %FR.ofz_add(~F, q2, S.Zpos{S.XH{}}) : {O.ofp(~F, n) == O.add(F, O.mul(F, _, O.ofp(~F, d)), O.ofz(~F, S.Z.sub(r2, S.Zpos{d}))) : O.C(F)}
  %ofz_sub(~F, S.Zpos{d}, r2) : {O.ofp(~F, n) == O.add(F, O.mul(F, O.add(F, O.ofz(~F, q2), O.one(F)), O.ofp(~F, d)), _) : O.C(F)}
  FO.eq_of_sub(~F, O.ofp(~F, n), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q2), O.one(F)), O.ofp(~F, d)), O.sub(~F, O.ofz(~F, r2), O.ofp(~F, d))), FO.cert1(~F, O.sub(~F, O.ofp(~F, n), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q2), O.one(F)), O.ofp(~F, d)), O.sub(~F, O.ofz(~F, r2), O.ofp(~F, d)))), O.one(F), O.sub(~F, O.ofp(~F, n), O.add(F, O.mul(F, O.ofz(~F, q2), O.ofp(~F, d)), O.ofz(~F, r2))), FR.fring_eq(~F, [O.ofp(~F, n), O.ofz(~F, q2), O.ofz(~F, r2), O.ofp(~F, d)], E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZSub{E.ZVar{2n}, E.ZVar{3n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), FO.sub_of_eq(~F, O.ofp(~F, n), O.add(F, O.mul(F, O.ofz(~F, q2), O.ofp(~F, d)), O.ofz(~F, r2)), he)))

# r2 >= d: subtract d once
def adj_ge(~F: O.OField, +n: S.Pos, +q2: S.Z, +r2: S.Z, +d: S.Pos, he: {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, q2), O.ofp(~F, d)), O.ofz(~F, r2)) : O.C(F)}, +hge: O.le(~F, O.ofp(~F, d), O.ofz(~F, r2)), h2: O.le(~F, O.add(F, O.ofz(~F, r2), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)))) -> dvok(~F, n, d, QRD.Dv{S.Z.add(q2, S.Zpos{S.XH{}}), S.Z.sub(r2, S.Zpos{d})}):
  dv_mk(~F, n, d, QRD.Dv{S.Z.add(q2, S.Zpos{S.XH{}}), S.Z.sub(r2, S.Zpos{d})}, adj_e(~F, n, q2, r2, d, he),
    (%ofz_sub(~F, S.Zpos{d}, r2) : O.le(~F, O.zero(F), _)
      FM.sub_nonneg(~F, O.ofp(~F, d), O.ofz(~F, r2), hge)),
    (%ofz_sub(~F, S.Zpos{d}, r2) : O.le(~F, O.add(F, _, O.one(F)), O.ofp(~F, d))
      FV.le_of_sub(~F, O.add(F, O.sub(~F, O.ofz(~F, r2), O.ofp(~F, d)), O.one(F)), O.ofp(~F, d), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.sub(~F, O.ofz(~F, r2), O.ofp(~F, d)), O.one(F))), O.sub(~F, O.add(F, O.ofp(~F, d), O.ofp(~F, d)), O.add(F, O.ofz(~F, r2), O.one(F))), FR.fring_eq(~F, [O.ofz(~F, r2), O.ofp(~F, d)], E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FM.sub_nonneg(~F, O.add(F, O.ofz(~F, r2), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)), h2)))))

def adj_ok(~F: O.OField, c: Cmp, +n: S.Pos, +q2: S.Z, +r2: S.Z, +d: S.Pos, e: {S.Z.cmp(r2, S.Zpos{d}) == c : Cmp}, he: {O.ofp(~F, n) == O.add(F, O.mul(F, O.ofz(~F, q2), O.ofp(~F, d)), O.ofz(~F, r2)) : O.C(F)}, h0: O.le(~F, O.zero(F), O.ofz(~F, r2)), h2: O.le(~F, O.add(F, O.ofz(~F, r2), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)))) -> dvok(~F, n, d, QRD.div.adj(c, q2, r2, d)):
  match c:
    case LT{}:
      dv_mk(~F, n, d, QRD.Dv{q2, r2}, he, h0, zlt(~F, r2, S.Zpos{d}, e))
    case EQ{}:
      adj_ge(~F, n, q2, r2, d, he, Inr{zeq(~F, r2, S.Zpos{d}, e)}, h2)
    case GT{}:
      adj_ge(~F, n, q2, r2, d, he, le_of_succ(~F, O.ofp(~F, d), O.ofz(~F, r2), zgt(~F, r2, S.Zpos{d}, e)), h2)

def step_e0(~F: O.OField, +m: S.Pos, +d: S.Pos, +q: S.Z, +r: S.Z, he: {O.ofp(~F, m) == O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r)) : O.C(F)}) -> {O.ofp(~F, S.XO{m}) == O.add(F, O.mul(F, O.ofz(~F, S.Z.double(q)), O.ofp(~F, d)), O.ofz(~F, S.Z.double(r))) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofz(~F, S.Z.double(q)), O.add(F, O.ofz(~F, q), O.ofz(~F, q)), ofz_double(~F, q)) : {O.ofp(~F, S.XO{m}) == O.add(F, O.mul(F, _, O.ofp(~F, d)), O.ofz(~F, S.Z.double(r))) : O.C(F)}
  %Equal.sym(O.C(F), O.ofz(~F, S.Z.double(r)), O.add(F, O.ofz(~F, r), O.ofz(~F, r)), ofz_double(~F, r)) : {O.ofp(~F, S.XO{m}) == O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), _) : O.C(F)}
  FO.eq_of_sub(~F, O.add(F, O.ofp(~F, m), O.ofp(~F, m)), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), O.add(F, O.ofz(~F, r), O.ofz(~F, r))), FO.cert1(~F, O.sub(~F, O.add(F, O.ofp(~F, m), O.ofp(~F, m)), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), O.add(F, O.ofz(~F, r), O.ofz(~F, r)))), O.add(F, O.one(F), O.one(F)), O.sub(~F, O.ofp(~F, m), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r))), FR.fring_eq(~F, [O.ofp(~F, m), O.ofz(~F, q), O.ofz(~F, r), O.ofp(~F, d)], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), FO.sub_of_eq(~F, O.ofp(~F, m), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r)), he)))

def step_e1(~F: O.OField, +m: S.Pos, +d: S.Pos, +q: S.Z, +r: S.Z, he: {O.ofp(~F, m) == O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r)) : O.C(F)}) -> {O.ofp(~F, S.XI{m}) == O.add(F, O.mul(F, O.ofz(~F, S.Z.double(q)), O.ofp(~F, d)), O.ofz(~F, S.Z.succ_double(r))) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofz(~F, S.Z.double(q)), O.add(F, O.ofz(~F, q), O.ofz(~F, q)), ofz_double(~F, q)) : {O.ofp(~F, S.XI{m}) == O.add(F, O.mul(F, _, O.ofp(~F, d)), O.ofz(~F, S.Z.succ_double(r))) : O.C(F)}
  %Equal.sym(O.C(F), O.ofz(~F, S.Z.succ_double(r)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), ofz_sdouble(~F, r)) : {O.ofp(~F, S.XI{m}) == O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), _) : O.C(F)}
  FO.eq_of_sub(~F, O.add(F, O.add(F, O.ofp(~F, m), O.ofp(~F, m)), O.one(F)), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F))), FO.cert1(~F, O.sub(~F, O.add(F, O.add(F, O.ofp(~F, m), O.ofp(~F, m)), O.one(F)), O.add(F, O.mul(F, O.add(F, O.ofz(~F, q), O.ofz(~F, q)), O.ofp(~F, d)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)))), O.add(F, O.one(F), O.one(F)), O.sub(~F, O.ofp(~F, m), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r))), FR.fring_eq(~F, [O.ofp(~F, m), O.ofz(~F, q), O.ofz(~F, r), O.ofp(~F, d)], E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), FO.sub_of_eq(~F, O.ofp(~F, m), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofz(~F, r)), he)))

def step0.go(~F: O.OField, +m: S.Pos, +d: S.Pos, +q: S.Z, +r: S.Z, +h: dvok(~F, m, d, QRD.Dv{q, r})) -> dvok(~F, S.XO{m}, d, QRD.div.step(d, False{}, QRD.Dv{q, r})):
  +h0 = dv_0(~F, m, d, QRD.Dv{q, r}, h)
  +s = FM.sub_nonneg(~F, O.add(F, O.ofz(~F, r), O.one(F)), O.ofp(~F, d), dv_1(~F, m, d, QRD.Dv{q, r}, h))
  adj_ok(~F, S.Z.cmp(S.Z.double(r), S.Zpos{d}), S.XO{m}, S.Z.double(q), S.Z.double(r), d, {==}, step_e0(~F, m, d, q, r, dv_e(~F, m, d, QRD.Dv{q, r}, h)),
    (%Equal.sym(O.C(F), O.ofz(~F, S.Z.double(r)), O.add(F, O.ofz(~F, r), O.ofz(~F, r)), ofz_double(~F, r)) : O.le(~F, O.zero(F), _)
      FO.nonneg_add(~F, O.ofz(~F, r), O.ofz(~F, r), h0, h0)),
    (%Equal.sym(O.C(F), O.ofz(~F, S.Z.double(r)), O.add(F, O.ofz(~F, r), O.ofz(~F, r)), ofz_double(~F, r)) : O.le(~F, O.add(F, _, O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)))
      FV.le_of_sub(~F, O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.add(F, O.ofp(~F, d), O.ofp(~F, d)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F))), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F)))), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, r), O.ofp(~F, d)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F)))), O.one(F), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), s, s), FO.one_nn(~F))))))

# one step of long division, bit 0
def step0(~F: O.OField, +m: S.Pos, +d: S.Pos, v: QRD.Dv, h: dvok(~F, m, d, v)) -> dvok(~F, S.XO{m}, d, QRD.div.step(d, False{}, v)):
  match v:
    case QRD.Dv{+q, +r}:
      step0.go(~F, m, d, q, r, h)

def step1.go(~F: O.OField, +m: S.Pos, +d: S.Pos, +q: S.Z, +r: S.Z, +h: dvok(~F, m, d, QRD.Dv{q, r})) -> dvok(~F, S.XI{m}, d, QRD.div.step(d, True{}, QRD.Dv{q, r})):
  +h0 = dv_0(~F, m, d, QRD.Dv{q, r}, h)
  +s = FM.sub_nonneg(~F, O.add(F, O.ofz(~F, r), O.one(F)), O.ofp(~F, d), dv_1(~F, m, d, QRD.Dv{q, r}, h))
  adj_ok(~F, S.Z.cmp(S.Z.succ_double(r), S.Zpos{d}), S.XI{m}, S.Z.double(q), S.Z.succ_double(r), d, {==}, step_e1(~F, m, d, q, r, dv_e(~F, m, d, QRD.Dv{q, r}, h)),
    (%Equal.sym(O.C(F), O.ofz(~F, S.Z.succ_double(r)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), ofz_sdouble(~F, r)) : O.le(~F, O.zero(F), _)
      FO.nonneg_add(~F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F), FO.nonneg_add(~F, O.ofz(~F, r), O.ofz(~F, r), h0, h0), FO.one_nn(~F))),
    (%Equal.sym(O.C(F), O.ofz(~F, S.Z.succ_double(r)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), ofz_sdouble(~F, r)) : O.le(~F, O.add(F, _, O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)))
      FV.le_of_sub(~F, O.add(F, O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.add(F, O.ofp(~F, d), O.ofp(~F, d)), O.add(F, O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), O.one(F))), O.add(F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F)))), FR.fring_eq(~F, [O.ofz(~F, r), O.ofp(~F, d)], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), s, s)))))

# one step of long division, bit 1
def step1(~F: O.OField, +m: S.Pos, +d: S.Pos, v: QRD.Dv, h: dvok(~F, m, d, v)) -> dvok(~F, S.XI{m}, d, QRD.div.step(d, True{}, v)):
  match v:
    case QRD.Dv{+q, +r}:
      step1.go(~F, m, d, q, r, h)

# Euclid: div(n, d) = (q, r) with n = q d + r and 0 <= r < d
def div_ok(~F: O.OField, n: S.Pos, +d: S.Pos) -> dvok(~F, n, d, QRD.div(n, d)):
  match n:
    case S.XH{}:
      adj_ok(~F, S.Z.cmp(S.Zpos{S.XH{}}, S.Zpos{d}), S.XH{}, S.Z0{}, S.Zpos{S.XH{}}, d, {==}, FR.fring_eq(~F, [O.ofp(~F, d)], E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), FO.one_nn(~F), le_dbl(~F, O.one(F), O.ofp(~F, d), ofp_ge1(~F, d)))
    case S.XO{+m}:
      step0(~F, m, d, QRD.div(m, d), div_ok(~F, m, d))
    case S.XI{+m}:
      step1(~F, m, d, QRD.div(m, d), div_ok(~F, m, d))

# Floors
# ------

# f is the floor of n / d: f d <= n and n + 1 <= (f + 1) d
def zfl(~F: O.OField, +n: S.Z, +d: S.Pos, +f: S.Z) -> Data:
  M.Both(O.le(~F, O.mul(F, O.ofz(~F, f), O.ofp(~F, d)), O.ofz(~F, n)), O.le(~F, O.add(F, O.ofz(~F, n), O.one(F)), O.mul(F, O.add(F, O.ofz(~F, f), O.one(F)), O.ofp(~F, d))))

# a floor stated with f's value in F
def zfl_of(~F: O.OField, +n: S.Z, +d: S.Pos, +f: S.Z, +fv: O.C(F), +ef: {O.ofz(~F, f) == fv : O.C(F)}, h1: O.le(~F, O.mul(F, fv, O.ofp(~F, d)), O.ofz(~F, n)), h2: O.le(~F, O.add(F, O.ofz(~F, n), O.one(F)), O.mul(F, O.add(F, fv, O.one(F)), O.ofp(~F, d)))) -> zfl(~F, n, d, f):
  ((%Equal.sym(O.C(F), O.ofz(~F, f), fv, ef) : O.le(~F, O.mul(F, _, O.ofp(~F, d)), O.ofz(~F, n))
     h1),
   (%Equal.sym(O.C(F), O.ofz(~F, f), fv, ef) : O.le(~F, O.add(F, O.ofz(~F, n), O.one(F)), O.mul(F, O.add(F, _, O.one(F)), O.ofp(~F, d)))
     h2))


def zfloor_pos(~F: O.OField, +p: S.Pos, +d: S.Pos, +v: QRD.Dv, +h: dvok(~F, p, d, v)) -> zfl(~F, S.Zpos{p}, d, QRD.Dv.q(v)):
  +ee = FO.sub_of_eq(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v))), dv_e(~F, p, d, v, h))
  (FV.le_of_sub(~F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofp(~F, p), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, p), O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d))), O.ofz(~F, QRD.Dv.r(v)), FO.eq_of_sub(~F, O.ofz(~F, QRD.Dv.r(v)), O.sub(~F, O.ofp(~F, p), O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d))), FO.cert1(~F, O.sub(~F, O.ofz(~F, QRD.Dv.r(v)), O.sub(~F, O.ofp(~F, p), O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)))), O.neg(F, O.one(F)), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v)))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, QRD.Dv.q(v)), O.ofz(~F, QRD.Dv.r(v)), O.ofp(~F, d)], E.ZSub{E.ZVar{2n}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), ee)), dv_0(~F, p, d, v, h))),
   FV.le_of_sub(~F, O.add(F, O.ofp(~F, p), O.one(F)), O.mul(F, O.add(F, O.ofz(~F, QRD.Dv.q(v)), O.one(F)), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.ofz(~F, QRD.Dv.q(v)), O.one(F)), O.ofp(~F, d)), O.add(F, O.ofp(~F, p), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F))), FO.eq_of_sub(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F))), O.sub(~F, O.mul(F, O.add(F, O.ofz(~F, QRD.Dv.q(v)), O.one(F)), O.ofp(~F, d)), O.add(F, O.ofp(~F, p), O.one(F))), FO.cert1(~F, O.sub(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F))), O.sub(~F, O.mul(F, O.add(F, O.ofz(~F, QRD.Dv.q(v)), O.one(F)), O.ofp(~F, d)), O.add(F, O.ofp(~F, p), O.one(F)))), O.one(F), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, QRD.Dv.q(v)), O.ofp(~F, d)), O.ofz(~F, QRD.Dv.r(v)))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, QRD.Dv.q(v)), O.ofz(~F, QRD.Dv.r(v)), O.ofp(~F, d)], E.ZSub{E.ZSub{E.ZVar{3n}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), ee)), FM.sub_nonneg(~F, O.add(F, O.ofz(~F, QRD.Dv.r(v)), O.one(F)), O.ofp(~F, d), dv_1(~F, p, d, v, h)))))

def ofz_negsucc(~F: O.OField, +q: S.Z) -> {O.ofz(~F, S.Z.neg(S.Z.add(q, S.Zpos{S.XH{}}))) == O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))) : O.C(F)}:
  %FR.ofz_neg(~F, S.Z.add(q, S.Zpos{S.XH{}})) : {_ == O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))) : O.C(F)}
  %FR.ofz_add(~F, q, S.Zpos{S.XH{}}) : {O.neg(F, _) == O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))) : O.C(F)}
  {==}


def zfloor_neg(~F: O.OField, +p: S.Pos, +d: S.Pos, v: QRD.Dv, +h: dvok(~F, p, d, v)) -> zfl(~F, S.Zneg{p}, d, NU.zfloor.neg(v)):
  match v:
    case QRD.Dv{+q, S.Z0{}}:
      +ee = FO.sub_of_eq(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.zero(F)), dv_e(~F, p, d, QRD.Dv{q, S.Z0{}}, h))
      zfl_of(~F, S.Zneg{p}, d, S.Z.neg(q), O.neg(F, O.ofz(~F, q)), Equal.sym(O.C(F), O.neg(F, O.ofz(~F, q)), O.ofz(~F, S.Z.neg(q)), FR.ofz_neg(~F, q)),
        Inr{FO.eq_of_sub(~F, O.mul(F, O.neg(F, O.ofz(~F, q)), O.ofp(~F, d)), O.neg(F, O.ofp(~F, p)), FO.cert1(~F, O.sub(~F, O.mul(F, O.neg(F, O.ofz(~F, q)), O.ofp(~F, d)), O.neg(F, O.ofp(~F, p))), O.one(F), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.zero(F))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, q), O.ofp(~F, d)], E.ZSub{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}, E.ZNeg{E.ZVar{0n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}}}, {==}), ee))},
        FV.le_of_sub(~F, O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F)), O.mul(F, O.add(F, O.neg(F, O.ofz(~F, q)), O.one(F)), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.ofz(~F, q)), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F))), O.sub(~F, O.ofp(~F, d), O.one(F)), FO.eq_of_sub(~F, O.sub(~F, O.ofp(~F, d), O.one(F)), O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.ofz(~F, q)), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F))), FO.cert1(~F, O.sub(~F, O.sub(~F, O.ofp(~F, d), O.one(F)), O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.ofz(~F, q)), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F)))), O.neg(F, O.one(F)), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.zero(F))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, q), O.ofp(~F, d)], E.ZSub{E.ZSub{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZNeg{E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{2n}}, E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}}}, {==}), ee)), FM.sub_nonneg(~F, O.one(F), O.ofp(~F, d), ofp_ge1(~F, d)))))
    case QRD.Dv{+q, S.Zpos{+r}}:
      +ee = FO.sub_of_eq(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofp(~F, r)), dv_e(~F, p, d, QRD.Dv{q, S.Zpos{r}}, h))
      zfl_of(~F, S.Zneg{p}, d, S.Z.neg(S.Z.add(q, S.Zpos{S.XH{}})), O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), ofz_negsucc(~F, q),
        FV.le_of_sub(~F, O.mul(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.ofp(~F, d)), O.neg(F, O.ofp(~F, p)), FM.nn_eq(~F, O.sub(~F, O.neg(F, O.ofp(~F, p)), O.mul(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.ofp(~F, d))), O.sub(~F, O.ofp(~F, d), O.ofp(~F, r)), FO.eq_of_sub(~F, O.sub(~F, O.ofp(~F, d), O.ofp(~F, r)), O.sub(~F, O.neg(F, O.ofp(~F, p)), O.mul(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.ofp(~F, d))), FO.cert1(~F, O.sub(~F, O.sub(~F, O.ofp(~F, d), O.ofp(~F, r)), O.sub(~F, O.neg(F, O.ofp(~F, p)), O.mul(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.ofp(~F, d)))), O.one(F), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofp(~F, r))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, q), O.ofp(~F, r), O.ofp(~F, d)], E.ZSub{E.ZSub{E.ZVar{3n}, E.ZVar{2n}}, E.ZSub{E.ZNeg{E.ZVar{0n}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZVar{3n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), ee)), FM.sub_nonneg(~F, O.ofp(~F, r), O.ofp(~F, d), le_of_succ(~F, O.ofp(~F, r), O.ofp(~F, d), dv_1(~F, p, d, QRD.Dv{q, S.Zpos{r}}, h))))),
        FV.le_of_sub(~F, O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F)), O.mul(F, O.add(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.one(F)), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F))), O.sub(~F, O.ofp(~F, r), O.one(F)), FO.eq_of_sub(~F, O.sub(~F, O.ofp(~F, r), O.one(F)), O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F))), FO.cert1(~F, O.sub(~F, O.sub(~F, O.ofp(~F, r), O.one(F)), O.sub(~F, O.mul(F, O.add(F, O.neg(F, O.add(F, O.ofz(~F, q), O.one(F))), O.one(F)), O.ofp(~F, d)), O.add(F, O.neg(F, O.ofp(~F, p)), O.one(F)))), O.neg(F, O.one(F)), O.sub(~F, O.ofp(~F, p), O.add(F, O.mul(F, O.ofz(~F, q), O.ofp(~F, d)), O.ofp(~F, r))), FR.fring_eq(~F, [O.ofp(~F, p), O.ofz(~F, q), O.ofp(~F, r), O.ofp(~F, d)], E.ZSub{E.ZSub{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZNeg{E.ZAdd{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}}, {==}), ee)), FM.sub_nonneg(~F, O.one(F), O.ofp(~F, r), ofp_ge1(~F, r)))))
    case QRD.Dv{+q, S.Zneg{+r}}:
      FO.absurd(zfl(~F, S.Zneg{p}, d, NU.zfloor.neg(QRD.Dv{q, S.Zneg{r}})), O.lt_irrefl(F)(O.zero(F))(FO.lt_subst_r(~F, O.add(F, O.ofp(~F, r), O.neg(F, O.ofp(~F, r))), O.zero(F), O.zero(F), O.add_neg(F)(O.ofp(~F, r)), FO.pos_add(~F, O.ofp(~F, r), O.neg(F, O.ofp(~F, r)), QE.ofp_pos(~F, r), dv_0(~F, p, d, QRD.Dv{q, S.Zneg{r}}, h)))))

# zfloor(n, d) is the floor of n / d
def zfloor_ok(~F: O.OField, n: S.Z, +d: S.Pos) -> zfl(~F, n, d, NU.zfloor(n, d)):
  match n:
    case S.Z0{}:
      (Inr{FL.zero_mul(~F, O.ofp(~F, d))}, FV.le_of_sub(~F, O.add(F, O.zero(F), O.one(F)), O.mul(F, O.add(F, O.zero(F), O.one(F)), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.zero(F), O.one(F)), O.ofp(~F, d)), O.add(F, O.zero(F), O.one(F))), O.sub(~F, O.ofp(~F, d), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, d)], E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FM.sub_nonneg(~F, O.one(F), O.ofp(~F, d), ofp_ge1(~F, d)))))
    case S.Zpos{+p}:
      zfloor_pos(~F, p, d, QRD.div(p, d), div_ok(~F, p, d))
    case S.Zneg{+p}:
      zfloor_neg(~F, p, d, QRD.div(p, d), div_ok(~F, p, d))

def zfl_1(~F: O.OField, +n: S.Z, +d: S.Pos, +f: S.Z, h: zfl(~F, n, d, f)) -> O.le(~F, O.mul(F, O.ofz(~F, f), O.ofp(~F, d)), O.ofz(~F, n)):
  (a, b) = h
  a

def zfl_2(~F: O.OField, +n: S.Z, +d: S.Pos, +f: S.Z, h: zfl(~F, n, d, f)) -> O.le(~F, O.add(F, O.ofz(~F, n), O.one(F)), O.mul(F, O.add(F, O.ofz(~F, f), O.one(F)), O.ofp(~F, d))):
  (a, b) = h
  b

# Shifts
# ------

# a floor by t, doubled: by 2t of 2q
def fl_xo(~F: O.OField, +f: O.C(F), +t: O.C(F), +q: O.C(F), h1: O.le(~F, O.mul(F, f, t), q), h2: O.le(~F, O.add(F, q, O.one(F)), O.mul(F, O.add(F, f, O.one(F)), t))) -> M.Both(O.le(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, q, q)), O.le(~F, O.add(F, O.add(F, q, q), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)))):
  +s1 = FM.sub_nonneg(~F, O.mul(F, f, t), q, h1)
  +s2 = FM.sub_nonneg(~F, O.add(F, q, O.one(F)), O.mul(F, O.add(F, f, O.one(F)), t), h2)
  (FV.le_of_sub(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, q, q), FM.nn_eq(~F, O.sub(~F, O.add(F, q, q), O.mul(F, f, O.add(F, t, t))), O.add(F, O.sub(~F, q, O.mul(F, f, t)), O.sub(~F, q, O.mul(F, f, t))), FR.fring_eq(~F, [f, t, q], E.ZAdd{E.ZSub{E.ZVar{2n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{2n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZSub{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, q, O.mul(F, f, t)), O.sub(~F, q, O.mul(F, f, t)), s1, s1))),
   FV.le_of_sub(~F, O.add(F, O.add(F, q, q), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), O.add(F, O.add(F, q, q), O.one(F))), O.add(F, O.add(F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F)))), O.one(F)), FR.fring_eq(~F, [f, t, q], E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F)))), O.one(F), FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), s2, s2), FO.one_nn(~F)))))

# a floor by t, doubled: by 2t of 2q + 1
def fl_xi(~F: O.OField, +f: O.C(F), +t: O.C(F), +q: O.C(F), h1: O.le(~F, O.mul(F, f, t), q), h2: O.le(~F, O.add(F, q, O.one(F)), O.mul(F, O.add(F, f, O.one(F)), t))) -> M.Both(O.le(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, O.add(F, q, q), O.one(F))), O.le(~F, O.add(F, O.add(F, O.add(F, q, q), O.one(F)), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)))):
  +s1 = FM.sub_nonneg(~F, O.mul(F, f, t), q, h1)
  +s2 = FM.sub_nonneg(~F, O.add(F, q, O.one(F)), O.mul(F, O.add(F, f, O.one(F)), t), h2)
  (FV.le_of_sub(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, O.add(F, q, q), O.one(F)), FM.nn_eq(~F, O.sub(~F, O.add(F, O.add(F, q, q), O.one(F)), O.mul(F, f, O.add(F, t, t))), O.add(F, O.add(F, O.sub(~F, q, O.mul(F, f, t)), O.sub(~F, q, O.mul(F, f, t))), O.one(F)), FR.fring_eq(~F, [f, t, q], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{2n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{2n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, q, O.mul(F, f, t)), O.sub(~F, q, O.mul(F, f, t))), O.one(F), FO.nonneg_add(~F, O.sub(~F, q, O.mul(F, f, t)), O.sub(~F, q, O.mul(F, f, t)), s1, s1), FO.one_nn(~F)))),
   FV.le_of_sub(~F, O.add(F, O.add(F, O.add(F, q, q), O.one(F)), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), O.add(F, O.add(F, O.add(F, q, q), O.one(F)), O.one(F))), O.add(F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F)))), FR.fring_eq(~F, [f, t, q], E.ZAdd{E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), t), O.add(F, q, O.one(F))), s2, s2))))

# p itself is its floor by 1
def fl_self(~F: O.OField, +p: O.C(F)) -> M.Both(O.le(~F, O.mul(F, p, O.one(F)), p), O.le(~F, O.add(F, p, O.one(F)), O.mul(F, O.add(F, p, O.one(F)), O.one(F)))):
  (Inr{FR.fring_eq(~F, [p], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})}, Inr{FR.fring_eq(~F, [p], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==})})

# pshr(p, k) is the floor of p / 2^k
def pshr_fl(~F: O.OField, p: S.Pos, k: Nat) -> zfl(~F, S.Zpos{p}, S.Pos.pow2(k), NU.pshr(p, k)):
  match p k:
    case S.XH{} 0n:
      fl_self(~F, O.one(F))
    case S.XH{} 1n++j:
      (FV.le_of_sub(~F, O.mul(F, O.zero(F), t2(~F, 1n+j)), O.one(F), FM.nn_eq(~F, O.sub(~F, O.one(F), O.mul(F, O.zero(F), t2(~F, 1n+j))), O.one(F), FR.fring_eq(~F, [t2(~F, 1n+j)], E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}}, {==}), FO.one_nn(~F))),
       FV.le_rw_r(~F, O.add(F, O.one(F), O.one(F)), O.add(F, t2(~F, j), t2(~F, j)), O.mul(F, O.add(F, O.zero(F), O.one(F)), t2(~F, 1n+j)), FR.fring_eq(~F, [t2(~F, j)], E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}}, {==}), le_dbl(~F, O.one(F), t2(~F, j), ofp_ge1(~F, S.Pos.pow2(j)))))
    case S.XO{+q} 0n:
      fl_self(~F, O.ofp(~F, S.XO{q}))
    case S.XO{+q} 1n++j:
      +h = pshr_fl(~F, q, j)
      fl_xo(~F, O.ofz(~F, NU.pshr(q, j)), t2(~F, j), O.ofp(~F, q), zfl_1(~F, S.Zpos{q}, S.Pos.pow2(j), NU.pshr(q, j), h), zfl_2(~F, S.Zpos{q}, S.Pos.pow2(j), NU.pshr(q, j), h))
    case S.XI{+q} 0n:
      fl_self(~F, O.ofp(~F, S.XI{q}))
    case S.XI{+q} 1n++j:
      +h = pshr_fl(~F, q, j)
      fl_xi(~F, O.ofz(~F, NU.pshr(q, j)), t2(~F, j), O.ofp(~F, q), zfl_1(~F, S.Zpos{q}, S.Pos.pow2(j), NU.pshr(q, j), h), zfl_2(~F, S.Zpos{q}, S.Pos.pow2(j), NU.pshr(q, j), h))

def sub0(j: Nat) -> {Nat.sub(j, 0n) == j : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      {==}

# the floor of (P + t) / 2t is within t of P / 2t, scaled: |2t f - P| <= t
def psr_core(~F: O.OField, +f: O.C(F), +t: O.C(F), +p: O.C(F), h1: O.le(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, p, t)), h2: O.le(~F, O.add(F, O.add(F, p, t), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)))) -> M.bnd(~F, O.sub(~F, O.mul(F, f, O.add(F, t, t)), p), t):
  (FM.nn_eq(~F, O.sub(~F, t, O.sub(~F, O.mul(F, f, O.add(F, t, t)), p)), O.sub(~F, O.add(F, p, t), O.mul(F, f, O.add(F, t, t))), FR.fring_eq(~F, [f, t, p], E.ZSub{E.ZAdd{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}}, E.ZSub{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{2n}}}, {==}), FM.sub_nonneg(~F, O.mul(F, f, O.add(F, t, t)), O.add(F, p, t), h1)),
   FM.nn_eq(~F, O.add(F, t, O.sub(~F, O.mul(F, f, O.add(F, t, t)), p)), O.add(F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), O.add(F, O.add(F, p, t), O.one(F))), O.one(F)), FR.fring_eq(~F, [f, t, p], E.ZAdd{E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZVar{2n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), O.add(F, O.add(F, p, t), O.one(F))), O.one(F), FM.sub_nonneg(~F, O.add(F, O.add(F, p, t), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, t, t)), h2), FO.one_nn(~F))))

def psr_go(~F: O.OField, +p: S.Pos, +j: Nat) -> M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j)), t2(~F, 1n+j)), O.ofp(~F, p)), t2(~F, j)):
  +h = pshr_fl(~F, S.Pos.add(p, S.Pos.pow2(j)), 1n+j)
  psr_core(~F, O.ofz(~F, NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j)), t2(~F, j), O.ofp(~F, p),
    (%Equal.sym(O.C(F), O.add(F, O.ofp(~F, p), t2(~F, j)), O.ofp(~F, S.Pos.add(p, S.Pos.pow2(j))), ofp_add(~F, p, S.Pos.pow2(j))) : O.le(~F, O.mul(F, O.ofz(~F, NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), _)
      zfl_1(~F, S.Zpos{S.Pos.add(p, S.Pos.pow2(j))}, S.Pos.pow2(1n+j), NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j), h)),
    (%Equal.sym(O.C(F), O.add(F, O.ofp(~F, p), t2(~F, j)), O.ofp(~F, S.Pos.add(p, S.Pos.pow2(j))), ofp_add(~F, p, S.Pos.pow2(j))) : O.le(~F, O.add(F, _, O.one(F)), O.mul(F, O.add(F, O.ofz(~F, NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j)), O.one(F)), O.add(F, t2(~F, j), t2(~F, j))))
      zfl_2(~F, S.Zpos{S.Pos.add(p, S.Pos.pow2(j))}, S.Pos.pow2(1n+j), NU.pshr(S.Pos.add(p, S.Pos.pow2(j)), 1n+j), h)))

# p / 2^(j+1) rounded to nearest: |2^(j+1) f - p| <= 2^j
def psr_bnd(~F: O.OField, +p: S.Pos, +j: Nat) -> M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.pshr_round(p, 1n+j)), t2(~F, 1n+j)), O.ofp(~F, p)), t2(~F, j)):
  %Equal.sym(Nat, Nat.sub(j, 0n), j, sub0(j)) : M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.pshr(S.Pos.add(p, S.Pos.pow2(_)), 1n+j)), t2(~F, 1n+j)), O.ofp(~F, p)), t2(~F, j))
  psr_go(~F, p, j)

# m / 2^(j+1) rounded to nearest: |2^(j+1) f - m| <= 2^j
def zsr(~F: O.OField, m: S.Z, +j: Nat) -> M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), t2(~F, 1n+j)), O.ofz(~F, m)), t2(~F, j)):
  match m:
    case S.Z0{}:
      KB.bnd_val(~F, O.zero(F), O.sub(~F, O.mul(F, O.zero(F), t2(~F, 1n+j)), O.zero(F)), t2(~F, j), FR.fring_eq(~F, [t2(~F, 1n+j)], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==}), FM.bnd_zero(~F, t2(~F, j), ofp_nn(~F, S.Pos.pow2(j))))
    case S.Zpos{+p}:
      psr_bnd(~F, p, j)
    case S.Zneg{+p}:
      %FR.ofz_neg(~F, NU.pshr_round(p, 1n+j)) : M.bnd(~F, O.sub(~F, O.mul(F, _, t2(~F, 1n+j)), O.neg(F, O.ofp(~F, p))), t2(~F, j))
      KB.bnd_val(~F, O.neg(F, O.sub(~F, O.mul(F, O.ofz(~F, NU.pshr_round(p, 1n+j)), t2(~F, 1n+j)), O.ofp(~F, p))), O.sub(~F, O.mul(F, O.neg(F, O.ofz(~F, NU.pshr_round(p, 1n+j))), t2(~F, 1n+j)), O.neg(F, O.ofp(~F, p))), t2(~F, j), FR.fring_eq(~F, [O.ofz(~F, NU.pshr_round(p, 1n+j)), t2(~F, 1n+j), O.ofp(~F, p)], E.ZNeg{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZSub{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZNeg{E.ZVar{2n}}}, {==}), FM.bnd_neg(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.pshr_round(p, 1n+j)), t2(~F, 1n+j)), O.ofp(~F, p)), t2(~F, j), psr_bnd(~F, p, j)))

# Rounding to a multiple of 2^-p
# ------------------------------

def sub_succ(e: Nat, p: Nat, h: {KA.natle(e, p) == False{} : Bool}) -> {Nat.sub(e, p) == 1n+Nat.sub(e, 1n+p) : Nat}:
  match e p:
    case 0n 0n:
      FO.absurd({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n++q:
      FO.absurd({Nat.sub(0n, 1n+q) == 1n+Nat.sub(0n, 2n+q) : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++i 0n:
      Equal.cong(Nat, Nat, x => 1n+x, i, Nat.sub(i, 0n), Equal.sym(Nat, Nat.sub(i, 0n), i, sub0(i)))
    case 1n++i 1n++q:
      sub_succ(i, q, h)

def add_sub(e: Nat, p: Nat, h: {KA.natle(e, p) == False{} : Bool}) -> {Nat.add(p, Nat.sub(e, p)) == e : Nat}:
  match e p:
    case 0n 0n:
      FO.absurd({Nat.add(0n, Nat.sub(0n, 0n)) == 0n : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n++q:
      FO.absurd({Nat.add(1n+q, Nat.sub(0n, 1n+q)) == 0n : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++i 0n:
      {==}
    case 1n++i 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, Nat.sub(i, q)), i, add_sub(i, q, h))

# |a| <= s and 0 <= c give |a c| <= s c
def bnd_scale(~F: O.OField, +a: O.C(F), +s: O.C(F), +c: O.C(F), +hc: O.le(~F, O.zero(F), c), h: M.bnd(~F, a, s)) -> M.bnd(~F, O.mul(F, a, c), O.mul(F, s, c)):
  FM.bnd_mul(~F, a, s, c, c, h, FV.bnd_self(~F, c, hc))

def inv_nn(~F: O.OField, +p: S.Pos) -> O.le(~F, O.zero(F), O.inv(F, O.ofp(~F, p))):
  FO.lt_le(~F, O.zero(F), O.inv(F, O.ofp(~F, p)), FO.inv_pos(~F, O.ofp(~F, p), QE.ofp_pos(~F, p)))


# m / 2^(p+j+1) rounded to a multiple of 2^-p is within 2^-(p+1)
def rnd_core(~F: O.OField, +m: S.Z, +p: Nat, +j: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, S.D{NU.zshr_round(m, 1n+j), p}), M.ofd(~F, S.D{m, Nat.add(p, 1n+j)})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p})):
  +r1 = QE.ofp_rel(~F, S.Pos.pow2(p))
  +r2 = QE.ofp_rel(~F, S.Pos.pow2(Nat.add(p, 1n+j)))
  +r3 = FO.sub_of_eq(~F, t2(~F, Nat.add(p, 1n+j)), O.mul(F, t2(~F, p), O.add(F, t2(~F, j), t2(~F, j))), Equal.sym(O.C(F), O.mul(F, t2(~F, p), O.add(F, t2(~F, j), t2(~F, j))), t2(~F, Nat.add(p, 1n+j)), t2_add(~F, p, 1n+j)))
  +s1 = QE.ofp_rel(~F, S.Pos.pow2(1n+p))
  KB.bnd_val(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), O.ofz(~F, m)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, p))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, Nat.add(p, 1n+j))))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+p))),
    FO.eq_of_sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), O.ofz(~F, m)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, p))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, Nat.add(p, 1n+j))))), FO.cert3(~F, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), O.ofz(~F, m)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, p))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, Nat.add(p, 1n+j)))))), O.neg(F, O.mul(F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.add(F, t2(~F, j), t2(~F, j)))), O.sub(~F, O.mul(F, t2(~F, p), O.inv(F, t2(~F, p))), O.one(F)), O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, p))), O.sub(~F, O.mul(F, t2(~F, Nat.add(p, 1n+j)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.inv(F, t2(~F, p)))), O.sub(~F, t2(~F, Nat.add(p, 1n+j)), O.mul(F, t2(~F, p), O.add(F, t2(~F, j), t2(~F, j)))), FR.fring_eq(~F, [O.ofz(~F, NU.zshr_round(m, 1n+j)), O.ofz(~F, m), t2(~F, p), t2(~F, j), t2(~F, Nat.add(p, 1n+j)), O.inv(F, t2(~F, p)), O.inv(F, t2(~F, Nat.add(p, 1n+j))), O.inv(F, t2(~F, 1n+p))], E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}}, E.ZVar{1n}}, E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{6n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{6n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{6n}}, E.ZVar{5n}}}, E.ZSub{E.ZVar{4n}, E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}}}}}, {==}), r1, r2, r3)),
    FM.bnd_eq(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), O.ofz(~F, m)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.mul(F, t2(~F, j), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+p))),
      FO.eq_of_sub(~F, O.mul(F, t2(~F, j), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+p))), FO.cert3(~F, O.sub(~F, O.mul(F, t2(~F, j), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+p)))), O.neg(F, O.mul(F, t2(~F, j), O.inv(F, t2(~F, Nat.add(p, 1n+j))))), O.sub(~F, O.mul(F, O.add(F, t2(~F, p), t2(~F, p)), O.inv(F, t2(~F, 1n+p))), O.one(F)), O.inv(F, t2(~F, 1n+p)), O.sub(~F, O.mul(F, t2(~F, Nat.add(p, 1n+j)), O.inv(F, t2(~F, Nat.add(p, 1n+j)))), O.one(F)), O.neg(F, O.mul(F, O.inv(F, t2(~F, 1n+p)), O.inv(F, t2(~F, Nat.add(p, 1n+j))))), O.sub(~F, t2(~F, Nat.add(p, 1n+j)), O.mul(F, t2(~F, p), O.add(F, t2(~F, j), t2(~F, j)))), FR.fring_eq(~F, [O.ofz(~F, NU.zshr_round(m, 1n+j)), O.ofz(~F, m), t2(~F, p), t2(~F, j), t2(~F, Nat.add(p, 1n+j)), O.inv(F, t2(~F, p)), O.inv(F, t2(~F, Nat.add(p, 1n+j))), O.inv(F, t2(~F, 1n+p))], E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{6n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{7n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZVar{3n}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{7n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZVar{7n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{7n}, E.ZVar{6n}}}, E.ZSub{E.ZVar{4n}, E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}}}}}, {==}), s1, r2, r3)),
      bnd_scale(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), O.add(F, t2(~F, j), t2(~F, j))), O.ofz(~F, m)), t2(~F, j), O.inv(F, t2(~F, Nat.add(p, 1n+j))), inv_nn(~F, S.Pos.pow2(Nat.add(p, 1n+j))), zsr(~F, m, j))))

def dround_go(~F: O.OField, le: Bool, +m: S.Z, +e: Nat, +p: Nat, +h: {KA.natle(e, p) == le : Bool}) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dround.go(le, S.D{m, e}, p)), M.ofd(~F, S.D{m, e})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p})):
  match le:
    case True{}:
      KB.bnd_subself(~F, M.ofd(~F, S.D{m, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p}), FO.lt_le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p}), DM.dpos(~F, S.XH{}, 1n+p)))
    case False{}:
      %add_sub(e, p, h) : M.bnd(~F, O.sub(~F, M.ofd(~F, S.D{NU.zshr_round(m, Nat.sub(e, p)), p}), M.ofd(~F, S.D{m, _})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p}))
      %Equal.sym(Nat, Nat.sub(e, p), 1n+Nat.sub(e, 1n+p), sub_succ(e, p, h)) : M.bnd(~F, O.sub(~F, M.ofd(~F, S.D{NU.zshr_round(m, _), p}), M.ofd(~F, S.D{m, Nat.add(p, Nat.sub(e, p))})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p}))
      %Equal.sym(Nat, Nat.sub(e, p), 1n+Nat.sub(e, 1n+p), sub_succ(e, p, h)) : M.bnd(~F, O.sub(~F, M.ofd(~F, S.D{NU.zshr_round(m, 1n+Nat.sub(e, 1n+p)), p}), M.ofd(~F, S.D{m, Nat.add(p, _)})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p}))
      rnd_core(~F, m, p, Nat.sub(e, 1n+p))

# |dround(x, p) - x| <= 2^-(p+1)
def dround_err(~F: O.OField, x: S.D, +p: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dround(x, p)), M.ofd(~F, x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p})):
  match x:
    case S.D{+m, +e}:
      dround_go(~F, KA.natle(e, p), m, e, p, {==})

# Rounding to b significant bits
# ------------------------------

def sub_add_le(x: Nat, y: Nat, h: {KA.natle(y, x) == True{} : Bool}) -> {Nat.add(Nat.sub(x, y), y) == x : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++j:
      FO.absurd({Nat.add(Nat.sub(0n, 1n+j), 1n+j) == 0n : Nat}, KA.ft(h))
    case 1n++i 0n:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(i, 0n), i, Equal.sym(Nat, i, Nat.add(i, 0n), LN.add_zero(i)))
    case 1n++i 1n++j:
      %LN.add_succ(Nat.sub(i, j), j) : {_ == 1n+i : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(i, j), j), i, sub_add_le(i, j, h))


# z / 2^c is (z 2^k) / 2^(c + k)
def valA(~F: O.OField, +z: S.Z, +c: Nat, +k: Nat) -> {M.ofd(~F, S.D{z, c}) == O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, k)), O.inv(F, t2(~F, Nat.add(c, k)))) : O.C(F)}:
  FO.eq_of_sub(~F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, c))), O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, k)), O.inv(F, t2(~F, Nat.add(c, k)))), FO.cert3(~F, O.sub(~F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, c))), O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, k)), O.inv(F, t2(~F, Nat.add(c, k))))), O.mul(F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, Nat.add(c, k)))), t2(~F, k)), O.sub(~F, O.mul(F, t2(~F, c), O.inv(F, t2(~F, c))), O.one(F)), O.neg(F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, c)))), O.sub(~F, O.mul(F, t2(~F, Nat.add(c, k)), O.inv(F, t2(~F, Nat.add(c, k)))), O.one(F)), O.mul(F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, Nat.add(c, k)))), O.inv(F, t2(~F, c))), O.sub(~F, t2(~F, Nat.add(c, k)), O.mul(F, t2(~F, c), t2(~F, k))), FR.fring_eq(~F, [O.ofz(~F, z), t2(~F, c), t2(~F, k), t2(~F, Nat.add(c, k)), O.inv(F, t2(~F, c)), O.inv(F, t2(~F, Nat.add(c, k)))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{5n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{4n}}, E.ZSub{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(c)), QE.ofp_rel(~F, S.Pos.pow2(Nat.add(c, k))), FO.sub_of_eq(~F, t2(~F, Nat.add(c, k)), O.mul(F, t2(~F, c), t2(~F, k)), Equal.sym(O.C(F), O.mul(F, t2(~F, c), t2(~F, k)), t2(~F, Nat.add(c, k)), t2_add(~F, c, k)))))


# (z 2^c) / 1 is (z 2^(c + e)) / 2^e
def valB(~F: O.OField, +z: S.Z, +c: Nat, +e: Nat) -> {M.ofd(~F, S.D{S.Z.mul(z, S.Zpos{S.Pos.pow2(c)}), 0n}) == O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, Nat.add(c, e))), O.inv(F, t2(~F, e))) : O.C(F)}:
  %FR.ofz_mul(~F, z, S.Zpos{S.Pos.pow2(c)}) : {O.mul(F, _, O.inv(F, O.one(F))) == O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, Nat.add(c, e))), O.inv(F, t2(~F, e))) : O.C(F)}
  FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, c)), O.inv(F, O.one(F))), O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, Nat.add(c, e))), O.inv(F, t2(~F, e))), FO.cert3(~F, O.sub(~F, O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, c)), O.inv(F, O.one(F))), O.mul(F, O.mul(F, O.ofz(~F, z), t2(~F, Nat.add(c, e))), O.inv(F, t2(~F, e)))), O.mul(F, O.ofz(~F, z), t2(~F, c)), O.sub(~F, O.mul(F, O.one(F), O.inv(F, O.one(F))), O.one(F)), O.neg(F, O.mul(F, O.ofz(~F, z), t2(~F, c))), O.sub(~F, O.mul(F, t2(~F, e), O.inv(F, t2(~F, e))), O.one(F)), O.neg(F, O.mul(F, O.ofz(~F, z), O.inv(F, t2(~F, e)))), O.sub(~F, t2(~F, Nat.add(c, e)), O.mul(F, t2(~F, c), t2(~F, e))), FR.fring_eq(~F, [O.ofz(~F, z), t2(~F, c), t2(~F, e), t2(~F, Nat.add(c, e)), O.inv(F, O.one(F)), O.inv(F, t2(~F, e))], E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{4n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}, E.ZSub{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}), QE.ofp_rel(~F, S.XH{}), QE.ofp_rel(~F, S.Pos.pow2(e)), FO.sub_of_eq(~F, t2(~F, Nat.add(c, e)), O.mul(F, t2(~F, c), t2(~F, e)), Equal.sym(O.C(F), O.mul(F, t2(~F, c), t2(~F, e)), t2(~F, Nat.add(c, e)), t2_add(~F, c, e)))))


# a rounding's error from its floor: with v = (r T) / 2^e, |r T - m| <= 2^j,
# T = 2 2^j and 2^b T <= 2 a, |v - m / 2^e| <= (a / 2^e) 2^-b
def dsig_core(~F: O.OField, +v: O.C(F), +r: O.C(F), +mv: O.C(F), +tt: O.C(F), +tj: O.C(F), +tb: O.C(F), +a: O.C(F), +ie: O.C(F), +ib: O.C(F), +ev: {v == O.mul(F, O.mul(F, r, tt), ie) : O.C(F)}, +et: {tt == O.add(F, tj, tj) : O.C(F)}, hz: M.bnd(~F, O.sub(~F, O.mul(F, r, tt), mv), tj), hs: O.le(~F, O.mul(F, tb, tt), O.add(F, a, a)), +hie: O.le(~F, O.zero(F), ie), +hib: O.le(~F, O.zero(F), ib), +rb: {O.sub(~F, O.mul(F, tb, ib), O.one(F)) == O.zero(F) : O.C(F)}) -> M.bnd(~F, O.sub(~F, v, O.mul(F, mv, ie)), O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib))):
  KB.bnd_val(~F, O.mul(F, O.sub(~F, O.mul(F, r, tt), mv), ie), O.sub(~F, v, O.mul(F, mv, ie)), O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib)),
    FO.eq_of_sub(~F, O.mul(F, O.sub(~F, O.mul(F, r, tt), mv), ie), O.sub(~F, v, O.mul(F, mv, ie)), FO.cert1(~F, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, r, tt), mv), ie), O.sub(~F, v, O.mul(F, mv, ie))), O.neg(F, O.one(F)), O.sub(~F, v, O.mul(F, O.mul(F, r, tt), ie)), FR.fring_eq(~F, [v, r, mv, tt, tj, tb, a, ie, ib], E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}, E.ZVar{7n}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{2n}, E.ZVar{7n}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{7n}}}}, {==}), FO.sub_of_eq(~F, v, O.mul(F, O.mul(F, r, tt), ie), ev))),
    FM.bnd_mono(~F, O.mul(F, O.sub(~F, O.mul(F, r, tt), mv), ie), O.mul(F, tj, ie), O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib)), bnd_scale(~F, O.sub(~F, O.mul(F, r, tt), mv), tj, ie, hie, hz),
      FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib)), O.mul(F, tj, ie)), O.mul(F, O.mul(F, ie, ib), O.sub(~F, a, O.mul(F, tb, tj))), FO.eq_of_sub(~F, O.mul(F, O.mul(F, ie, ib), O.sub(~F, a, O.mul(F, tb, tj))), O.sub(~F, O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib)), O.mul(F, tj, ie)), FO.cert1(~F, O.sub(~F, O.mul(F, O.mul(F, ie, ib), O.sub(~F, a, O.mul(F, tb, tj))), O.sub(~F, O.mul(F, O.mul(F, a, ie), O.mul(F, O.one(F), ib)), O.mul(F, tj, ie))), O.neg(F, O.mul(F, tj, ie)), O.sub(~F, O.mul(F, tb, ib), O.one(F)), FR.fring_eq(~F, [v, r, mv, tt, tj, tb, a, ie, ib], E.ZSub{E.ZMul{E.ZMul{E.ZVar{7n}, E.ZVar{8n}}, E.ZSub{E.ZVar{6n}, E.ZMul{E.ZVar{5n}, E.ZVar{4n}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{8n}}}, E.ZMul{E.ZVar{4n}, E.ZVar{7n}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{4n}, E.ZVar{7n}}}, E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), rb)),
        FO.mul_nonneg(~F, O.mul(F, ie, ib), O.sub(~F, a, O.mul(F, tb, tj)), FO.mul_nonneg(~F, ie, ib, hie, hib), FM.twice_nonneg(~F, O.sub(~F, a, O.mul(F, tb, tj)), FM.nn_eq(~F, O.add(F, O.sub(~F, a, O.mul(F, tb, tj)), O.sub(~F, a, O.mul(F, tb, tj))), O.sub(~F, O.add(F, a, a), O.mul(F, tb, tt)), FO.eq_of_sub(~F, O.sub(~F, O.add(F, a, a), O.mul(F, tb, tt)), O.add(F, O.sub(~F, a, O.mul(F, tb, tj)), O.sub(~F, a, O.mul(F, tb, tj))), FO.cert1(~F, O.sub(~F, O.sub(~F, O.add(F, a, a), O.mul(F, tb, tt)), O.add(F, O.sub(~F, a, O.mul(F, tb, tj)), O.sub(~F, a, O.mul(F, tb, tj)))), O.neg(F, tb), O.sub(~F, tt, O.add(F, tj, tj)), FR.fring_eq(~F, [v, r, mv, tt, tj, tb, a, ie, ib], E.ZSub{E.ZSub{E.ZAdd{E.ZVar{6n}, E.ZVar{6n}}, E.ZMul{E.ZVar{5n}, E.ZVar{3n}}}, E.ZAdd{E.ZSub{E.ZVar{6n}, E.ZMul{E.ZVar{5n}, E.ZVar{4n}}}, E.ZSub{E.ZVar{6n}, E.ZMul{E.ZVar{5n}, E.ZVar{4n}}}}}, E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZSub{E.ZVar{3n}, E.ZAdd{E.ZVar{4n}, E.ZVar{4n}}}}, {==}), FO.sub_of_eq(~F, tt, O.add(F, tj, tj), et))), FM.sub_nonneg(~F, O.mul(F, tb, tt), O.add(F, a, a), hs)))))))

# the value dsig's shift produces: (round(m / 2^k) 2^k) / 2^e
def dsh_val(~F: O.OField, le: Bool, +m: S.Z, +e: Nat, +k: Nat, h: {KA.natle(k, e) == le : Bool}) -> {M.ofd(~F, NU.dsig.sh(le, m, e, k)) == O.mul(F, O.mul(F, O.ofz(~F, NU.zshr_round(m, k)), t2(~F, k)), O.inv(F, t2(~F, e))) : O.C(F)}:
  match le:
    case True{}:
      %sub_add_le(e, k, h) : {M.ofd(~F, S.D{NU.zshr_round(m, k), Nat.sub(e, k)}) == O.mul(F, O.mul(F, O.ofz(~F, NU.zshr_round(m, k)), t2(~F, k)), O.inv(F, t2(~F, _))) : O.C(F)}
      valA(~F, NU.zshr_round(m, k), Nat.sub(e, k), k)
    case False{}:
      %sub_add_le(k, e, KA.natle_flip(k, e, h)) : {M.ofd(~F, S.D{S.Z.mul(NU.zshr_round(m, k), S.Zpos{S.Pos.pow2(Nat.sub(k, e))}), 0n}) == O.mul(F, O.mul(F, O.ofz(~F, NU.zshr_round(m, k)), t2(~F, _)), O.inv(F, t2(~F, e))) : O.C(F)}
      valB(~F, NU.zshr_round(m, k), Nat.sub(k, e), e)

# zsr at k = j + 1
def zsr_k(~F: O.OField, +m: S.Z, +k: Nat, +j: Nat, +hk: {k == 1n+j : Nat}) -> M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, k)), t2(~F, k)), O.ofz(~F, m)), t2(~F, j)):
  %Equal.sym(Nat, k, 1n+j, hk) : M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, _)), t2(~F, k)), O.ofz(~F, m)), t2(~F, j))
  %Equal.sym(Nat, k, 1n+j, hk) : M.bnd(~F, O.sub(~F, O.mul(F, O.ofz(~F, NU.zshr_round(m, 1n+j)), t2(~F, _)), O.ofz(~F, m)), t2(~F, j))
  zsr(~F, m, j)

# 2^b 2^(size p - b) <= 2 p
def size_k(~F: O.OField, +p: S.Pos, +b: Nat, +h: {KA.natle(QRD.size(p), b) == False{} : Bool}) -> O.le(~F, O.mul(F, t2(~F, b), t2(~F, Nat.sub(QRD.size(p), b))), O.add(F, O.ofp(~F, p), O.ofp(~F, p))):
  %Equal.sym(O.C(F), O.mul(F, t2(~F, b), t2(~F, Nat.sub(QRD.size(p), b))), t2(~F, Nat.add(b, Nat.sub(QRD.size(p), b))), t2_add(~F, b, Nat.sub(QRD.size(p), b))) : O.le(~F, _, O.add(F, O.ofp(~F, p), O.ofp(~F, p)))
  %Equal.sym(Nat, Nat.add(b, Nat.sub(QRD.size(p), b)), QRD.size(p), add_sub(QRD.size(p), b, h)) : O.le(~F, t2(~F, _), O.add(F, O.ofp(~F, p), O.ofp(~F, p)))
  size_lo(~F, p)

def bound_nn(~F: O.OField, +m: S.Z, +e: Nat, +b: Nat) -> O.le(~F, O.zero(F), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  FO.mul_nonneg(~F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), DM.dabs_nonneg(~F, S.D{m, e}), FO.lt_le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), DM.dpos(~F, S.XH{}, b)))

# m nonzero with |m| = p
def dsig_go(~F: O.OField, le: Bool, +m: S.Z, +p: S.Pos, +e: Nat, +b: Nat, +h: {KA.natle(QRD.size(p), b) == le : Bool}, ea: {O.ofz(~F, M.zabs(m)) == O.ofp(~F, p) : O.C(F)}, hn: {S.D{m, e} == NU.dznorm(S.D{m, e}) : S.D}) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig.go(le, S.D{m, e}, Nat.sub(QRD.size(p), b))), M.ofd(~F, S.D{m, e})), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  match le:
    case True{}:
      %hn : M.bnd(~F, O.sub(~F, M.ofd(~F, _), M.ofd(~F, S.D{m, e})), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})))
      KB.bnd_subself(~F, M.ofd(~F, S.D{m, e}), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), bound_nn(~F, m, e, b))
    case False{}:
      +k = Nat.sub(QRD.size(p), b)
      +j = Nat.sub(QRD.size(p), 1n+b)
      +hk = sub_succ(QRD.size(p), b, h)
      %Equal.sym(O.C(F), O.ofz(~F, M.zabs(m)), O.ofp(~F, p), ea) : M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig.sh(KA.natle(k, e), m, e, k)), M.ofd(~F, S.D{m, e})), O.mul(F, O.mul(F, _, O.inv(F, t2(~F, e))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})))
      dsig_core(~F, M.ofd(~F, NU.dsig.sh(KA.natle(k, e), m, e, k)), O.ofz(~F, NU.zshr_round(m, k)), O.ofz(~F, m), t2(~F, k), t2(~F, j), t2(~F, b), O.ofp(~F, p), O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b)),
        dsh_val(~F, KA.natle(k, e), m, e, k, {==}), Equal.cong(Nat, O.C(F), z => t2(~F, z), k, 1n+j, hk), zsr_k(~F, m, k, j, hk), size_k(~F, p, b, h), inv_nn(~F, S.Pos.pow2(e)), inv_nn(~F, S.Pos.pow2(b)), QE.ofp_rel(~F, S.Pos.pow2(b)))

def dsig_z2(~F: O.OField, le: Bool, +e: Nat, +k: Nat, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig.sh(le, S.Z0{}, e, k)), M.ofd(~F, S.D{S.Z0{}, e})), O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  match le:
    case True{}:
      KB.bnd_val(~F, O.zero(F), O.sub(~F, M.ofd(~F, S.D{S.Z0{}, Nat.sub(e, k)}), M.ofd(~F, S.D{S.Z0{}, e})), O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), FR.fring_eq(~F, [O.inv(F, t2(~F, Nat.sub(e, k))), O.inv(F, t2(~F, e))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, {==}), FM.bnd_zero(~F, O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), bound_nn(~F, S.Z0{}, e, b)))
    case False{}:
      KB.bnd_val(~F, O.zero(F), O.sub(~F, M.ofd(~F, S.D{S.Z0{}, 0n}), M.ofd(~F, S.D{S.Z0{}, e})), O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), FR.fring_eq(~F, [O.inv(F, O.one(F)), O.inv(F, t2(~F, e))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, {==}), FM.bnd_zero(~F, O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), bound_nn(~F, S.Z0{}, e, b)))

def dsig_z(~F: O.OField, le: Bool, +e: Nat, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig.go(le, S.D{S.Z0{}, e}, Nat.sub(1n, b))), M.ofd(~F, S.D{S.Z0{}, e})), O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  match le:
    case True{}:
      KB.bnd_val(~F, O.zero(F), O.sub(~F, M.ofd(~F, S.D{S.Z0{}, 0n}), M.ofd(~F, S.D{S.Z0{}, e})), O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), FR.fring_eq(~F, [O.inv(F, O.one(F)), O.inv(F, t2(~F, e))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, {==}), FM.bnd_zero(~F, O.mul(F, M.ofd(~F, S.D{S.Z0{}, e}), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), bound_nn(~F, S.Z0{}, e, b)))
    case False{}:
      dsig_z2(~F, KA.natle(Nat.sub(1n, b), e), e, Nat.sub(1n, b), b)

# |dsig(x, b) - x| <= |x| 2^-b
def dsig_err(~F: O.OField, x: S.D, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig(x, b)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  match x:
    case S.D{S.Z0{}, +e}:
      dsig_z(~F, KA.natle(1n, b), e, b)
    case S.D{S.Zpos{+p}, +e}:
      dsig_go(~F, KA.natle(QRD.size(p), b), S.Zpos{p}, p, e, b, {==}, {==}, {==})
    case S.D{S.Zneg{+p}, +e}:
      dsig_go(~F, KA.natle(QRD.size(p), b), S.Zneg{p}, p, e, b, {==}, {==}, {==})

# The exponent a rational is rounded at
# -------------------------------------

def sub_zero(s: Nat, t: Nat, h: {KA.natle(t, s) == False{} : Bool}) -> {Nat.sub(s, t) == 0n : Nat}:
  match s t:
    case 0n 0n:
      FO.absurd({Nat.sub(0n, 0n) == 0n : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+i 0n:
      FO.absurd({Nat.sub(1n+i, 0n) == 0n : Nat}, KA.ft(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n+q:
      {==}
    case 1n+i 1n+q:
      sub_zero(i, q, h)

def t2_mono(~F: O.OField, +a: Nat, +c: Nat) -> O.le(~F, t2(~F, a), t2(~F, Nat.add(c, a))):
  %t2_add(~F, c, a) : O.le(~F, t2(~F, a), _)
  FV.le_of_sub(~F, t2(~F, a), O.mul(F, t2(~F, c), t2(~F, a)), FM.nn_eq(~F, O.sub(~F, O.mul(F, t2(~F, c), t2(~F, a)), t2(~F, a)), O.mul(F, O.sub(~F, t2(~F, c), O.one(F)), t2(~F, a)), FR.fring_eq(~F, [t2(~F, c), t2(~F, a)], E.ZMul{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}), FO.mul_nonneg(~F, O.sub(~F, t2(~F, c), O.one(F)), t2(~F, a), FM.sub_nonneg(~F, O.one(F), t2(~F, c), ofp_ge1(~F, S.Pos.pow2(c))), ofp_nn(~F, S.Pos.pow2(a)))))


def ts_split(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat, +h: {KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))) == True{} : Bool}) -> {O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), t2(~F, QRD.size(p))) == t2(~F, Nat.add(b, QRD.size(d))) : O.C(F)}:
  %sub_add_le(Nat.add(b, QRD.size(d)), QRD.size(p), h) : {O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), t2(~F, QRD.size(p))) == t2(~F, _) : O.C(F)}
  t2_add(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)), QRD.size(p))

# b + size d >= size p
def qb_hi(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat, +h: {KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))) == True{} : Bool}) -> O.le(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))):
  FV.le_of_sub(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b))), O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p))))),
    FO.eq_of_sub(~F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b))), FO.cert2(~F, O.sub(~F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b)))), O.one(F), O.sub(~F, O.mul(F, t2(~F, b), t2(~F, QRD.size(d))), t2(~F, Nat.add(b, QRD.size(d)))), O.neg(F, O.one(F)), O.sub(~F, O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), t2(~F, QRD.size(p))), t2(~F, Nat.add(b, QRD.size(d)))), FR.fring_eq(~F, [O.ofp(~F, d), O.ofp(~F, p), t2(~F, b), t2(~F, QRD.size(d)), t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d))), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{3n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{6n}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{4n}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{6n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{5n}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{4n}}, E.ZVar{5n}}}}, {==}), FO.sub_of_eq(~F, O.mul(F, t2(~F, b), t2(~F, QRD.size(d))), t2(~F, Nat.add(b, QRD.size(d))), t2_add(~F, b, QRD.size(d))), FO.sub_of_eq(~F, O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), t2(~F, QRD.size(p))), t2(~F, Nat.add(b, QRD.size(d))), ts_split(~F, p, d, b, h)))),
    FO.nonneg_add(~F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p)))),
      FO.mul_nonneg(~F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d)), ofp_nn(~F, S.Pos.pow2(b)), FM.sub_nonneg(~F, O.ofp(~F, d), t2(~F, QRD.size(d)), le_of_succ(~F, O.ofp(~F, d), t2(~F, QRD.size(d)), size_hi(~F, d)))),
      FO.mul_nonneg(~F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p))), ofp_nn(~F, S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), FM.sub_nonneg(~F, t2(~F, QRD.size(p)), O.add(F, O.ofp(~F, p), O.ofp(~F, p)), size_lo(~F, p))))))

def ts_mono(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat, +h: {KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))) == False{} : Bool}) -> O.le(~F, t2(~F, Nat.add(b, QRD.size(d))), t2(~F, QRD.size(p))):
  %sub_add_le(QRD.size(p), Nat.add(b, QRD.size(d)), KA.natle_flip(QRD.size(p), Nat.add(b, QRD.size(d)), h)) : O.le(~F, t2(~F, Nat.add(b, QRD.size(d))), t2(~F, _))
  t2_mono(~F, Nat.add(b, QRD.size(d)), Nat.sub(QRD.size(p), Nat.add(b, QRD.size(d))))


# b + size d < size p: the exponent is 0
def qb_lo(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat, +h: {KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))) == False{} : Bool}) -> O.le(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))):
  %Equal.sym(Nat, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)), 0n, sub_zero(Nat.add(b, QRD.size(d)), QRD.size(p), h)) : O.le(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, _)))
  FV.le_of_sub(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), O.one(F)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), O.one(F)), O.mul(F, O.ofp(~F, d), t2(~F, b))), O.add(F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.sub(~F, t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d))))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p)))),
    FO.eq_of_sub(~F, O.add(F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.sub(~F, t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d))))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p)))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), O.one(F)), O.mul(F, O.ofp(~F, d), t2(~F, b))), FO.cert1(~F, O.sub(~F, O.add(F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.sub(~F, t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d))))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p)))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), O.one(F)), O.mul(F, O.ofp(~F, d), t2(~F, b)))), O.one(F), O.sub(~F, O.mul(F, t2(~F, b), t2(~F, QRD.size(d))), t2(~F, Nat.add(b, QRD.size(d)))), FR.fring_eq(~F, [O.ofp(~F, d), O.ofp(~F, p), t2(~F, b), t2(~F, QRD.size(d)), t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d)))], E.ZSub{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{3n}, E.ZVar{0n}}}, E.ZSub{E.ZVar{4n}, E.ZVar{5n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{5n}}}, {==}), FO.sub_of_eq(~F, O.mul(F, t2(~F, b), t2(~F, QRD.size(d))), t2(~F, Nat.add(b, QRD.size(d))), t2_add(~F, b, QRD.size(d))))),
    FO.nonneg_add(~F, O.add(F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.sub(~F, t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d))))), O.sub(~F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, QRD.size(p))),
      FO.nonneg_add(~F, O.mul(F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d))), O.sub(~F, t2(~F, QRD.size(p)), t2(~F, Nat.add(b, QRD.size(d)))),
        FO.mul_nonneg(~F, t2(~F, b), O.sub(~F, t2(~F, QRD.size(d)), O.ofp(~F, d)), ofp_nn(~F, S.Pos.pow2(b)), FM.sub_nonneg(~F, O.ofp(~F, d), t2(~F, QRD.size(d)), le_of_succ(~F, O.ofp(~F, d), t2(~F, QRD.size(d)), size_hi(~F, d)))),
        FM.sub_nonneg(~F, t2(~F, Nat.add(b, QRD.size(d))), t2(~F, QRD.size(p)), ts_mono(~F, p, d, b, h))),
      FM.sub_nonneg(~F, t2(~F, QRD.size(p)), O.add(F, O.ofp(~F, p), O.ofp(~F, p)), size_lo(~F, p)))))

def qbound.go(~F: O.OField, le: Bool, +p: S.Pos, +d: S.Pos, +b: Nat, h: {KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))) == le : Bool}) -> O.le(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))):
  match le:
    case True{}:
      qb_hi(~F, p, d, b, h)
    case False{}:
      qb_lo(~F, p, d, b, h)

# d 2^b <= 2 p 2^E for the exponent E = (b + size d) - size p a rational
# p / d is rounded at
def qbound(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat) -> O.le(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))):
  qbound.go(~F, KA.natle(QRD.size(p), Nat.add(b, QRD.size(d))), p, d, b, {==})

# Rounding a rational
# -------------------

def w_eq(~F: O.OField, +n: S.Z, +d: S.Pos, +e: Nat) -> {O.ofz(~F, S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d})) == O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), O.mul(F, O.ofz(~F, n), t2(~F, e))), O.ofp(~F, d)) : O.C(F)}:
  %FR.ofz_add(~F, S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}) : {_ == O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), O.mul(F, O.ofz(~F, n), t2(~F, e))), O.ofp(~F, d)) : O.C(F)}
  %Equal.sym(O.C(F), O.ofz(~F, S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)}))), O.add(F, O.ofz(~F, S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), O.ofz(~F, S.Z.mul(n, S.Zpos{S.Pos.pow2(e)}))), ofz_double(~F, S.Z.mul(n, S.Zpos{S.Pos.pow2(e)}))) : {O.add(F, _, O.ofp(~F, d)) == O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), O.mul(F, O.ofz(~F, n), t2(~F, e))), O.ofp(~F, d)) : O.C(F)}
  %FR.ofz_mul(~F, n, S.Zpos{S.Pos.pow2(e)}) : {O.add(F, O.add(F, _, O.ofz(~F, S.Z.mul(n, S.Zpos{S.Pos.pow2(e)}))), O.ofp(~F, d)) == O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), O.mul(F, O.ofz(~F, n), t2(~F, e))), O.ofp(~F, d)) : O.C(F)}
  %FR.ofz_mul(~F, n, S.Zpos{S.Pos.pow2(e)}) : {O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), _), O.ofp(~F, d)) == O.add(F, O.add(F, O.mul(F, O.ofz(~F, n), t2(~F, e)), O.mul(F, O.ofz(~F, n), t2(~F, e))), O.ofp(~F, d)) : O.C(F)}
  {==}


# f = floor((2 n 2^e + d) / 2d) is within 2^-(e+1) of n / d, at scale 2^-e
def qr_core(~F: O.OField, +f: O.C(F), +nv: O.C(F), +dd: O.C(F), +te: O.C(F), +ie: O.C(F), +id: O.C(F), +i2: O.C(F), h1: O.le(~F, O.mul(F, f, O.add(F, dd, dd)), O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd)), h2: O.le(~F, O.add(F, O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, dd, dd))), +rd: {O.sub(~F, O.mul(F, dd, id), O.one(F)) == O.zero(F) : O.C(F)}, +re: {O.sub(~F, O.mul(F, te, ie), O.one(F)) == O.zero(F) : O.C(F)}, +r2: {O.sub(~F, O.mul(F, O.add(F, te, te), i2), O.one(F)) == O.zero(F) : O.C(F)}, +hid: O.le(~F, O.zero(F), id), +hi2: O.le(~F, O.zero(F), i2)) -> M.bnd(~F, O.sub(~F, O.mul(F, f, ie), O.mul(F, nv, id)), O.mul(F, O.one(F), i2)):
  KB.bnd_val(~F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te))), O.mul(F, i2, id)), O.sub(~F, O.mul(F, f, ie), O.mul(F, nv, id)), O.mul(F, O.one(F), i2),
    FO.eq_of_sub(~F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te))), O.mul(F, i2, id)), O.sub(~F, O.mul(F, f, ie), O.mul(F, nv, id)), FO.cert3(~F, O.sub(~F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te))), O.mul(F, i2, id)), O.sub(~F, O.mul(F, f, ie), O.mul(F, nv, id))), O.mul(F, O.mul(F, O.add(F, O.one(F), O.one(F)), f), i2), O.sub(~F, O.mul(F, dd, id), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.add(F, O.one(F), O.one(F)), f), i2)), O.sub(~F, O.mul(F, te, ie), O.one(F)), O.sub(~F, O.mul(F, f, ie), O.mul(F, nv, id)), O.sub(~F, O.mul(F, O.add(F, te, te), i2), O.one(F)), FR.fring_eq(~F, [f, nv, dd, te, ie, id, i2], E.ZSub{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{6n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}}, E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), rd, re, r2)),
    FM.bnd_eq(~F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te))), O.mul(F, i2, id)), O.mul(F, dd, O.mul(F, i2, id)), O.mul(F, O.one(F), i2), FO.eq_of_sub(~F, O.mul(F, dd, O.mul(F, i2, id)), O.mul(F, O.one(F), i2), FO.cert1(~F, O.sub(~F, O.mul(F, dd, O.mul(F, i2, id)), O.mul(F, O.one(F), i2)), i2, O.sub(~F, O.mul(F, dd, id), O.one(F)), FR.fring_eq(~F, [f, nv, dd, te, ie, id, i2], E.ZSub{E.ZMul{E.ZVar{2n}, E.ZMul{E.ZVar{6n}, E.ZVar{5n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{6n}}}, E.ZMul{E.ZVar{6n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), rd)),
      bnd_scale(~F, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te))), dd, O.mul(F, i2, id), FO.mul_nonneg(~F, i2, id, hi2, hid),
        (FM.nn_eq(~F, O.sub(~F, dd, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)))), O.sub(~F, O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), O.mul(F, f, O.add(F, dd, dd))), FR.fring_eq(~F, [f, nv, dd, te], E.ZSub{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{2n}, E.ZAdd{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}}, {==}), FM.sub_nonneg(~F, O.mul(F, f, O.add(F, dd, dd)), O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), h1)),
         FM.nn_eq(~F, O.add(F, dd, O.add(F, O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)), O.sub(~F, O.mul(F, f, dd), O.mul(F, nv, te)))), O.add(F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, dd, dd)), O.add(F, O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), O.one(F))), O.one(F)), FR.fring_eq(~F, [f, nv, dd, te], E.ZAdd{E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{2n}, E.ZAdd{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.add(F, f, O.one(F)), O.add(F, dd, dd)), O.add(F, O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), O.one(F))), O.one(F), FM.sub_nonneg(~F, O.add(F, O.add(F, O.add(F, O.mul(F, nv, te), O.mul(F, nv, te)), dd), O.one(F)), O.mul(F, O.add(F, f, O.one(F)), O.add(F, dd, dd)), h2), FO.one_nn(~F)))))))

# n / d rounded to a multiple of 2^-e is within 2^-(e+1)
def qround_err(~F: O.OField, +n: S.Z, +d: S.Pos, +e: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.qround(S.Q{n, d}, e)), O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+e})):
  +h = zfloor_ok(~F, S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d})
  qr_core(~F, O.ofz(~F, NU.zfloor(S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d})), O.ofz(~F, n), O.ofp(~F, d), t2(~F, e), O.inv(F, t2(~F, e)), O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, 1n+e)),
    (%w_eq(~F, n, d, e) : O.le(~F, O.mul(F, O.ofz(~F, NU.zfloor(S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d})), O.add(F, O.ofp(~F, d), O.ofp(~F, d))), _)
      zfl_1(~F, S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d}, NU.zfloor(S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d}), h)),
    (%w_eq(~F, n, d, e) : O.le(~F, O.add(F, _, O.one(F)), O.mul(F, O.add(F, O.ofz(~F, NU.zfloor(S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d})), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d))))
      zfl_2(~F, S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d}, NU.zfloor(S.Z.add(S.Z.double(S.Z.mul(n, S.Zpos{S.Pos.pow2(e)})), S.Zpos{d}), S.XO{d}), h)),
    QE.ofp_rel(~F, d), QE.ofp_rel(~F, S.Pos.pow2(e)), QE.ofp_rel(~F, S.Pos.pow2(1n+e)), inv_nn(~F, d), inv_nn(~F, S.Pos.pow2(1n+e)))


# 2^-(E+1) <= (p / d) 2^-b at the exponent E p / d is rounded at
def qrel(~F: O.OField, +p: S.Pos, +d: S.Pos, +b: Nat) -> O.le(~F, O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.mul(F, O.one(F), O.inv(F, t2(~F, b))))):
  FV.le_of_sub(~F, O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.mul(F, O.one(F), O.inv(F, t2(~F, b)))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.mul(F, O.one(F), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))))), O.mul(F, O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b)))),
    FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b)))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.mul(F, O.one(F), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))))), FO.cert3(~F, O.sub(~F, O.mul(F, O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b)))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.mul(F, O.one(F), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))))), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), O.inv(F, t2(~F, b))), O.sub(~F, O.mul(F, O.add(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), t2(~F, b)), O.inv(F, t2(~F, b)))), O.sub(~F, O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F)), O.neg(F, O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.sub(~F, O.mul(F, t2(~F, b), O.inv(F, t2(~F, b))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, p), O.ofp(~F, d), t2(~F, b), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))), O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b)), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))], E.ZSub{E.ZMul{E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{5n}}, E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{5n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{6n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), QE.ofp_rel(~F, d), QE.ofp_rel(~F, S.Pos.pow2(b)))),
    FO.mul_nonneg(~F, O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.mul(F, O.ofp(~F, d), t2(~F, b))), FO.mul_nonneg(~F, O.mul(F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), FO.mul_nonneg(~F, O.inv(F, O.ofp(~F, d)), O.inv(F, t2(~F, b)), inv_nn(~F, d), inv_nn(~F, S.Pos.pow2(b))), inv_nn(~F, S.Pos.pow2(1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))))), FM.sub_nonneg(~F, O.mul(F, O.ofp(~F, d), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), qbound(~F, p, d, b)))))

def bnd_hi(~F: O.OField, +v: O.C(F), +s: O.C(F), h: M.bnd(~F, v, s)) -> O.le(~F, O.neg(F, v), s):
  (h1, h2) = h
  FV.le_of_sub(~F, O.neg(F, v), s, FM.nn_eq(~F, O.sub(~F, s, O.neg(F, v)), O.add(F, s, v), FR.fring_eq(~F, [v, s], E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{1n}, E.ZNeg{E.ZVar{0n}}}, {==}), h2))

# the error bound 2^-(E+1) is at most |q| 2^-b, given a <= fabs q
def qsig_fin(~F: O.OField, +n: S.Z, +p: S.Pos, +d: S.Pos, +b: Nat, ha: O.le(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), FV.fabs(~F, O.ofq(~F, S.Q{n, d})))) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.qround(S.Q{n, d}, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.ofq(~F, S.Q{n, d})), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  FM.bnd_mono(~F, O.sub(~F, M.ofd(~F, NU.qround(S.Q{n, d}, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p)))), O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))}), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), qround_err(~F, n, d, Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))),
    FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))}), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), DM.le_trans(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+Nat.sub(Nat.add(b, QRD.size(d)), QRD.size(p))}), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), qrel(~F, p, d, b),
      FV.mul_le_r(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), FV.fabs(~F, O.ofq(~F, S.Q{n, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), FO.lt_le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), DM.dpos(~F, S.XH{}, b)), ha))))

# -(-p / d) <= fabs(-p / d)
def neg_le(~F: O.OField, +p: S.Pos, +d: S.Pos) -> O.le(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), FV.fabs(~F, O.ofq(~F, S.Q{S.Zneg{p}, d}))):
  %FR.fring_eq(~F, [O.ofp(~F, p), O.inv(F, O.ofp(~F, d))], E.ZNeg{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, {==}) : O.le(~F, _, FV.fabs(~F, O.ofq(~F, S.Q{S.Zneg{p}, d})))
  bnd_hi(~F, O.ofq(~F, S.Q{S.Zneg{p}, d}), FV.fabs(~F, O.ofq(~F, S.Q{S.Zneg{p}, d})), FV.fabs_bnd(~F, O.ofq(~F, S.Q{S.Zneg{p}, d})))

# |qsig(q, b) - q| <= |q| 2^-b
def qsig_err(~F: O.OField, x: S.Q, +b: Nat) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.qsig(x, b)), O.ofq(~F, x)), O.mul(F, FV.fabs(~F, O.ofq(~F, x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}))):
  match x:
    case S.Q{S.Z0{}, +d}:
      KB.bnd_val(~F, O.zero(F), O.sub(~F, M.ofd(~F, S.D{S.Z0{}, 0n}), O.ofq(~F, S.Q{S.Z0{}, d})), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{S.Z0{}, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), FR.fring_eq(~F, [O.inv(F, O.one(F)), O.inv(F, O.ofp(~F, d))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, {==}), FM.bnd_zero(~F, O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q{S.Z0{}, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b})), FO.mul_nonneg(~F, FV.fabs(~F, O.ofq(~F, S.Q{S.Z0{}, d})), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), FV.fabs_nn(~F, O.ofq(~F, S.Q{S.Z0{}, d})), FO.lt_le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, b}), DM.dpos(~F, S.XH{}, b)))))
    case S.Q{S.Zpos{+p}, +d}:
      qsig_fin(~F, S.Zpos{p}, p, d, b, FV.bnd_lo(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, d))), FV.fabs(~F, O.ofq(~F, S.Q{S.Zpos{p}, d})), FV.fabs_bnd(~F, O.ofq(~F, S.Q{S.Zpos{p}, d}))))
    case S.Q{S.Zneg{+p}, +d}:
      qsig_fin(~F, S.Zneg{p}, p, d, b, neg_le(~F, p, d))

# Rounding up
# -----------


# c = -floor(-n 2^E / 2^e): 0 <= c / 2^E - n / 2^e <= 2^-E
def qc_core(~F: O.OField, +g: O.C(F), +nv: O.C(F), +te: O.C(F), +tt: O.C(F), +ie: O.C(F), +it: O.C(F), h1: O.le(~F, O.mul(F, g, te), O.neg(F, O.mul(F, nv, tt))), h2: O.le(~F, O.add(F, O.neg(F, O.mul(F, nv, tt)), O.one(F)), O.mul(F, O.add(F, g, O.one(F)), te)), +re: {O.sub(~F, O.mul(F, te, ie), O.one(F)) == O.zero(F) : O.C(F)}, +rt: {O.sub(~F, O.mul(F, tt, it), O.one(F)) == O.zero(F) : O.C(F)}, +hie: O.le(~F, O.zero(F), ie), +hit: O.le(~F, O.zero(F), it)) -> M.Both(O.le(~F, O.mul(F, nv, ie), O.mul(F, O.neg(F, g), it)), O.le(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.one(F), it))):
  (FV.le_of_sub(~F, O.mul(F, nv, ie), O.mul(F, O.neg(F, g), it), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.mul(F, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te)), ie), it), FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te)), ie), it), O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), FO.cert2(~F, O.sub(~F, O.mul(F, O.mul(F, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te)), ie), it), O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie))), O.neg(F, O.mul(F, g, it)), O.sub(~F, O.mul(F, te, ie), O.one(F)), O.neg(F, O.mul(F, nv, ie)), O.sub(~F, O.mul(F, tt, it), O.one(F)), FR.fring_eq(~F, [g, nv, te, tt, ie, it], E.ZSub{E.ZMul{E.ZMul{E.ZSub{E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{4n}}}}, E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), re, rt)), FO.mul_nonneg(~F, O.mul(F, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te)), ie), it, FO.mul_nonneg(~F, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te)), ie, FM.sub_nonneg(~F, O.mul(F, g, te), O.neg(F, O.mul(F, nv, tt)), h1), hie), hit))),
   FV.le_of_sub(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.one(F), it), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.one(F), it), O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie))), O.mul(F, O.mul(F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), ie), it), FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), ie), it), O.sub(~F, O.mul(F, O.one(F), it), O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie))), FO.cert2(~F, O.sub(~F, O.mul(F, O.mul(F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), ie), it), O.sub(~F, O.mul(F, O.one(F), it), O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)))), O.mul(F, O.add(F, O.one(F), g), it), O.sub(~F, O.mul(F, te, ie), O.one(F)), O.mul(F, nv, ie), O.sub(~F, O.mul(F, tt, it), O.one(F)), FR.fring_eq(~F, [g, nv, te, tt, ie, it], E.ZSub{E.ZMul{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZSub{E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{5n}}, E.ZMul{E.ZVar{1n}, E.ZVar{4n}}}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), re, rt)),
     FO.mul_nonneg(~F, O.mul(F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), ie), it, FO.mul_nonneg(~F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), ie, FM.nn_eq(~F, O.sub(~F, te, O.sub(~F, O.neg(F, O.mul(F, nv, tt)), O.mul(F, g, te))), O.add(F, O.sub(~F, O.mul(F, O.add(F, g, O.one(F)), te), O.add(F, O.neg(F, O.mul(F, nv, tt)), O.one(F))), O.one(F)), FR.fring_eq(~F, [g, nv, te, tt, ie, it], E.ZAdd{E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{2n}}, E.ZAdd{E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{2n}, E.ZSub{E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.add(F, g, O.one(F)), te), O.add(F, O.neg(F, O.mul(F, nv, tt)), O.one(F))), O.one(F), FM.sub_nonneg(~F, O.add(F, O.neg(F, O.mul(F, nv, tt)), O.one(F)), O.mul(F, O.add(F, g, O.one(F)), te), h2), FO.one_nn(~F))), hie), hit))))

def qc_1(~F: O.OField, +g: O.C(F), +nv: O.C(F), +ie: O.C(F), +it: O.C(F), h: M.Both(O.le(~F, O.mul(F, nv, ie), O.mul(F, O.neg(F, g), it)), O.le(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.one(F), it)))) -> O.le(~F, O.mul(F, nv, ie), O.mul(F, O.neg(F, g), it)):
  (a, b) = h
  a

def qc_2(~F: O.OField, +g: O.C(F), +nv: O.C(F), +ie: O.C(F), +it: O.C(F), h: M.Both(O.le(~F, O.mul(F, nv, ie), O.mul(F, O.neg(F, g), it)), O.le(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.one(F), it)))) -> O.le(~F, O.sub(~F, O.mul(F, O.neg(F, g), it), O.mul(F, nv, ie)), O.mul(F, O.one(F), it)):
  (a, b) = h
  b

def nm_eq(~F: O.OField, +m: S.Z, +k: Nat) -> {O.ofz(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)}))) == O.neg(F, O.mul(F, O.ofz(~F, m), t2(~F, k))) : O.C(F)}:
  %FR.ofz_neg(~F, S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})) : {_ == O.neg(F, O.mul(F, O.ofz(~F, m), t2(~F, k))) : O.C(F)}
  %FR.ofz_mul(~F, m, S.Zpos{S.Pos.pow2(k)}) : {O.neg(F, _) == O.neg(F, O.mul(F, O.ofz(~F, m), t2(~F, k))) : O.C(F)}
  {==}


# 2^-E <= (p / 2^e) 2^(1-b) at the exponent E dsigup rounds p / 2^e at
def dur(~F: O.OField, +p: S.Pos, +e: Nat, +b: Nat) -> O.le(~F, O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b))))):
  FV.le_of_sub(~F, O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))))), O.mul(F, O.mul(F, O.mul(F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), O.mul(F, t2(~F, e), t2(~F, b)))),
    FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.mul(F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), O.mul(F, t2(~F, e), t2(~F, b)))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))))), FO.cert3(~F, O.sub(~F, O.mul(F, O.mul(F, O.mul(F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), O.mul(F, t2(~F, e), t2(~F, b)))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))))), O.mul(F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), O.inv(F, t2(~F, e))), O.inv(F, t2(~F, b))), O.sub(~F, O.mul(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), t2(~F, b)), O.inv(F, t2(~F, b)))), O.sub(~F, O.mul(F, t2(~F, e), O.inv(F, t2(~F, e))), O.one(F)), O.neg(F, O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.sub(~F, O.mul(F, t2(~F, b), O.inv(F, t2(~F, b))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, p), t2(~F, e), t2(~F, b), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))), O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b)), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))], E.ZSub{E.ZMul{E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{5n}}, E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{5n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{6n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{2n}}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZVar{6n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), QE.ofp_rel(~F, S.Pos.pow2(e)), QE.ofp_rel(~F, S.Pos.pow2(b)))),
    FO.mul_nonneg(~F, O.mul(F, O.mul(F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.sub(~F, O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), O.mul(F, t2(~F, e), t2(~F, b))), FO.mul_nonneg(~F, O.mul(F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), FO.mul_nonneg(~F, O.inv(F, t2(~F, e)), O.inv(F, t2(~F, b)), inv_nn(~F, S.Pos.pow2(e)), inv_nn(~F, S.Pos.pow2(b))), inv_nn(~F, S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), FM.sub_nonneg(~F, O.mul(F, t2(~F, e), t2(~F, b)), O.mul(F, O.add(F, O.ofp(~F, p), O.ofp(~F, p)), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), qbound(~F, p, S.Pos.pow2(e), b)))))


def dsu_h1(~F: O.OField, +m: S.Z, +e: Nat, +k: Nat, h: zfl(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e), NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e)))) -> O.le(~F, O.mul(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e))), t2(~F, e)), O.neg(F, O.mul(F, O.ofz(~F, m), t2(~F, k)))):
  %nm_eq(~F, m, k) : O.le(~F, O.mul(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e))), t2(~F, e)), _)
  zfl_1(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e), NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e)), h)

def dsu_h2(~F: O.OField, +m: S.Z, +e: Nat, +k: Nat, h: zfl(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e), NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e)))) -> O.le(~F, O.add(F, O.neg(F, O.mul(F, O.ofz(~F, m), t2(~F, k))), O.one(F)), O.mul(F, O.add(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e))), O.one(F)), t2(~F, e))):
  %nm_eq(~F, m, k) : O.le(~F, O.add(F, _, O.one(F)), O.mul(F, O.add(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e))), O.one(F)), t2(~F, e)))
  zfl_2(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e), NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(k)})), S.Pos.pow2(e)), h)

def dsu_fin(~F: O.OField, +m: S.Z, +p: S.Pos, +e: Nat, +b: Nat, ea: {O.ofz(~F, M.zabs(m)) == O.ofp(~F, p) : O.C(F)}, +cc: M.Both(O.le(~F, O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, e))), O.mul(F, O.neg(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e)))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))))), O.le(~F, O.sub(~F, O.mul(F, O.neg(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e)))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, e)))), O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))))))) -> M.Both(O.le(~F, M.ofd(~F, S.D{m, e}), M.ofd(~F, NU.qceil(S.Q{m, S.Pos.pow2(e)}, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.le(~F, O.sub(~F, M.ofd(~F, NU.qceil(S.Q{m, S.Pos.pow2(e)}, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), M.ofd(~F, S.D{m, e})), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, b})))):
  ((%FR.ofz_neg(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))) : O.le(~F, O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, e))), O.mul(F, _, O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))))
     qc_1(~F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))), O.ofz(~F, m), O.inv(F, t2(~F, e)), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), cc)),
   (%FR.ofz_neg(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))) : O.le(~F, O.sub(~F, O.mul(F, _, O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, e)))), O.mul(F, O.mul(F, O.ofz(~F, M.zabs(m)), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))))
     DM.le_trans(~F, O.sub(~F, O.mul(F, O.neg(F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e)))), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.ofz(~F, m), O.inv(F, t2(~F, e)))), O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.mul(F, O.ofz(~F, M.zabs(m)), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))),
       qc_2(~F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))), O.ofz(~F, m), O.inv(F, t2(~F, e)), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), cc),
       (%Equal.sym(O.C(F), O.ofz(~F, M.zabs(m)), O.ofp(~F, p), ea) : O.le(~F, O.mul(F, O.one(F), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.mul(F, O.mul(F, _, O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))))
         dur(~F, p, e, b)))))

# m nonzero with |m| = p
def dsu_go(~F: O.OField, +m: S.Z, +p: S.Pos, +e: Nat, +b: Nat, ea: {O.ofz(~F, M.zabs(m)) == O.ofp(~F, p) : O.C(F)}) -> M.Both(O.le(~F, M.ofd(~F, S.D{m, e}), M.ofd(~F, NU.qceil(S.Q{m, S.Pos.pow2(e)}, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))))), O.le(~F, O.sub(~F, M.ofd(~F, NU.qceil(S.Q{m, S.Pos.pow2(e)}, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), M.ofd(~F, S.D{m, e})), O.mul(F, M.ofd(~F, S.D{M.zabs(m), e}), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, b})))):
  +h = zfloor_ok(~F, S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))
  +cc = qc_core(~F, O.ofz(~F, NU.zfloor(S.Z.neg(S.Z.mul(m, S.Zpos{S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))})), S.Pos.pow2(e))), O.ofz(~F, m), t2(~F, e), t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p))), O.inv(F, t2(~F, e)), O.inv(F, t2(~F, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))),
    dsu_h1(~F, m, e, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)), h), dsu_h2(~F, m, e, Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)), h),
    QE.ofp_rel(~F, S.Pos.pow2(e)), QE.ofp_rel(~F, S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))), inv_nn(~F, S.Pos.pow2(e)), inv_nn(~F, S.Pos.pow2(Nat.sub(Nat.add(b, QRD.size(S.Pos.pow2(e))), QRD.size(p)))))
  dsu_fin(~F, m, p, e, b, ea, cc)

# x <= dsigup(x, b) <= x + |x| 2^(1-b)
def dsigup_ok(~F: O.OField, x: S.D, +b: Nat) -> M.Both(O.le(~F, M.ofd(~F, x), M.ofd(~F, NU.dsigup(x, b))), O.le(~F, O.sub(~F, M.ofd(~F, NU.dsigup(x, b)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XO{S.XH{}}}, b})))):
  match x:
    case S.D{S.Z0{}, +e}:
      (Inr{FR.fring_eq(~F, [O.inv(F, t2(~F, e)), O.inv(F, O.one(F))], E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, {==})},
       FV.le_of_sub(~F, O.sub(~F, O.mul(F, O.zero(F), O.inv(F, O.one(F))), O.mul(F, O.zero(F), O.inv(F, t2(~F, e)))), O.mul(F, O.mul(F, O.zero(F), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, O.zero(F), O.inv(F, t2(~F, e))), O.mul(F, O.add(F, O.one(F), O.one(F)), O.inv(F, t2(~F, b)))), O.sub(~F, O.mul(F, O.zero(F), O.inv(F, O.one(F))), O.mul(F, O.zero(F), O.inv(F, t2(~F, e))))), O.zero(F), FR.fring_eq(~F, [O.inv(F, t2(~F, e)), O.inv(F, O.one(F)), O.inv(F, t2(~F, b))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{2n}}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}}}, {==}), FO.le_refl(~F, O.zero(F)))))
    case S.D{S.Zpos{+p}, +e}:
      dsu_go(~F, S.Zpos{p}, p, e, b, {==})
    case S.D{S.Zneg{+p}, +e}:
      dsu_go(~F, S.Zneg{p}, p, e, b, {==})
