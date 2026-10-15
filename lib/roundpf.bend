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

# Order helpers
# -------------

def one_nn(~F: O.OField) -> O.le(~F, O.zero(F), O.one(F)):
  Inl{O.zero_lt_one(F)}

# a <= b and c <= d give a + c <= b + d
def le_add2(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), h1: O.le(~F, a, b), h2: O.le(~F, c, d)) -> O.le(~F, O.add(F, a, c), O.add(F, b, d)):
  FV.le_of_sub(~F, O.add(F, a, c), O.add(F, b, d), FM.nn_eq(~F, O.sub(~F, O.add(F, b, d), O.add(F, a, c)), O.add(F, O.sub(~F, b, a), O.sub(~F, d, c)), FR.fring_eq(~F, [a, b, c, d], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, b, a), O.sub(~F, d, c), FM.sub_nonneg(~F, a, b, h1), FM.sub_nonneg(~F, c, d, h2))))

# a <= b gives a + a <= b + b
def le_dbl(~F: O.OField, +a: O.C(F), +b: O.C(F), +h: O.le(~F, a, b)) -> O.le(~F, O.add(F, a, a), O.add(F, b, b)):
  le_add2(~F, a, b, a, b, h, h)

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
      FV.le_of_sub(~F, O.one(F), O.ofp(~F, S.XO{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XO{q}), O.one(F)), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.one(F), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F)), s, s), one_nn(~F))))
    case S.XI{+q}:
      +s = FM.sub_nonneg(~F, O.one(F), O.ofp(~F, q), ofp_ge1(~F, q))
      FV.le_of_sub(~F, O.one(F), O.ofp(~F, S.XI{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XI{q}), O.one(F)), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.add(F, O.one(F), O.one(F))), FR.fring_eq(~F, [O.ofp(~F, q)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F))), O.add(F, O.one(F), O.one(F)), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, q), O.one(F)), O.sub(~F, O.ofp(~F, q), O.one(F)), s, s), FO.nonneg_add(~F, O.one(F), O.one(F), one_nn(~F), one_nn(~F)))))

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
      le_dbl(~F, t2(~F, QRD.size(q)), O.ofp(~F, S.XI{q}), FV.le_of_sub(~F, t2(~F, QRD.size(q)), O.ofp(~F, S.XI{q}), FM.nn_eq(~F, O.sub(~F, O.ofp(~F, S.XI{q}), t2(~F, QRD.size(q))), O.add(F, O.sub(~F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), t2(~F, QRD.size(q))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q), t2(~F, QRD.size(q))], E.ZAdd{E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), t2(~F, QRD.size(q))), O.one(F), FM.sub_nonneg(~F, t2(~F, QRD.size(q)), O.add(F, O.ofp(~F, q), O.ofp(~F, q)), size_lo(~F, q)), one_nn(~F)))))

# p + 1 <= 2^(size p)
def size_hi(~F: O.OField, p: S.Pos) -> O.le(~F, O.add(F, O.ofp(~F, p), O.one(F)), t2(~F, QRD.size(p))):
  match p:
    case S.XH{}:
      FO.le_refl(~F, O.add(F, O.one(F), O.one(F)))
    case S.XO{+q}:
      FV.le_of_sub(~F, O.add(F, O.ofp(~F, S.XO{q}), O.one(F)), t2(~F, QRD.size(S.XO{q})), FM.nn_eq(~F, O.sub(~F, t2(~F, QRD.size(S.XO{q})), O.add(F, O.ofp(~F, S.XO{q}), O.one(F))), O.add(F, O.sub(~F, O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F)))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, q), t2(~F, QRD.size(q))], E.ZAdd{E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F)))), O.one(F), FM.sub_nonneg(~F, O.add(F, O.add(F, O.ofp(~F, q), O.one(F)), O.add(F, O.ofp(~F, q), O.one(F))), O.add(F, t2(~F, QRD.size(q)), t2(~F, QRD.size(q))), le_dbl(~F, O.add(F, O.ofp(~F, q), O.one(F)), t2(~F, QRD.size(q)), size_hi(~F, q))), one_nn(~F))))
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
  FV.le_of_sub(~F, a, b, FM.nn_eq(~F, O.sub(~F, b, a), O.add(F, O.sub(~F, b, O.add(F, a, O.one(F))), O.one(F)), FR.fring_eq(~F, [a, b], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, {==}), FO.nonneg_add(~F, O.sub(~F, b, O.add(F, a, O.one(F))), O.one(F), FM.sub_nonneg(~F, O.add(F, a, O.one(F)), b, h), one_nn(~F))))

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
      FV.le_of_sub(~F, O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F)), O.add(F, O.ofp(~F, d), O.ofp(~F, d)), FM.nn_eq(~F, O.sub(~F, O.add(F, O.ofp(~F, d), O.ofp(~F, d)), O.add(F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F))), O.add(F, O.add(F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F)))), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, r), O.ofp(~F, d)], E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.nonneg_add(~F, O.add(F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F)))), O.one(F), FO.nonneg_add(~F, O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), O.sub(~F, O.ofp(~F, d), O.add(F, O.ofz(~F, r), O.one(F))), s, s), one_nn(~F))))))

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
      FO.nonneg_add(~F, O.add(F, O.ofz(~F, r), O.ofz(~F, r)), O.one(F), FO.nonneg_add(~F, O.ofz(~F, r), O.ofz(~F, r), h0, h0), one_nn(~F))),
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
      adj_ok(~F, S.Z.cmp(S.Zpos{S.XH{}}, S.Zpos{d}), S.XH{}, S.Z0{}, S.Zpos{S.XH{}}, d, {==}, FR.fring_eq(~F, [O.ofp(~F, d)], E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}), one_nn(~F), le_dbl(~F, O.one(F), O.ofp(~F, d), ofp_ge1(~F, d)))
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
