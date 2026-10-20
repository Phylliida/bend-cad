# bend-cad: values a + b delta in an ordered field, delta a positive
# infinitesimal, compared lexicographically (PLAN-sk13a S3: the simplex's
# strict bounds). A value is a pair (x0, x1); its sign is x0's, or x1's
# when x0 = 0. Sums and positive (negative) multiples keep (flip) signs.
# Also: integer comparisons read in F.
#
# Generated from tools/drafts/lexpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./zord.bend as ZO
import ./karith.bend as KA

def absurd(-A: Type, x: Empty) -> A:
  match x:

def both_l(-A: Data, -B: Data, h: M.Both(A, B)) -> A:
  (a, b) = h
  a

def both_r(-A: Data, -B: Data, h: M.Both(A, B)) -> B:
  (a, b) = h
  b

# Integer comparisons in F
# ------------------------

def ofz_sub(~F: O.OField, +a: S.Z, +b: S.Z) -> {O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)) == O.ofz(~F, S.Z.sub(b, a)) : O.C(F)}:
  %Equal.sym(O.C(F), O.neg(F, O.ofz(~F, a)), O.ofz(~F, S.Z.neg(a)), FR.ofz_neg(~F, a)) : {O.add(F, O.ofz(~F, b), _) == O.ofz(~F, S.Z.sub(b, a)) : O.C(F)}
  FR.ofz_add(~F, b, S.Z.neg(a))

def zlt_f(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == LT{} : Cmp}) -> O.lt(F, O.ofz(~F, a), O.ofz(~F, b)):
  QE.lt_of_sub(~F, O.ofz(~F, a), O.ofz(~F, b), (%Equal.sym(O.C(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.ofz(~F, S.Z.sub(b, a)), ofz_sub(~F, a, b)) : O.lt(F, O.zero(F), _)
    QE.ofz_pos(~F, S.Z.sub(b, a), ZO.lt_pos(a, b, h))))

def zeq_f(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == EQ{} : Cmp}) -> {O.ofz(~F, a) == O.ofz(~F, b) : O.C(F)}:
  Equal.sym(O.C(F), O.ofz(~F, b), O.ofz(~F, a), FO.eq_of_sub(~F, O.ofz(~F, b), O.ofz(~F, a), (%Equal.sym(O.C(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.ofz(~F, S.Z.sub(b, a)), ofz_sub(~F, a, b)) : {_ == O.zero(F) : O.C(F)}
    %Equal.sym(S.Z, S.Z.sub(b, a), S.Z0{}, ZO.eq_zero(a, b, h)) : {O.ofz(~F, _) == O.zero(F) : O.C(F)}
    {==})))

def zgt_f(~F: O.OField, +a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == GT{} : Cmp}) -> O.lt(F, O.ofz(~F, b), O.ofz(~F, a)):
  QE.lt_of_sub(~F, O.ofz(~F, b), O.ofz(~F, a), (%FR.fring_eq(~F, [O.ofz(~F, a), O.ofz(~F, b)], E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}) : O.lt(F, O.zero(F), _)
    %Equal.sym(O.C(F), O.sub(~F, O.ofz(~F, b), O.ofz(~F, a)), O.ofz(~F, S.Z.sub(b, a)), ofz_sub(~F, a, b)) : O.lt(F, O.zero(F), O.neg(F, _))
    %Equal.sym(O.C(F), O.neg(F, O.ofz(~F, S.Z.sub(b, a))), O.ofz(~F, S.Z.neg(S.Z.sub(b, a))), FR.ofz_neg(~F, S.Z.sub(b, a))) : O.lt(F, O.zero(F), _)
    QE.ofz_pos(~F, S.Z.neg(S.Z.sub(b, a)), ZO.gt_pos(a, b, h))))

# Signs of pairs
# --------------

def LNeg(~F: O.OField, +x0: O.C(F), +x1: O.C(F)) -> Data:
  Either<&2, &2, O.lt(F, x0, O.zero(F)), M.Both({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)))>

def LNonpos(~F: O.OField, +x0: O.C(F), +x1: O.C(F)) -> Data:
  Either<&2, &2, O.lt(F, x0, O.zero(F)), M.Both({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)))>

def LPos(~F: O.OField, +x0: O.C(F), +x1: O.C(F)) -> Data:
  Either<&2, &2, O.lt(F, O.zero(F), x0), M.Both({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1))>

def LNonneg(~F: O.OField, +x0: O.C(F), +x1: O.C(F)) -> Data:
  Either<&2, &2, O.lt(F, O.zero(F), x0), M.Both({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1))>

# Order helpers
# -------------

def lt_rw_l(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), e: {a == b : O.C(F)}, h: O.lt(F, a, c)) -> O.lt(F, b, c):
  FO.lt_subst_l(~F, a, b, c, e, h)

def le_rw_l(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), e: {a == b : O.C(F)}, h: O.le(~F, a, c)) -> O.le(~F, b, c):
  %e : O.le(~F, _, c)
  h

def le_rw_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), e: {a == b : O.C(F)}, h: O.le(~F, c, a)) -> O.le(~F, c, b):
  %e : O.le(~F, c, _)
  h

# x < 0 and y <= 0: x + y < 0
def neg_add(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.lt(F, x, O.zero(F)), hy: O.le(~F, y, O.zero(F))) -> O.lt(F, O.add(F, x, y), O.zero(F)):
  FO.lt_le_trans(~F, O.add(F, x, y), O.add(F, O.zero(F), y), O.zero(F), O.lt_add(F)(x, O.zero(F), y)(hx), le_rw_l(~F, y, O.add(F, O.zero(F), y), O.zero(F), Equal.sym(O.C(F), O.add(F, O.zero(F), y), y, FL.zero_add(~F, y)), hy))

# x <= 0 and y <= 0: x + y <= 0
def nonpos_add(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.le(~F, x, O.zero(F)), hy: O.le(~F, y, O.zero(F))) -> O.le(~F, O.add(F, x, y), O.zero(F)):
  match hx:
    case Inl{l}:
      FO.lt_le(~F, O.add(F, x, y), O.zero(F), neg_add(~F, x, y, l, hy))
    case Inr{e}:
      %Equal.sym(O.C(F), x, O.zero(F), e) : O.le(~F, O.add(F, _, y), O.zero(F))
      le_rw_l(~F, y, O.add(F, O.zero(F), y), O.zero(F), Equal.sym(O.C(F), O.add(F, O.zero(F), y), y, FL.zero_add(~F, y)), hy)

# x <= 0 and y < 0: x + y < 0
def neg_add_r(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.le(~F, x, O.zero(F)), hy: O.lt(F, y, O.zero(F))) -> O.lt(F, O.add(F, x, y), O.zero(F)):
  %O.add_comm(F)(y, x) : O.lt(F, _, O.zero(F))
  neg_add(~F, y, x, hy, hx)

# 0 < -y: y < 0
def lt0_of_neg(~F: O.OField, +y: O.C(F), h: O.lt(F, O.zero(F), O.neg(F, y))) -> O.lt(F, y, O.zero(F)):
  QE.lt_of_sub(~F, y, O.zero(F), (%FR.fring_eq(~F, [y], E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{0n}}, {==}) : O.lt(F, O.zero(F), _)
    h))

# 0 < c, x < 0: c x < 0
def mul_pos_neg(~F: O.OField, +c: O.C(F), +x: O.C(F), hc: O.lt(F, O.zero(F), c), hx: O.lt(F, x, O.zero(F))) -> O.lt(F, O.mul(F, c, x), O.zero(F)):
  lt0_of_neg(~F, O.mul(F, c, x), (%FR.fring_eq(~F, [c, x], E.ZMul{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==}) : O.lt(F, O.zero(F), _)
    O.lt_mul(F)(c, O.neg(F, x), hc, FO.neg_pos(~F, x, hx))))

# c < 0, 0 < x: c x < 0
def mul_neg_pos(~F: O.OField, +c: O.C(F), +x: O.C(F), hc: O.lt(F, c, O.zero(F)), hx: O.lt(F, O.zero(F), x)) -> O.lt(F, O.mul(F, c, x), O.zero(F)):
  lt0_of_neg(~F, O.mul(F, c, x), (%FR.fring_eq(~F, [c, x], E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==}) : O.lt(F, O.zero(F), _)
    O.lt_mul(F)(O.neg(F, c), x, FO.neg_pos(~F, c, hc), hx)))

def zero_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), ea: {a == O.zero(F) : O.C(F)}, eb: {b == O.zero(F) : O.C(F)}) -> {O.add(F, a, b) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), a, O.zero(F), ea) : {O.add(F, _, b) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), b, O.zero(F), eb) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
  O.add_zero(F)(O.zero(F))

def mul_zero_r(~F: O.OField, +c: O.C(F), +x: O.C(F), e: {x == O.zero(F) : O.C(F)}) -> {O.mul(F, c, x) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.zero(F), e) : {O.mul(F, c, _) == O.zero(F) : O.C(F)}
  Equal.sym(O.C(F), O.zero(F), O.mul(F, c, O.zero(F)), FL.mul_zero(~F, c))

def le0_of_eq(~F: O.OField, +x: O.C(F), e: {x == O.zero(F) : O.C(F)}) -> O.le(~F, x, O.zero(F)):
  Inr{e}

# Sums
# ----

def lnonpos_add(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LNonpos(~F, x0, x1), hy: LNonpos(~F, y0, y1)) -> LNonpos(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{neg_add(~F, x0, y0, u, FO.lt_le(~F, y0, O.zero(F), v))}
    case Inl{+u} Inr{+v}:
      Inl{neg_add(~F, x0, y0, u, le0_of_eq(~F, y0, both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)))}
    case Inr{+u} Inl{+v}:
      Inl{neg_add_r(~F, x0, y0, le0_of_eq(~F, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(zero_eq(~F, x0, y0, both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u), both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)), nonpos_add(~F, x1, y1, both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u), both_r({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)))}

def lneg_add_l(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LNeg(~F, x0, x1), hy: LNonpos(~F, y0, y1)) -> LNeg(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{neg_add(~F, x0, y0, u, FO.lt_le(~F, y0, O.zero(F), v))}
    case Inl{+u} Inr{+v}:
      Inl{neg_add(~F, x0, y0, u, le0_of_eq(~F, y0, both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)))}
    case Inr{+u} Inl{+v}:
      Inl{neg_add_r(~F, x0, y0, le0_of_eq(~F, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(zero_eq(~F, x0, y0, both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), u), both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)), neg_add(~F, x1, y1, both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), u), both_r({y0 == O.zero(F) : O.C(F)}, O.le(~F, y1, O.zero(F)), v)))}

def lneg_add_r(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LNonpos(~F, x0, x1), hy: LNeg(~F, y0, y1)) -> LNeg(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{neg_add(~F, x0, y0, u, FO.lt_le(~F, y0, O.zero(F), v))}
    case Inl{+u} Inr{+v}:
      Inl{neg_add(~F, x0, y0, u, le0_of_eq(~F, y0, both_l({y0 == O.zero(F) : O.C(F)}, O.lt(F, y1, O.zero(F)), v)))}
    case Inr{+u} Inl{+v}:
      Inl{neg_add_r(~F, x0, y0, le0_of_eq(~F, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(zero_eq(~F, x0, y0, both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u), both_l({y0 == O.zero(F) : O.C(F)}, O.lt(F, y1, O.zero(F)), v)), neg_add_r(~F, x1, y1, both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, x1, O.zero(F)), u), both_r({y0 == O.zero(F) : O.C(F)}, O.lt(F, y1, O.zero(F)), v)))}

# Multiples
# ---------

def lneg_scale(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), hc: O.lt(F, O.zero(F), c), hx: LNeg(~F, x0, x1)) -> LNeg(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  match hx:
    case Inl{a}:
      Inl{mul_pos_neg(~F, c, x0, hc, a)}
    case Inr{+p}:
      Inr{(mul_zero_r(~F, c, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), p)), mul_pos_neg(~F, c, x1, hc, both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), p)))}

# c < 0, 0 <= x: c x <= 0
def lnonpos_scale_neg.le(~F: O.OField, +c: O.C(F), +x: O.C(F), hc: O.lt(F, c, O.zero(F)), hx: O.le(~F, O.zero(F), x)) -> O.le(~F, O.mul(F, c, x), O.zero(F)):
  match hx:
    case Inl{a}:
      FO.lt_le(~F, O.mul(F, c, x), O.zero(F), mul_neg_pos(~F, c, x, hc, a))
    case Inr{e}:
      le0_of_eq(~F, O.mul(F, c, x), mul_zero_r(~F, c, x, Equal.sym(O.C(F), O.zero(F), x, e)))

def lnonpos_scale_neg(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), hc: O.lt(F, c, O.zero(F)), hx: LNonneg(~F, x0, x1)) -> LNonpos(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  match hx:
    case Inl{a}:
      Inl{mul_neg_pos(~F, c, x0, hc, a)}
    case Inr{+p}:
      Inr{(mul_zero_r(~F, c, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), p)), lnonpos_scale_neg.le(~F, c, x1, hc, both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), p)))}

def lnonpos_zero(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), e0: {x0 == O.zero(F) : O.C(F)}, e1: {x1 == O.zero(F) : O.C(F)}) -> LNonpos(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  Inr{(mul_zero_r(~F, c, x0, e0), le0_of_eq(~F, O.mul(F, c, x1), mul_zero_r(~F, c, x1, e1)))}

def lnonpos_czero(~F: O.OField, +x0: O.C(F), +x1: O.C(F)) -> LNonpos(~F, O.mul(F, O.zero(F), x0), O.mul(F, O.zero(F), x1)):
  Inr{(FL.zero_mul(~F, x0), le0_of_eq(~F, O.mul(F, O.zero(F), x1), FL.zero_mul(~F, x1)))}

# Comparing signs
# ---------------

def lt_irr0(~F: O.OField, +x: O.C(F), h1: O.lt(F, O.zero(F), x), h2: O.lt(F, x, O.zero(F))) -> Empty:
  O.lt_irrefl(F)(O.zero(F))(O.lt_trans(F)(O.zero(F), x, O.zero(F))(h1)(h2))

def lt_eq0(~F: O.OField, +x: O.C(F), e: {x == O.zero(F) : O.C(F)}, h: O.lt(F, O.zero(F), x)) -> Empty:
  O.lt_irrefl(F)(O.zero(F))((%e : O.lt(F, O.zero(F), _)
    h))

# a pair is not both positive and negative
def lpos_lneg(~F: O.OField, +x0: O.C(F), +x1: O.C(F), hp: LPos(~F, x0, x1), hn: LNeg(~F, x0, x1)) -> Empty:
  match hp hn:
    case Inl{+u} Inl{+v}:
      lt_irr0(~F, x0, u, v)
    case Inl{+u} Inr{+v}:
      lt_eq0(~F, x0, both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), v), u)
    case Inr{+u} Inl{+v}:
      lt_eq0(~F, O.neg(F, x0), (%Equal.sym(O.C(F), x0, O.zero(F), both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), u)) : {O.neg(F, _) == O.zero(F) : O.C(F)}
        Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))), FO.neg_pos(~F, x0, v))
    case Inr{+u} Inr{+v}:
      lt_irr0(~F, x1, both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), u), both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), v))

# 0 <= a, b < 0: 0 < a - b
def pos_sub_l(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.le(~F, O.zero(F), a), hb: O.lt(F, b, O.zero(F))) -> O.lt(F, O.zero(F), O.sub(~F, a, b)):
  FO.pos_add_r(~F, a, O.neg(F, b), ha, FO.neg_pos(~F, b, hb))

def pos_sub_r.nn(~F: O.OField, +b: O.C(F), hb: O.le(~F, b, O.zero(F))) -> O.le(~F, O.zero(F), O.neg(F, b)):
  match hb:
    case Inl{l}:
      FO.lt_le(~F, O.zero(F), O.neg(F, b), FO.neg_pos(~F, b, l))
    case Inr{e}:
      Inr{(%Equal.sym(O.C(F), b, O.zero(F), e) : {O.zero(F) == O.neg(F, _) : O.C(F)}
        FL.neg_zero(~F))}

# 0 < a, b <= 0: 0 < a - b
def pos_sub_r(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.lt(F, O.zero(F), a), hb: O.le(~F, b, O.zero(F))) -> O.lt(F, O.zero(F), O.sub(~F, a, b)):
  FO.pos_add(~F, a, O.neg(F, b), ha, pos_sub_r.nn(~F, b, hb))

def sub_zero2(~F: O.OField, +a: O.C(F), +b: O.C(F), ea: {a == O.zero(F) : O.C(F)}, eb: {b == O.zero(F) : O.C(F)}) -> {O.sub(~F, a, b) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), a, O.zero(F), ea) : {O.sub(~F, _, b) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), b, O.zero(F), eb) : {O.sub(~F, O.zero(F), _) == O.zero(F) : O.C(F)}
  FR.fring_eq(~F, [], E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

# A >= 0 and B < 0 (lexicographically): A - B > 0
def lpos_sub(~F: O.OField, +a0: O.C(F), +a1: O.C(F), +b0: O.C(F), +b1: O.C(F), ha: LNonneg(~F, a0, a1), hb: LNeg(~F, b0, b1)) -> LPos(~F, O.sub(~F, a0, b0), O.sub(~F, a1, b1)):
  match ha hb:
    case Inl{+u} Inl{+v}:
      Inl{pos_sub_r(~F, a0, b0, u, FO.lt_le(~F, b0, O.zero(F), v))}
    case Inl{+u} Inr{+v}:
      Inl{pos_sub_r(~F, a0, b0, u, le0_of_eq(~F, b0, both_l({b0 == O.zero(F) : O.C(F)}, O.lt(F, b1, O.zero(F)), v)))}
    case Inr{+u} Inl{+v}:
      Inl{pos_sub_l(~F, a0, b0, Inr{Equal.sym(O.C(F), a0, O.zero(F), both_l({a0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), a1), u))}, v)}
    case Inr{+u} Inr{+v}:
      Inr{(sub_zero2(~F, a0, b0, both_l({a0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), a1), u), both_l({b0 == O.zero(F) : O.C(F)}, O.lt(F, b1, O.zero(F)), v)), pos_sub_l(~F, a1, b1, both_r({a0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), a1), u), both_r({b0 == O.zero(F) : O.C(F)}, O.lt(F, b1, O.zero(F)), v)))}
