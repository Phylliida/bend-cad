# Order facts and certificate helpers in every ordered field, from the
# axioms of spec/field.bend. A certificate proves x = 0 from relations
# r1 = 0, ..., rn = 0 and one normalizer call showing x = c1 r1 + ... + cn rn
# (the §8.7 identity-certificate technique; divisions enter as an atom i
# with the relation n i - 1 = 0).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ./flaws.bend as FL
import ./fring.bend as FR

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Equalities as differences
# -------------------------

# a = b gives a - b = 0
def sub_of_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {a == b : O.C(F)}) -> {O.sub(~F, a, b) == O.zero(F) : O.C(F)}:
  %h : {O.sub(~F, a, _) == O.zero(F) : O.C(F)}
  O.add_neg(F)(a)

# a - b = 0 gives a = b
def eq_of_sub(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {O.sub(~F, a, b) == O.zero(F) : O.C(F)}) -> {a == b : O.C(F)}:
  %FL.zero_add(~F, b) : {a == _ : O.C(F)}
  %h : {a == O.add(F, _, b) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.add(F, a, O.neg(F, b)), b), O.add(F, a, O.add(F, O.neg(F, b), b)), O.add_assoc(F)(a, O.neg(F, b), b)) : {a == _ : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.neg(F, b), b), O.zero(F), FL.neg_add_l(~F, b)) : {a == O.add(F, a, _) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, a, O.zero(F)), a, O.add_zero(F)(a)) : {a == _ : O.C(F)}
  {==}

# Certificates
# ------------

def cert1(~F: O.OField, +x: O.C(F), +c1: O.C(F), +r1: O.C(F), hid: {x == O.mul(F, c1, r1) : O.C(F)}, h1: {r1 == O.zero(F) : O.C(F)}) -> {x == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.mul(F, c1, r1), hid) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r1, O.zero(F), h1) : {O.mul(F, c1, _) == O.zero(F) : O.C(F)}
  Equal.sym(O.C(F), O.zero(F), O.mul(F, c1, O.zero(F)), FL.mul_zero(~F, c1))

def cert2(~F: O.OField, +x: O.C(F), +c1: O.C(F), +r1: O.C(F), +c2: O.C(F), +r2: O.C(F), hid: {x == O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)) : O.C(F)}, h1: {r1 == O.zero(F) : O.C(F)}, h2: {r2 == O.zero(F) : O.C(F)}) -> {x == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)), hid) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r1, O.zero(F), h1) : {O.add(F, O.mul(F, c1, _), O.mul(F, c2, r2)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r2, O.zero(F), h2) : {O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, _)) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c1) : {O.add(F, _, O.mul(F, c2, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c2) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
  O.add_zero(F)(O.zero(F))

def cert3(~F: O.OField, +x: O.C(F), +c1: O.C(F), +r1: O.C(F), +c2: O.C(F), +r2: O.C(F), +c3: O.C(F), +r3: O.C(F), hid: {x == O.add(F, O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)), O.mul(F, c3, r3)) : O.C(F)}, h1: {r1 == O.zero(F) : O.C(F)}, h2: {r2 == O.zero(F) : O.C(F)}, h3: {r3 == O.zero(F) : O.C(F)}) -> {x == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.add(F, O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)), O.mul(F, c3, r3)), hid) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r1, O.zero(F), h1) : {O.add(F, O.add(F, O.mul(F, c1, _), O.mul(F, c2, r2)), O.mul(F, c3, r3)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r2, O.zero(F), h2) : {O.add(F, O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, _)), O.mul(F, c3, r3)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r3, O.zero(F), h3) : {O.add(F, O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, O.zero(F))), O.mul(F, c3, _)) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c1) : {O.add(F, O.add(F, _, O.mul(F, c2, O.zero(F))), O.mul(F, c3, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c2) : {O.add(F, O.add(F, O.zero(F), _), O.mul(F, c3, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c3) : {O.add(F, O.add(F, O.zero(F), O.zero(F)), _) == O.zero(F) : O.C(F)}
  %FL.add_zero(~F, O.zero(F)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
  O.add_zero(F)(O.zero(F))

# Order
# -----

def lt_subst_l(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), e: {a == b : O.C(F)}, h: O.lt(F, a, c)) -> O.lt(F, b, c):
  %e : O.lt(F, _, c)
  h

def lt_subst_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), e: {a == b : O.C(F)}, h: O.lt(F, c, a)) -> O.lt(F, c, b):
  %e : O.lt(F, c, _)
  h

# a < b gives a ≠ b, and b ≠ a
def ne_of_lt(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.lt(F, a, b)) -> {a == b : O.C(F)} -> Empty:
  e => O.lt_irrefl(F)(b)(lt_subst_l(~F, a, b, b, e, h))

def ne_of_gt(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.lt(F, b, a)) -> {a == b : O.C(F)} -> Empty:
  e => O.lt_irrefl(F)(b)(lt_subst_r(~F, a, b, b, e, h))

def lt_le(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.lt(F, a, b)) -> O.le(~F, a, b):
  Inl{h}

def le_refl(~F: O.OField, +a: O.C(F)) -> O.le(~F, a, a):
  Inr{{==}}

def lt_le_trans(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), h1: O.lt(F, a, b), h2: O.le(~F, b, c)) -> O.lt(F, a, c):
  match h2:
    case Inl{l}:
      O.lt_trans(F)(a, b, c)(h1)(l)
    case Inr{e}:
      %e : O.lt(F, a, _)
      h1

def le_lt_trans(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), h1: O.le(~F, a, b), h2: O.lt(F, b, c)) -> O.lt(F, a, c):
  match h1:
    case Inl{l}:
      O.lt_trans(F)(a, b, c)(l)(h2)
    case Inr{e}:
      %Equal.sym(O.C(F), a, b, e) : O.lt(F, _, c)
      h2

# a < 0 gives 0 < -a
def neg_pos(~F: O.OField, +a: O.C(F), h: O.lt(F, a, O.zero(F))) -> O.lt(F, O.zero(F), O.neg(F, a)):
  %O.add_neg(F)(a) : O.lt(F, _, O.neg(F, a))
  %FL.zero_add(~F, O.neg(F, a)) : O.lt(F, O.add(F, a, O.neg(F, a)), _)
  O.lt_add(F)(a, O.zero(F), O.neg(F, a))(h)

# 0 < a gives -a < 0
def pos_neg(~F: O.OField, +a: O.C(F), h: O.lt(F, O.zero(F), a)) -> O.lt(F, O.neg(F, a), O.zero(F)):
  %FL.zero_add(~F, O.neg(F, a)) : O.lt(F, _, O.zero(F))
  %O.add_neg(F)(a) : O.lt(F, O.add(F, O.zero(F), O.neg(F, a)), _)
  O.lt_add(F)(O.zero(F), a, O.neg(F, a))(h)

# 0 < a and 0 ≤ b give 0 < a + b
def pos_add.step(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.lt(F, O.zero(F), a)) -> O.lt(F, b, O.add(F, a, b)):
  %FL.zero_add(~F, b) : O.lt(F, _, O.add(F, a, b))
  O.lt_add(F)(O.zero(F), a, b)(ha)

def pos_add(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.lt(F, O.zero(F), a), hb: O.le(~F, O.zero(F), b)) -> O.lt(F, O.zero(F), O.add(F, a, b)):
  le_lt_trans(~F, O.zero(F), b, O.add(F, a, b), hb, pos_add.step(~F, a, b, ha))

def pos_add_r(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.le(~F, O.zero(F), a), hb: O.lt(F, O.zero(F), b)) -> O.lt(F, O.zero(F), O.add(F, a, b)):
  %FL.add_comm(~F, b, a) : O.lt(F, O.zero(F), _)
  pos_add(~F, b, a, hb, ha)

def nonneg_add(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.le(~F, O.zero(F), a), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), O.add(F, a, b)):
  match ha:
    case Inl{l}:
      Inl{pos_add(~F, a, b, l, hb)}
    case Inr{e}:
      %e : O.le(~F, O.zero(F), O.add(F, _, b))
      %Equal.sym(O.C(F), O.add(F, O.zero(F), b), b, FL.zero_add(~F, b)) : O.le(~F, O.zero(F), _)
      hb

def mul_nonneg(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.le(~F, O.zero(F), a), hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), O.mul(F, a, b)):
  match ha:
    case Inl{la}:
      match hb:
        case Inl{lb}:
          Inl{O.lt_mul(F)(a, b)(la)(lb)}
        case Inr{e}:
          %e : O.le(~F, O.zero(F), O.mul(F, a, _))
          Inr{FL.mul_zero(~F, a)}
    case Inr{e}:
      %e : O.le(~F, O.zero(F), O.mul(F, _, b))
      Inr{Equal.sym(O.C(F), O.mul(F, O.zero(F), b), O.zero(F), FL.zero_mul(~F, b))}

# a ≠ 0 gives 0 < a a
def sq_pos.go(~F: O.OField, +a: O.C(F), h: {a == O.zero(F) : O.C(F)} -> Empty, t: Or(O.lt(F, a, O.zero(F)), Or({a == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), a)))) -> O.lt(F, O.zero(F), O.mul(F, a, a)):
  match t:
    case Inl{+l}:
      %FL.neg_mul_neg(~F, a, a) : O.lt(F, O.zero(F), _)
      O.lt_mul(F)(O.neg(F, a), O.neg(F, a))(neg_pos(~F, a, l))(neg_pos(~F, a, l))
    case Inr{Inl{e}}:
      absurd(O.lt(F, O.zero(F), O.mul(F, a, a)), h(e))
    case Inr{Inr{+g}}:
      O.lt_mul(F)(a, a)(g)(g)

def sq_pos(~F: O.OField, +a: O.C(F), h: {a == O.zero(F) : O.C(F)} -> Empty) -> O.lt(F, O.zero(F), O.mul(F, a, a)):
  sq_pos.go(~F, a, h, O.lt_total(F)(a, O.zero(F)))

# 0 ≤ a a
def sq_nonneg.go(~F: O.OField, +a: O.C(F), t: Or(O.lt(F, a, O.zero(F)), Or({a == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), a)))) -> O.le(~F, O.zero(F), O.mul(F, a, a)):
  match t:
    case Inl{+l}:
      %FL.neg_mul_neg(~F, a, a) : O.le(~F, O.zero(F), _)
      Inl{O.lt_mul(F)(O.neg(F, a), O.neg(F, a))(neg_pos(~F, a, l))(neg_pos(~F, a, l))}
    case Inr{Inl{e}}:
      %Equal.sym(O.C(F), a, O.zero(F), e) : O.le(~F, O.zero(F), O.mul(F, _, _))
      Inr{FL.mul_zero(~F, O.zero(F))}
    case Inr{Inr{+g}}:
      Inl{O.lt_mul(F)(a, a)(g)(g)}

def sq_nonneg(~F: O.OField, +a: O.C(F)) -> O.le(~F, O.zero(F), O.mul(F, a, a)):
  sq_nonneg.go(~F, a, O.lt_total(F)(a, O.zero(F)))

# a a = 0 gives a = 0
def sq_zero.go(~F: O.OField, +a: O.C(F), +h: {O.mul(F, a, a) == O.zero(F) : O.C(F)}, t: Or(O.lt(F, a, O.zero(F)), Or({a == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), a)))) -> {a == O.zero(F) : O.C(F)}:
  match t:
    case Inl{l}:
      absurd({a == O.zero(F) : O.C(F)}, ne_of_gt(~F, O.mul(F, a, a), O.zero(F), sq_pos(~F, a, ne_of_lt(~F, a, O.zero(F), l)))(h))
    case Inr{Inl{e}}:
      e
    case Inr{Inr{g}}:
      absurd({a == O.zero(F) : O.C(F)}, ne_of_gt(~F, O.mul(F, a, a), O.zero(F), sq_pos(~F, a, ne_of_gt(~F, a, O.zero(F), g)))(h))

def sq_zero(~F: O.OField, +a: O.C(F), h: {O.mul(F, a, a) == O.zero(F) : O.C(F)}) -> {a == O.zero(F) : O.C(F)}:
  sq_zero.go(~F, a, h, O.lt_total(F)(a, O.zero(F)))

# a a + b b = 0 gives a = 0
def sumsq_zero.go(~F: O.OField, +a: O.C(F), +b: O.C(F), +h: {O.add(F, O.mul(F, a, a), O.mul(F, b, b)) == O.zero(F) : O.C(F)}, t: Or(O.lt(F, a, O.zero(F)), Or({a == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), a)))) -> {a == O.zero(F) : O.C(F)}:
  match t:
    case Inl{l}:
      absurd({a == O.zero(F) : O.C(F)}, ne_of_gt(~F, O.add(F, O.mul(F, a, a), O.mul(F, b, b)), O.zero(F), pos_add(~F, O.mul(F, a, a), O.mul(F, b, b), sq_pos(~F, a, ne_of_lt(~F, a, O.zero(F), l)), sq_nonneg(~F, b)))(h))
    case Inr{Inl{e}}:
      e
    case Inr{Inr{g}}:
      absurd({a == O.zero(F) : O.C(F)}, ne_of_gt(~F, O.add(F, O.mul(F, a, a), O.mul(F, b, b)), O.zero(F), pos_add(~F, O.mul(F, a, a), O.mul(F, b, b), sq_pos(~F, a, ne_of_gt(~F, a, O.zero(F), g)), sq_nonneg(~F, b)))(h))

def sumsq_zero(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {O.add(F, O.mul(F, a, a), O.mul(F, b, b)) == O.zero(F) : O.C(F)}) -> {a == O.zero(F) : O.C(F)}:
  sumsq_zero.go(~F, a, b, h, O.lt_total(F)(a, O.zero(F)))

# Inverses
# --------

# a ≠ 0: a (1/a) - 1 = 0, the relation a certificate uses
def inv_rel(~F: O.OField, +a: O.C(F), h: {a == O.zero(F) : O.C(F)} -> Empty) -> {O.sub(~F, O.mul(F, a, O.inv(F, a)), O.one(F)) == O.zero(F) : O.C(F)}:
  sub_of_eq(~F, O.mul(F, a, O.inv(F, a)), O.one(F), O.mul_inv(F)(a)(h))

# a ≠ 0 and a b = 0 give b = 0
def mul_eq_zero(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: {a == O.zero(F) : O.C(F)} -> Empty, h: {O.mul(F, a, b) == O.zero(F) : O.C(F)}) -> {b == O.zero(F) : O.C(F)}:
  cert2(~F, b, O.neg(F, b), O.sub(~F, O.mul(F, a, O.inv(F, a)), O.one(F)), O.inv(F, a), O.mul(F, a, b),
    FR.fring_eq(~F, [a, b, O.inv(F, a)], E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZVar{2n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, {==}),
    inv_rel(~F, a, ha), h)

# 0 < a gives 0 < 1/a
def inv_pos.neg(~F: O.OField, +a: O.C(F), +h: O.lt(F, O.zero(F), a), l: O.lt(F, O.inv(F, a), O.zero(F))) -> O.lt(F, O.zero(F), O.neg(F, O.one(F))):
  %O.mul_inv(F)(a)(ne_of_gt(~F, a, O.zero(F), h)) : O.lt(F, O.zero(F), O.neg(F, _))
  %FL.mul_neg(~F, a, O.inv(F, a)) : O.lt(F, O.zero(F), _)
  O.lt_mul(F)(a, O.neg(F, O.inv(F, a)))(h)(neg_pos(~F, O.inv(F, a), l))

def inv_pos.zero(~F: O.OField, +a: O.C(F), +h: O.lt(F, O.zero(F), a), e: {O.inv(F, a) == O.zero(F) : O.C(F)}) -> {O.zero(F) == O.one(F) : O.C(F)}:
  %O.mul_inv(F)(a)(ne_of_gt(~F, a, O.zero(F), h)) : {O.zero(F) == _ : O.C(F)}
  %Equal.sym(O.C(F), O.inv(F, a), O.zero(F), e) : {O.zero(F) == O.mul(F, a, _) : O.C(F)}
  FL.mul_zero(~F, a)

def inv_pos.go(~F: O.OField, +a: O.C(F), +h: O.lt(F, O.zero(F), a), t: Or(O.lt(F, O.inv(F, a), O.zero(F)), Or({O.inv(F, a) == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), O.inv(F, a))))) -> O.lt(F, O.zero(F), O.inv(F, a)):
  match t:
    case Inl{l}:
      absurd(O.lt(F, O.zero(F), O.inv(F, a)), O.lt_irrefl(F)(O.zero(F))(O.lt_trans(F)(O.zero(F), O.neg(F, O.one(F)), O.zero(F))(inv_pos.neg(~F, a, h, l))(pos_neg(~F, O.one(F), O.zero_lt_one(F)))))
    case Inr{Inl{e}}:
      absurd(O.lt(F, O.zero(F), O.inv(F, a)), ne_of_lt(~F, O.zero(F), O.one(F), O.zero_lt_one(F))(inv_pos.zero(~F, a, h, e)))
    case Inr{Inr{g}}:
      g

def inv_pos(~F: O.OField, +a: O.C(F), +h: O.lt(F, O.zero(F), a)) -> O.lt(F, O.zero(F), O.inv(F, a)):
  inv_pos.go(~F, a, h, O.lt_total(F)(O.inv(F, a), O.zero(F)))

# 0 < 2, and 2 (1/2) - 1 = 0
def two_pos(~F: O.OField) -> O.lt(F, O.zero(F), O.two(~F)):
  pos_add(~F, O.one(F), O.one(F), O.zero_lt_one(F), lt_le(~F, O.zero(F), O.one(F), O.zero_lt_one(F)))

def half_rel(~F: O.OField) -> {O.sub(~F, O.mul(F, O.two(~F), O.half(~F)), O.one(F)) == O.zero(F) : O.C(F)}:
  inv_rel(~F, O.two(~F), ne_of_gt(~F, O.two(~F), O.zero(F), two_pos(~F)))

# Square roots are unique: 0 ≤ x, 0 ≤ y and x x = y y give x = y
def sq_eq.yy(~F: O.OField, +x: O.C(F), +y: O.C(F), e: {O.zero(F) == x : O.C(F)}, h: {O.mul(F, x, x) == O.mul(F, y, y) : O.C(F)}) -> {O.mul(F, y, y) == O.zero(F) : O.C(F)}:
  %h : {_ == O.zero(F) : O.C(F)}
  %e : {O.mul(F, _, _) == O.zero(F) : O.C(F)}
  Equal.sym(O.C(F), O.zero(F), O.mul(F, O.zero(F), O.zero(F)), FL.mul_zero(~F, O.zero(F)))

def sq_eq(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.le(~F, O.zero(F), x), +hy: O.le(~F, O.zero(F), y), +h: {O.mul(F, x, x) == O.mul(F, y, y) : O.C(F)}) -> {x == y : O.C(F)}:
  match hx:
    case Inl{+lx}:
      eq_of_sub(~F, x, y, mul_eq_zero(~F, O.add(F, x, y), O.sub(~F, x, y), ne_of_gt(~F, O.add(F, x, y), O.zero(F), pos_add(~F, x, y, lx, hy)),
        cert1(~F, O.mul(F, O.add(F, x, y), O.sub(~F, x, y)), O.one(F), O.sub(~F, O.mul(F, x, x), O.mul(F, y, y)),
          FR.fring_eq(~F, [x, y], E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}}, {==}),
          sub_of_eq(~F, O.mul(F, x, x), O.mul(F, y, y), h))))
    case Inr{+e}:
      %e : {_ == y : O.C(F)}
      Equal.sym(O.C(F), y, O.zero(F), sq_zero(~F, y, sq_eq.yy(~F, x, y, e, h)))

def cert4(~F: O.OField, +x: O.C(F), +c1: O.C(F), +r1: O.C(F), +c2: O.C(F), +r2: O.C(F), +c3: O.C(F), +r3: O.C(F), +c4: O.C(F), +r4: O.C(F), hid: {x == O.add(F, O.add(F, O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)), O.mul(F, c3, r3)), O.mul(F, c4, r4)) : O.C(F)}, h1: {r1 == O.zero(F) : O.C(F)}, h2: {r2 == O.zero(F) : O.C(F)}, h3: {r3 == O.zero(F) : O.C(F)}, h4: {r4 == O.zero(F) : O.C(F)}) -> {x == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.add(F, O.add(F, O.add(F, O.mul(F, c1, r1), O.mul(F, c2, r2)), O.mul(F, c3, r3)), O.mul(F, c4, r4)), hid) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r1, O.zero(F), h1) : {O.add(F, O.add(F, O.add(F, O.mul(F, c1, _), O.mul(F, c2, r2)), O.mul(F, c3, r3)), O.mul(F, c4, r4)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r2, O.zero(F), h2) : {O.add(F, O.add(F, O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, _)), O.mul(F, c3, r3)), O.mul(F, c4, r4)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r3, O.zero(F), h3) : {O.add(F, O.add(F, O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, O.zero(F))), O.mul(F, c3, _)), O.mul(F, c4, r4)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), r4, O.zero(F), h4) : {O.add(F, O.add(F, O.add(F, O.mul(F, c1, O.zero(F)), O.mul(F, c2, O.zero(F))), O.mul(F, c3, O.zero(F))), O.mul(F, c4, _)) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c1) : {O.add(F, O.add(F, O.add(F, _, O.mul(F, c2, O.zero(F))), O.mul(F, c3, O.zero(F))), O.mul(F, c4, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c2) : {O.add(F, O.add(F, O.add(F, O.zero(F), _), O.mul(F, c3, O.zero(F))), O.mul(F, c4, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c3) : {O.add(F, O.add(F, O.add(F, O.zero(F), O.zero(F)), _), O.mul(F, c4, O.zero(F))) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, c4) : {O.add(F, O.add(F, O.add(F, O.zero(F), O.zero(F)), O.zero(F)), _) == O.zero(F) : O.C(F)}
  %FL.add_zero(~F, O.zero(F)) : {O.add(F, O.add(F, _, O.zero(F)), O.zero(F)) == O.zero(F) : O.C(F)}
  %FL.add_zero(~F, O.zero(F)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
  O.add_zero(F)(O.zero(F))
