# The rationals inside every ordered field: O.ofq sends n/d to n * (1/d).
# It respects Q.eq and the operations, and it preserves and reflects the
# order, so a rational fact decided by computation holds in every ordered
# field. Each identity is one certificate (lib/ford.bend) with the
# denominators' inverses as atoms; positivity of denominators is by
# induction on the binary positive.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./zord.bend as ZO
import ./qord.bend as LQO


# Positives are positive
# ----------------------

def ofp_pos(~F: O.OField, p: S.Pos) -> O.lt(F, O.zero(F), O.ofp(~F, p)):
  match p:
    case S.XH{}:
      O.zero_lt_one(F)
    case S.XO{+q}:
      +h = ofp_pos(~F, q)
      FO.pos_add(~F, O.ofp(~F, q), O.ofp(~F, q), h, FO.lt_le(~F, O.zero(F), O.ofp(~F, q), h))
    case S.XI{+q}:
      +h = ofp_pos(~F, q)
      FO.pos_add(~F, O.add(F, O.ofp(~F, q), O.ofp(~F, q)), O.one(F), FO.pos_add(~F, O.ofp(~F, q), O.ofp(~F, q), h, FO.lt_le(~F, O.zero(F), O.ofp(~F, q), h)), FO.lt_le(~F, O.zero(F), O.one(F), O.zero_lt_one(F)))

def ofp_ne(~F: O.OField, +p: S.Pos) -> {O.ofp(~F, p) == O.zero(F) : O.C(F)} -> Empty:
  FO.ne_of_gt(~F, O.ofp(~F, p), O.zero(F), ofp_pos(~F, p))

# p (1/p) - 1 = 0
def ofp_rel(~F: O.OField, +p: S.Pos) -> {O.sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, p))), O.one(F)) == O.zero(F) : O.C(F)}:
  FO.inv_rel(~F, O.ofp(~F, p), ofp_ne(~F, p))

# p q (1/(p q)) - 1 = 0
def ofp2_rel(~F: O.OField, +p: S.Pos, +q: S.Pos) -> {O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, p), O.ofp(~F, q)), O.inv(F, O.mul(F, O.ofp(~F, p), O.ofp(~F, q)))), O.one(F)) == O.zero(F) : O.C(F)}:
  FO.inv_rel(~F, O.mul(F, O.ofp(~F, p), O.ofp(~F, q)), FO.ne_of_gt(~F, O.mul(F, O.ofp(~F, p), O.ofp(~F, q)), O.zero(F), O.lt_mul(F)(O.ofp(~F, p), O.ofp(~F, q))(ofp_pos(~F, p))(ofp_pos(~F, q))))

# a positive integer is positive
def ofz_pos(~F: O.OField, s: S.Z, h: ZO.pos(s)) -> O.lt(F, O.zero(F), O.ofz(~F, s)):
  match s:
    case S.Z0{}:
      FO.absurd(O.lt(F, O.zero(F), O.zero(F)), h)
    case S.Zpos{p}:
      ofp_pos(~F, p)
    case S.Zneg{p}:
      FO.absurd(O.lt(F, O.zero(F), O.neg(F, O.ofp(~F, p))), h)

# Integer facts in F
# ------------------

def ofz_eq(~F: O.OField, +u: S.Z, +v: S.Z, h: {u == v : S.Z}) -> {O.ofz(~F, u) == O.ofz(~F, v) : O.C(F)}:
  %h : {O.ofz(~F, u) == O.ofz(~F, _) : O.C(F)}
  {==}

# u p - v q, for u p = v q in Z
def ofz_cross(~F: O.OField, +u: S.Z, +p: S.Pos, +v: S.Z, +q: S.Pos, h: {S.Z.mul(u, S.Zpos{p}) == S.Z.mul(v, S.Zpos{q}) : S.Z}) -> {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == O.zero(F) : O.C(F)}:
  FO.sub_of_eq(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q)),
    Equal.trans(O.C(F), O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.ofz(~F, S.Z.mul(u, S.Zpos{p})), O.mul(F, O.ofz(~F, v), O.ofp(~F, q)), FR.ofz_mul(~F, u, S.Zpos{p}),
      Equal.trans(O.C(F), O.ofz(~F, S.Z.mul(u, S.Zpos{p})), O.ofz(~F, S.Z.mul(v, S.Zpos{q})), O.mul(F, O.ofz(~F, v), O.ofp(~F, q)), ofz_eq(~F, S.Z.mul(u, S.Zpos{p}), S.Z.mul(v, S.Zpos{q}), h),
        Equal.sym(O.C(F), O.mul(F, O.ofz(~F, v), O.ofp(~F, q)), O.ofz(~F, S.Z.mul(v, S.Zpos{q})), FR.ofz_mul(~F, v, S.Zpos{q})))))

# u p - v q is the integer u p - v q
def ofz_dif(~F: O.OField, +u: S.Z, +p: S.Pos, +v: S.Z, +q: S.Pos) -> {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == O.ofz(~F, S.Z.sub(S.Z.mul(u, S.Zpos{p}), S.Z.mul(v, S.Zpos{q}))) : O.C(F)}:
  %FR.ofz_add(~F, S.Z.mul(u, S.Zpos{p}), S.Z.neg(S.Z.mul(v, S.Zpos{q}))) : {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == _ : O.C(F)}
  %FR.ofz_neg(~F, S.Z.mul(v, S.Zpos{q})) : {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == O.add(F, O.ofz(~F, S.Z.mul(u, S.Zpos{p})), _) : O.C(F)}
  %FR.ofz_mul(~F, u, S.Zpos{p}) : {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == O.add(F, _, O.neg(F, O.ofz(~F, S.Z.mul(v, S.Zpos{q})))) : O.C(F)}
  %FR.ofz_mul(~F, v, S.Zpos{q}) : {O.sub(~F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.mul(F, O.ofz(~F, v), O.ofp(~F, q))) == O.add(F, O.mul(F, O.ofz(~F, u), O.ofp(~F, p)), O.neg(F, _)) : O.C(F)}
  {==}

# 0 < b - a gives a < b
def lt_of_sub(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.lt(F, O.zero(F), O.sub(~F, b, a))) -> O.lt(F, a, b):
  FO.lt_subst_l(~F, O.add(F, O.zero(F), a), a, b, FL.zero_add(~F, a),
    FO.lt_subst_r(~F, O.add(F, O.sub(~F, b, a), a), b, O.add(F, O.zero(F), a), FR.fring_eq(~F, [b, a], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZVar{0n}, {==}),
      O.lt_add(F)(O.zero(F), O.sub(~F, b, a), a)(h)))

# The embedding
# -------------

def ofq_eq(~F: O.OField, +x: S.Q, +y: S.Q, h: S.Q.eq(x, y)) -> {O.ofq(~F, x) == O.ofq(~F, y) : O.C(F)}:
  FO.eq_of_sub(~F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), FO.cert3(~F, O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.one(F)), O.neg(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.one(F)), O.mul(F, O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)))), FR.fring_eq(~F, [O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y)))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}), ofp_rel(~F, S.Q.den(x)), ofp_rel(~F, S.Q.den(y)), ofz_cross(~F, S.Q.num(x), S.Q.den(y), S.Q.num(y), S.Q.den(x), h)))

def ofq_add(~F: O.OField, +x: S.Q, +y: S.Q) -> {O.ofq(~F, S.Q.add(x, y)) == O.add(F, O.ofq(~F, x), O.ofq(~F, y)) : O.C(F)}:
  %FR.ofz_add(~F, S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)})) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(S.Q.den(x), S.Q.den(y))))) == O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  %FR.ofz_mul(~F, S.Q.num(x), S.Zpos{S.Q.den(y)}) : {O.mul(F, O.add(F, _, O.ofz(~F, S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}))), O.inv(F, O.ofp(~F, S.Pos.mul(S.Q.den(x), S.Q.den(y))))) == O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  %FR.ofz_mul(~F, S.Q.num(y), S.Zpos{S.Q.den(x)}) : {O.mul(F, O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), _), O.inv(F, O.ofp(~F, S.Pos.mul(S.Q.den(x), S.Q.den(y))))) == O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  %FR.ofz_mul(~F, S.Zpos{S.Q.den(x)}, S.Zpos{S.Q.den(y)}) : {O.mul(F, O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)))), O.inv(F, _)) == O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  FO.eq_of_sub(~F, O.mul(F, O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))), FO.cert3(~F, O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))))), O.neg(F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.one(F)), O.add(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))], E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{6n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), ofp_rel(~F, S.Q.den(x)), ofp_rel(~F, S.Q.den(y)), ofp2_rel(~F, S.Q.den(x), S.Q.den(y))))

def ofq_mul(~F: O.OField, +x: S.Q, +y: S.Q) -> {O.ofq(~F, S.Q.mul(x, y)) == O.mul(F, O.ofq(~F, x), O.ofq(~F, y)) : O.C(F)}:
  %FR.ofz_mul(~F, S.Q.num(x), S.Q.num(y)) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(S.Q.den(x), S.Q.den(y))))) == O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  %FR.ofz_mul(~F, S.Zpos{S.Q.den(x)}, S.Zpos{S.Q.den(y)}) : {O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, _)) == O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))) : O.C(F)}
  FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y))))), FO.cert3(~F, O.sub(~F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))))), O.neg(F, O.mul(F, O.mul(F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.ofp(~F, S.Q.den(y))), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.one(F)), O.neg(F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.one(F)), O.mul(F, O.mul(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y))), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))), O.inv(F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y))))], E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{6n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{6n}}, E.ZVar{3n}}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), ofp_rel(~F, S.Q.den(x)), ofp_rel(~F, S.Q.den(y)), ofp2_rel(~F, S.Q.den(x), S.Q.den(y))))

def ofq_neg(~F: O.OField, +x: S.Q) -> {O.ofq(~F, S.Q.neg(x)) == O.neg(F, O.ofq(~F, x)) : O.C(F)}:
  %FR.ofz_neg(~F, S.Q.num(x)) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.Q.den(x)))) == O.neg(F, O.ofq(~F, x)) : O.C(F)}
  FL.neg_mul(~F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x))))

def ofq_zero(~F: O.OField) -> {O.ofq(~F, S.Q{S.Z0{}, S.XH{}}) == O.zero(F) : O.C(F)}:
  FL.zero_mul(~F, O.inv(F, O.one(F)))

def ofq_one(~F: O.OField) -> {O.ofq(~F, S.Q{S.Zpos{S.XH{}}, S.XH{}}) == O.one(F) : O.C(F)}:
  O.mul_inv(F)(O.one(F))(ofp_ne(~F, S.XH{}))

# x < y gives ofq x < ofq y: ofq y - ofq x is the cross difference over p q
def ofq_lt(~F: O.OField, +x: S.Q, +y: S.Q, h: S.Q.lt(x, y)) -> O.lt(F, O.ofq(~F, x), O.ofq(~F, y)):
  +d = FO.lt_subst_r(~F, O.ofz(~F, LQO.dif(x, y)), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.zero(F),
    Equal.sym(O.C(F), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.ofz(~F, LQO.dif(x, y)), ofz_dif(~F, S.Q.num(y), S.Q.den(x), S.Q.num(x), S.Q.den(y))),
    ofz_pos(~F, LQO.dif(x, y), LQO.lt_dif(x, y, h)))
  +ij = O.lt_mul(F)(O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))))(FO.inv_pos(~F, O.ofp(~F, S.Q.den(x)), ofp_pos(~F, S.Q.den(x))))(FO.inv_pos(~F, O.ofp(~F, S.Q.den(y)), ofp_pos(~F, S.Q.den(y))))
  lt_of_sub(~F, O.ofq(~F, x), O.ofq(~F, y),
    FO.lt_subst_r(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.mul(F, O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x))))), O.zero(F),
      FO.eq_of_sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.mul(F, O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x))))), FO.cert2(~F, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.mul(F, O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y))))), O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))))), O.mul(F, O.ofz(~F, S.Q.num(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(x)), O.inv(F, O.ofp(~F, S.Q.den(x)))), O.one(F)), O.neg(F, O.mul(F, O.ofz(~F, S.Q.num(x)), O.inv(F, O.ofp(~F, S.Q.den(x))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(y)))), O.one(F)), FR.fring_eq(~F, [O.ofz(~F, S.Q.num(x)), O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x)), O.ofp(~F, S.Q.den(y)), O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y)))], E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{5n}}, E.ZMul{E.ZVar{0n}, E.ZVar{4n}}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), ofp_rel(~F, S.Q.den(x)), ofp_rel(~F, S.Q.den(y)))),
      O.lt_mul(F)(O.sub(~F, O.mul(F, O.ofz(~F, S.Q.num(y)), O.ofp(~F, S.Q.den(x))), O.mul(F, O.ofz(~F, S.Q.num(x)), O.ofp(~F, S.Q.den(y)))), O.mul(F, O.inv(F, O.ofp(~F, S.Q.den(x))), O.inv(F, O.ofp(~F, S.Q.den(y)))))(d)(ij)))

# and back: ofq x < ofq y gives x < y
def ofq_lt_rev.go(~F: O.OField, +x: S.Q, +y: S.Q, +h: O.lt(F, O.ofq(~F, x), O.ofq(~F, y)), t: Or(S.Q.lt(x, y), Or(S.Q.eq(x, y), S.Q.lt(y, x)))) -> S.Q.lt(x, y):
  match t:
    case Inl{l}:
      l
    case Inr{Inl{e}}:
      FO.absurd(S.Q.lt(x, y), O.lt_irrefl(F)(O.ofq(~F, y))(FO.lt_subst_l(~F, O.ofq(~F, x), O.ofq(~F, y), O.ofq(~F, y), ofq_eq(~F, x, y, e), h)))
    case Inr{Inr{g}}:
      FO.absurd(S.Q.lt(x, y), O.lt_irrefl(F)(O.ofq(~F, x))(O.lt_trans(F)(O.ofq(~F, x), O.ofq(~F, y), O.ofq(~F, x))(h)(ofq_lt(~F, y, x, g))))

def ofq_lt_rev(~F: O.OField, +x: S.Q, +y: S.Q, +h: O.lt(F, O.ofq(~F, x), O.ofq(~F, y))) -> S.Q.lt(x, y):
  ofq_lt_rev.go(~F, x, y, h, LQO.q_lt_total(x, y))

# ofq x = ofq y gives x = y
def ofq_eq_rev.go(~F: O.OField, +x: S.Q, +y: S.Q, +e: {O.ofq(~F, x) == O.ofq(~F, y) : O.C(F)}, t: Or(S.Q.lt(x, y), Or(S.Q.eq(x, y), S.Q.lt(y, x)))) -> S.Q.eq(x, y):
  match t:
    case Inl{l}:
      FO.absurd(S.Q.eq(x, y), O.lt_irrefl(F)(O.ofq(~F, y))(FO.lt_subst_l(~F, O.ofq(~F, x), O.ofq(~F, y), O.ofq(~F, y), e, ofq_lt(~F, x, y, l))))
    case Inr{Inl{q}}:
      q
    case Inr{Inr{g}}:
      FO.absurd(S.Q.eq(x, y), O.lt_irrefl(F)(O.ofq(~F, y))(FO.lt_subst_r(~F, O.ofq(~F, x), O.ofq(~F, y), O.ofq(~F, y), e, ofq_lt(~F, y, x, g))))

def ofq_eq_rev(~F: O.OField, +x: S.Q, +y: S.Q, +e: {O.ofq(~F, x) == O.ofq(~F, y) : O.C(F)}) -> S.Q.eq(x, y):
  ofq_eq_rev.go(~F, x, y, e, LQO.q_lt_total(x, y))
