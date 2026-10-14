# Demo: a meaning proven in every ordered field, from the axioms alone. The
# field is a template parameter, so Bend checks these proofs with F's
# operations opaque, and the axioms may be used as often as needed. This is
# the Fix case of means_sound (ROADMAP.bend): a solution of v - k = 0 has
# v = k.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/sketch.bend as K

# 0 + a = a
def zero_add(~F: O.OField, +a: O.C(F)) -> {O.add(F, O.zero(F), a) == a : O.C(F)}:
  %O.add_comm(F)(a, O.zero(F)) : {_ == a : O.C(F)}
  %O.add_zero(F)(a) : {O.add(F, a, O.zero(F)) == _ : O.C(F)}
  {==}

# -a + a = 0
def neg_add(~F: O.OField, +a: O.C(F)) -> {O.add(F, O.neg(F, a), a) == O.zero(F) : O.C(F)}:
  %O.add_comm(F)(a, O.neg(F, a)) : {_ == O.zero(F) : O.C(F)}
  %O.add_neg(F)(a) : {O.add(F, a, O.neg(F, a)) == _ : O.C(F)}
  {==}

# a - b = 0 gives a = b: a = a + (-b + b) = (a - b) + b = 0 + b = b
def sub_zero(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {O.sub(~F, a, b) == O.zero(F) : O.C(F)}) -> {a == b : O.C(F)}:
  %zero_add(~F, b) : {a == _ : O.C(F)}
  %h : {a == O.add(F, _, b) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.add(F, a, O.neg(F, b)), b), O.add(F, a, O.add(F, O.neg(F, b), b)), O.add_assoc(F)(a, O.neg(F, b), b)) : {a == _ : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.neg(F, b), b), O.zero(F), neg_add(~F, b)) : {a == O.add(F, a, _) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, a, O.zero(F)), a, O.add_zero(F)(a)) : {a == _ : O.C(F)}
  {==}

# the Fix case of means_sound, in every ordered field
def fix_sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +v: Nat, +k: S.Q, h: K.Constraint.holds(~F, env, es, K.Fix{v, k})) -> K.Constraint.means(~F, env, es, K.Fix{v, k}):
  ((hz, u1), u2) = h
  sub_zero(~F, O.lookup(~F, env, v), O.ofq(~F, k), hz)
