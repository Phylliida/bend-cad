# The commutative ring laws in every ordered field, stated as lib/zlaws.bend
# states them for the integers ({target == source}, so a rewrite
# %law(..) : P turns the source form into the target form), plus the facts
# about 0 and negation that the axioms leave implicit. Each is proven from
# the axioms of spec/field.bend; F is a template parameter.

import Base
import ../spec/field.bend as O

# 0 + x = x
def zero_add(~F: O.OField, +x: O.C(F)) -> {O.add(F, O.zero(F), x) == x : O.C(F)}:
  %O.add_comm(F)(x, O.zero(F)) : {_ == x : O.C(F)}
  %O.add_zero(F)(x) : {O.add(F, x, O.zero(F)) == _ : O.C(F)}
  {==}

# -x + x = 0
def neg_add_l(~F: O.OField, +x: O.C(F)) -> {O.add(F, O.neg(F, x), x) == O.zero(F) : O.C(F)}:
  %O.add_comm(F)(x, O.neg(F, x)) : {_ == O.zero(F) : O.C(F)}
  %O.add_neg(F)(x) : {O.add(F, x, O.neg(F, x)) == _ : O.C(F)}
  {==}

# x + y = y + x
def add_comm(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.add(F, x, y) == O.add(F, y, x) : O.C(F)}:
  %O.add_comm(F)(y, x) : {_ == O.add(F, y, x) : O.C(F)}
  {==}

# x + (y + z) = (x + y) + z
def add_assoc(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.add(F, x, O.add(F, y, z)) == O.add(F, O.add(F, x, y), z) : O.C(F)}:
  %O.add_assoc(F)(x, y, z) : {_ == O.add(F, O.add(F, x, y), z) : O.C(F)}
  {==}

# x + (y + z) = y + (x + z)
def add_swap(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.add(F, x, O.add(F, y, z)) == O.add(F, y, O.add(F, x, z)) : O.C(F)}:
  %O.add_assoc(F)(y, x, z) : {O.add(F, x, O.add(F, y, z)) == _ : O.C(F)}
  %O.add_comm(F)(x, y) : {O.add(F, x, O.add(F, y, z)) == O.add(F, _, z) : O.C(F)}
  %O.add_assoc(F)(x, y, z) : {_ == O.add(F, O.add(F, x, y), z) : O.C(F)}
  {==}

# (x + y) + (z + w) = (x + z) + (y + w)
def add_shuffle(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F), +w: O.C(F)) -> {O.add(F, O.add(F, x, y), O.add(F, z, w)) == O.add(F, O.add(F, x, z), O.add(F, y, w)) : O.C(F)}:
  %add_assoc(~F, x, y, O.add(F, z, w)) : {_ == O.add(F, O.add(F, x, z), O.add(F, y, w)) : O.C(F)}
  %add_swap(~F, z, y, w) : {O.add(F, x, _) == O.add(F, O.add(F, x, z), O.add(F, y, w)) : O.C(F)}
  %add_assoc(~F, x, z, O.add(F, y, w)) : {O.add(F, x, O.add(F, z, O.add(F, y, w))) == _ : O.C(F)}
  {==}

# x = x + 0
def add_zero(~F: O.OField, +x: O.C(F)) -> {x == O.add(F, x, O.zero(F)) : O.C(F)}:
  %O.add_zero(F)(x) : {_ == O.add(F, x, O.zero(F)) : O.C(F)}
  {==}

# x * y = y * x
def mul_comm(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.mul(F, x, y) == O.mul(F, y, x) : O.C(F)}:
  %O.mul_comm(F)(y, x) : {_ == O.mul(F, y, x) : O.C(F)}
  {==}

# x * (y * z) = (x * y) * z
def mul_assoc(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.mul(F, x, O.mul(F, y, z)) == O.mul(F, O.mul(F, x, y), z) : O.C(F)}:
  %O.mul_assoc(F)(x, y, z) : {_ == O.mul(F, O.mul(F, x, y), z) : O.C(F)}
  {==}

# x * (y * z) = y * (x * z)
def mul_swap(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.mul(F, x, O.mul(F, y, z)) == O.mul(F, y, O.mul(F, x, z)) : O.C(F)}:
  %O.mul_assoc(F)(y, x, z) : {O.mul(F, x, O.mul(F, y, z)) == _ : O.C(F)}
  %O.mul_comm(F)(x, y) : {O.mul(F, x, O.mul(F, y, z)) == O.mul(F, _, z) : O.C(F)}
  %O.mul_assoc(F)(x, y, z) : {_ == O.mul(F, O.mul(F, x, y), z) : O.C(F)}
  {==}

# (x * z) * (y * w) = (x * y) * (z * w)
def mul_shuffle(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F), +w: O.C(F)) -> {O.mul(F, O.mul(F, x, z), O.mul(F, y, w)) == O.mul(F, O.mul(F, x, y), O.mul(F, z, w)) : O.C(F)}:
  %mul_assoc(~F, x, z, O.mul(F, y, w)) : {_ == O.mul(F, O.mul(F, x, y), O.mul(F, z, w)) : O.C(F)}
  %mul_swap(~F, y, z, w) : {O.mul(F, x, _) == O.mul(F, O.mul(F, x, y), O.mul(F, z, w)) : O.C(F)}
  %mul_assoc(~F, x, y, O.mul(F, z, w)) : {O.mul(F, x, O.mul(F, y, O.mul(F, z, w))) == _ : O.C(F)}
  {==}

# x = x * 1
def mul_one(~F: O.OField, +x: O.C(F)) -> {x == O.mul(F, x, O.one(F)) : O.C(F)}:
  %O.mul_one(F)(x) : {_ == O.mul(F, x, O.one(F)) : O.C(F)}
  {==}

# x = 1 * x
def one_mul(~F: O.OField, +x: O.C(F)) -> {x == O.mul(F, O.one(F), x) : O.C(F)}:
  %O.mul_comm(F)(x, O.one(F)) : {x == _ : O.C(F)}
  mul_one(~F, x)

# x * y + x * z = x * (y + z)
def mul_add_l(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.add(F, O.mul(F, x, y), O.mul(F, x, z)) == O.mul(F, x, O.add(F, y, z)) : O.C(F)}:
  %O.mul_add(F)(x, y, z) : {_ == O.mul(F, x, O.add(F, y, z)) : O.C(F)}
  {==}

# x * z + y * z = (x + y) * z
def mul_add_r(~F: O.OField, +x: O.C(F), +y: O.C(F), +z: O.C(F)) -> {O.add(F, O.mul(F, x, z), O.mul(F, y, z)) == O.mul(F, O.add(F, x, y), z) : O.C(F)}:
  %O.mul_comm(F)(z, O.add(F, x, y)) : {O.add(F, O.mul(F, x, z), O.mul(F, y, z)) == _ : O.C(F)}
  %mul_add_l(~F, z, x, y) : {O.add(F, O.mul(F, x, z), O.mul(F, y, z)) == _ : O.C(F)}
  %O.mul_comm(F)(x, z) : {O.add(F, O.mul(F, x, z), O.mul(F, y, z)) == O.add(F, _, O.mul(F, z, y)) : O.C(F)}
  %O.mul_comm(F)(y, z) : {O.add(F, O.mul(F, x, z), O.mul(F, y, z)) == O.add(F, O.mul(F, x, z), _) : O.C(F)}
  {==}

# Zero and negation
# -----------------

# x + x = x only for x = 0
def double_zero(~F: O.OField, +x: O.C(F), h: {O.add(F, x, x) == x : O.C(F)}) -> {x == O.zero(F) : O.C(F)}:
  %O.add_zero(F)(x) : {_ == O.zero(F) : O.C(F)}
  %O.add_neg(F)(x) : {O.add(F, x, _) == O.zero(F) : O.C(F)}
  %O.add_assoc(F)(x, x, O.neg(F, x)) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, x, x), x, h) : {O.add(F, _, O.neg(F, x)) == O.zero(F) : O.C(F)}
  %O.add_neg(F)(x) : {O.add(F, x, O.neg(F, x)) == _ : O.C(F)}
  {==}

# x * 0 + x * 0 = x * 0
def mul_zero.h(~F: O.OField, +x: O.C(F)) -> {O.add(F, O.mul(F, x, O.zero(F)), O.mul(F, x, O.zero(F))) == O.mul(F, x, O.zero(F)) : O.C(F)}:
  %O.mul_add(F)(x, O.zero(F), O.zero(F)) : {_ == O.mul(F, x, O.zero(F)) : O.C(F)}
  %add_zero(~F, O.zero(F)) : {O.mul(F, x, _) == O.mul(F, x, O.zero(F)) : O.C(F)}
  {==}

# 0 = x * 0
def mul_zero(~F: O.OField, +x: O.C(F)) -> {O.zero(F) == O.mul(F, x, O.zero(F)) : O.C(F)}:
  Equal.sym(O.C(F), O.mul(F, x, O.zero(F)), O.zero(F), double_zero(~F, O.mul(F, x, O.zero(F)), mul_zero.h(~F, x)))

# 0 * x = 0
def zero_mul(~F: O.OField, +x: O.C(F)) -> {O.mul(F, O.zero(F), x) == O.zero(F) : O.C(F)}:
  %O.mul_comm(F)(x, O.zero(F)) : {_ == O.zero(F) : O.C(F)}
  %mul_zero(~F, x) : {_ == O.zero(F) : O.C(F)}
  {==}

# the negative is unique: a + b = 0 gives b = -a
def neg_uniq(~F: O.OField, +a: O.C(F), +b: O.C(F), h: {O.add(F, a, b) == O.zero(F) : O.C(F)}) -> {b == O.neg(F, a) : O.C(F)}:
  %zero_add(~F, b) : {_ == O.neg(F, a) : O.C(F)}
  %neg_add_l(~F, a) : {O.add(F, _, b) == O.neg(F, a) : O.C(F)}
  %add_assoc(~F, O.neg(F, a), a, b) : {_ == O.neg(F, a) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, a, b), O.zero(F), h) : {O.add(F, O.neg(F, a), _) == O.neg(F, a) : O.C(F)}
  %O.add_zero(F)(O.neg(F, a)) : {O.add(F, O.neg(F, a), O.zero(F)) == _ : O.C(F)}
  {==}

# --x = x
def neg_neg(~F: O.OField, +x: O.C(F)) -> {O.neg(F, O.neg(F, x)) == x : O.C(F)}:
  Equal.sym(O.C(F), x, O.neg(F, O.neg(F, x)), neg_uniq(~F, O.neg(F, x), x, neg_add_l(~F, x)))

# 0 = -0
def neg_zero(~F: O.OField) -> {O.zero(F) == O.neg(F, O.zero(F)) : O.C(F)}:
  neg_uniq(~F, O.zero(F), O.zero(F), O.add_zero(F)(O.zero(F)))

# (x + y) + (-x + -y) = 0
def neg_add.sum(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.add(F, O.add(F, x, y), O.add(F, O.neg(F, x), O.neg(F, y))) == O.zero(F) : O.C(F)}:
  %add_shuffle(~F, x, O.neg(F, x), y, O.neg(F, y)) : {_ == O.zero(F) : O.C(F)}
  %O.add_zero(F)(O.zero(F)) : {O.add(F, O.add(F, x, O.neg(F, x)), O.add(F, y, O.neg(F, y))) == _ : O.C(F)}
  %O.add_neg(F)(x) : {O.add(F, O.add(F, x, O.neg(F, x)), O.add(F, y, O.neg(F, y))) == O.add(F, _, O.zero(F)) : O.C(F)}
  %O.add_neg(F)(y) : {O.add(F, O.add(F, x, O.neg(F, x)), O.add(F, y, O.neg(F, y))) == O.add(F, O.add(F, x, O.neg(F, x)), _) : O.C(F)}
  {==}

# -x + -y = -(x + y)
def neg_add(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.add(F, O.neg(F, x), O.neg(F, y)) == O.neg(F, O.add(F, x, y)) : O.C(F)}:
  neg_uniq(~F, O.add(F, x, y), O.add(F, O.neg(F, x), O.neg(F, y)), neg_add.sum(~F, x, y))

# x * y + -x * y = 0
def neg_mul.sum(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.add(F, O.mul(F, x, y), O.mul(F, O.neg(F, x), y)) == O.zero(F) : O.C(F)}:
  %zero_mul(~F, y) : {O.add(F, O.mul(F, x, y), O.mul(F, O.neg(F, x), y)) == _ : O.C(F)}
  %O.add_neg(F)(x) : {O.add(F, O.mul(F, x, y), O.mul(F, O.neg(F, x), y)) == O.mul(F, _, y) : O.C(F)}
  %mul_add_r(~F, x, O.neg(F, x), y) : {O.add(F, O.mul(F, x, y), O.mul(F, O.neg(F, x), y)) == _ : O.C(F)}
  {==}

# -x * y = -(x * y)
def neg_mul(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.mul(F, O.neg(F, x), y) == O.neg(F, O.mul(F, x, y)) : O.C(F)}:
  neg_uniq(~F, O.mul(F, x, y), O.mul(F, O.neg(F, x), y), neg_mul.sum(~F, x, y))

# x * -y = -(x * y)
def mul_neg(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.mul(F, x, O.neg(F, y)) == O.neg(F, O.mul(F, x, y)) : O.C(F)}:
  %O.mul_comm(F)(O.neg(F, y), x) : {_ == O.neg(F, O.mul(F, x, y)) : O.C(F)}
  %O.mul_comm(F)(y, x) : {O.mul(F, O.neg(F, y), x) == O.neg(F, _) : O.C(F)}
  neg_mul(~F, y, x)

# -x * -y = x * y
def neg_mul_neg(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.mul(F, O.neg(F, x), O.neg(F, y)) == O.mul(F, x, y) : O.C(F)}:
  %Equal.sym(O.C(F), O.mul(F, O.neg(F, x), O.neg(F, y)), O.neg(F, O.mul(F, x, O.neg(F, y))), neg_mul(~F, x, O.neg(F, y))) : {_ == O.mul(F, x, y) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, x, O.neg(F, y)), O.neg(F, O.mul(F, x, y)), mul_neg(~F, x, y)) : {O.neg(F, _) == O.mul(F, x, y) : O.C(F)}
  neg_neg(~F, O.mul(F, x, y))

# x - 0 = x
def sub_zero(~F: O.OField, +x: O.C(F)) -> {O.add(F, x, O.neg(F, O.zero(F))) == x : O.C(F)}:
  %neg_zero(~F) : {O.add(F, x, _) == x : O.C(F)}
  %O.add_zero(F)(x) : {O.add(F, x, O.zero(F)) == _ : O.C(F)}
  {==}

# (1 + a) - (1 + b) = a - b
def sub_succ(~F: O.OField, +a: O.C(F), +b: O.C(F)) -> {O.add(F, O.add(F, O.one(F), a), O.neg(F, O.add(F, O.one(F), b))) == O.add(F, a, O.neg(F, b)) : O.C(F)}:
  %neg_add(~F, O.one(F), b) : {O.add(F, O.add(F, O.one(F), a), _) == O.add(F, a, O.neg(F, b)) : O.C(F)}
  %add_shuffle(~F, O.one(F), O.neg(F, O.one(F)), a, O.neg(F, b)) : {_ == O.add(F, a, O.neg(F, b)) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.one(F), O.neg(F, O.one(F))), O.zero(F), O.add_neg(F)(O.one(F))) : {O.add(F, _, O.add(F, a, O.neg(F, b))) == O.add(F, a, O.neg(F, b)) : O.C(F)}
  zero_add(~F, O.add(F, a, O.neg(F, b)))

# (a - b)(c - d) = (ac + bd) - (ad + bc)
def mul_sub(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F)) -> {O.mul(F, O.add(F, a, O.neg(F, b)), O.add(F, c, O.neg(F, d))) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}:
  %mul_add_r(~F, a, O.neg(F, b), O.add(F, c, O.neg(F, d))) : {_ == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %mul_add_l(~F, a, c, O.neg(F, d)) : {O.add(F, _, O.mul(F, O.neg(F, b), O.add(F, c, O.neg(F, d)))) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %mul_add_l(~F, O.neg(F, b), c, O.neg(F, d)) : {O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, a, O.neg(F, d))), _) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, a, O.neg(F, d)), O.neg(F, O.mul(F, a, d)), mul_neg(~F, a, d)) : {O.add(F, O.add(F, O.mul(F, a, c), _), O.add(F, O.mul(F, O.neg(F, b), c), O.mul(F, O.neg(F, b), O.neg(F, d)))) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, O.neg(F, b), c), O.neg(F, O.mul(F, b, c)), neg_mul(~F, b, c)) : {O.add(F, O.add(F, O.mul(F, a, c), O.neg(F, O.mul(F, a, d))), O.add(F, _, O.mul(F, O.neg(F, b), O.neg(F, d)))) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, O.neg(F, b), O.neg(F, d)), O.mul(F, b, d), neg_mul_neg(~F, b, d)) : {O.add(F, O.add(F, O.mul(F, a, c), O.neg(F, O.mul(F, a, d))), O.add(F, O.neg(F, O.mul(F, b, c)), _)) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.neg(F, O.add(F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}
  %neg_add(~F, O.mul(F, a, d), O.mul(F, b, c)) : {O.add(F, O.add(F, O.mul(F, a, c), O.neg(F, O.mul(F, a, d))), O.add(F, O.neg(F, O.mul(F, b, c)), O.mul(F, b, d))) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), _) : O.C(F)}
  %add_comm(~F, O.mul(F, b, d), O.neg(F, O.mul(F, b, c))) : {O.add(F, O.add(F, O.mul(F, a, c), O.neg(F, O.mul(F, a, d))), _) == O.add(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.add(F, O.neg(F, O.mul(F, a, d)), O.neg(F, O.mul(F, b, c)))) : O.C(F)}
  add_shuffle(~F, O.mul(F, a, c), O.neg(F, O.mul(F, a, d)), O.mul(F, b, d), O.neg(F, O.mul(F, b, c)))
