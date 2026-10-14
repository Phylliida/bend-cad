# bend-cad spec: ordered fields, the numbers every meaning is stated over
# (DESIGN §5.5). Trusted: the textbook axioms of an ordered field. A
# sketch's exact solution is real, and the reals are an ordered field, so a
# meaning proven for every ordered field holds at the exact solution.
#
# Laws take the field as a template parameter (`for ~F: OField`): Bend
# checks them with its operations opaque, and a template's axioms may be
# used any number of times (an ordinary function-valued argument could be
# used only once). Equality is Bend's own {==}; order facts are Data, so a
# proof of a < b can be reused.

import Base
import ./num.bend as S
import ./ring.bend as E

type OField is Type:
  OField{C: Data,
    zero: C,
    one: C,
    add: C -> C -> C,
    mul: C -> C -> C,
    neg: C -> C,
    inv: C -> C,
    lt: C -> C -> Data,
    add_assoc: @a: C -> @b: C -> @c: C -> {add(add(a, b), c) == add(a, add(b, c)) : C},
    add_comm: @a: C -> @b: C -> {add(a, b) == add(b, a) : C},
    add_zero: @a: C -> {add(a, zero) == a : C},
    add_neg: @a: C -> {add(a, neg(a)) == zero : C},
    mul_assoc: @a: C -> @b: C -> @c: C -> {mul(mul(a, b), c) == mul(a, mul(b, c)) : C},
    mul_comm: @a: C -> @b: C -> {mul(a, b) == mul(b, a) : C},
    mul_one: @a: C -> {mul(a, one) == a : C},
    mul_add: @a: C -> @b: C -> @c: C -> {mul(a, add(b, c)) == add(mul(a, b), mul(a, c)) : C},
    mul_inv: @a: C -> ({a == zero : C} -> Empty) -> {mul(a, inv(a)) == one : C},
    lt_irrefl: @a: C -> lt(a, a) -> Empty,
    lt_trans: @a: C -> @b: C -> @c: C -> lt(a, b) -> lt(b, c) -> lt(a, c),
    lt_total: @a: C -> @b: C -> Or(lt(a, b), Or({a == b : C}, lt(b, a))),
    lt_add: @a: C -> @b: C -> @c: C -> lt(a, b) -> lt(add(a, c), add(b, c)),
    lt_mul: @a: C -> @b: C -> lt(zero, a) -> lt(zero, b) -> lt(zero, mul(a, b)),
    zero_lt_one: lt(zero, one)}

# Accessors
# ---------

def C(F: OField) -> Data:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      C

# the additive identity
def zero(F: OField) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      zero

# the multiplicative identity
def one(F: OField) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      one

def add(F: OField) -> C(F) -> C(F) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      add

def mul(F: OField) -> C(F) -> C(F) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul

def neg(F: OField) -> C(F) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      neg

# 1/a for a ≠ 0 (its value at 0 is unspecified)
def inv(F: OField) -> C(F) -> C(F):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      inv

# a < b
def lt(F: OField) -> C(F) -> C(F) -> Data:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt

def add_assoc(F: OField) -> @a: C(F) -> @b: C(F) -> @c: C(F) -> {add(F, add(F, a, b), c) == add(F, a, add(F, b, c)) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      add_assoc

def add_comm(F: OField) -> @a: C(F) -> @b: C(F) -> {add(F, a, b) == add(F, b, a) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      add_comm

def add_zero(F: OField) -> @a: C(F) -> {add(F, a, zero(F)) == a : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      add_zero

def add_neg(F: OField) -> @a: C(F) -> {add(F, a, neg(F, a)) == zero(F) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      add_neg

def mul_assoc(F: OField) -> @a: C(F) -> @b: C(F) -> @c: C(F) -> {mul(F, mul(F, a, b), c) == mul(F, a, mul(F, b, c)) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul_assoc

def mul_comm(F: OField) -> @a: C(F) -> @b: C(F) -> {mul(F, a, b) == mul(F, b, a) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul_comm

def mul_one(F: OField) -> @a: C(F) -> {mul(F, a, one(F)) == a : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul_one

def mul_add(F: OField) -> @a: C(F) -> @b: C(F) -> @c: C(F) -> {mul(F, a, add(F, b, c)) == add(F, mul(F, a, b), mul(F, a, c)) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul_add

def mul_inv(F: OField) -> @a: C(F) -> ({a == zero(F) : C(F)} -> Empty) -> {mul(F, a, inv(F, a)) == one(F) : C(F)}:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      mul_inv

def lt_irrefl(F: OField) -> @a: C(F) -> lt(F, a, a) -> Empty:
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt_irrefl

def lt_trans(F: OField) -> @a: C(F) -> @b: C(F) -> @c: C(F) -> lt(F, a, b) -> lt(F, b, c) -> lt(F, a, c):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt_trans

def lt_total(F: OField) -> @a: C(F) -> @b: C(F) -> Or(lt(F, a, b), Or({a == b : C(F)}, lt(F, b, a))):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt_total

def lt_add(F: OField) -> @a: C(F) -> @b: C(F) -> @c: C(F) -> lt(F, a, b) -> lt(F, add(F, a, c), add(F, b, c)):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt_add

def lt_mul(F: OField) -> @a: C(F) -> @b: C(F) -> lt(F, zero(F), a) -> lt(F, zero(F), b) -> lt(F, zero(F), mul(F, a, b)):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      lt_mul

def zero_lt_one(F: OField) -> lt(F, zero(F), one(F)):
  match F:
    case OField{C, zero, one, add, mul, neg, inv, lt, add_assoc, add_comm, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add, mul_inv, lt_irrefl, lt_trans, lt_total, lt_add, lt_mul, zero_lt_one}:
      zero_lt_one

# Derived operations
# ------------------

def sub(~F: OField, a: C(F), b: C(F)) -> C(F):
  add(F, a, neg(F, b))

# a ≠ b
def ne(~F: OField, +a: C(F), +b: C(F)) -> Type:
  {a == b : C(F)} -> Empty

# a ≤ b
def le(~F: OField, +a: C(F), +b: C(F)) -> Data:
  Either<&2, &2, lt(F, a, b), {a == b : C(F)}>

def two(~F: OField) -> C(F):
  add(F, one(F), one(F))

def half(~F: OField) -> C(F):
  inv(F, two(~F))

# The rationals inside F: a binary positive, an integer, n/d
def ofp(~F: OField, p: S.Pos) -> C(F):
  match p:
    case S.XH{}:
      one(F)
    case S.XO{+q}:
      add(F, ofp(~F, q), ofp(~F, q))
    case S.XI{+q}:
      add(F, add(F, ofp(~F, q), ofp(~F, q)), one(F))

def ofz(~F: OField, z: S.Z) -> C(F):
  match z:
    case S.Z0{}:
      zero(F)
    case S.Zpos{p}:
      ofp(~F, p)
    case S.Zneg{p}:
      neg(F, ofp(~F, p))

def ofq(~F: OField, +q: S.Q) -> C(F):
  mul(F, ofz(~F, S.Q.num(q)), inv(F, ofp(~F, S.Q.den(q))))

# Rational expressions evaluated in F (unused variables read as 0)
def lookup(~F: OField, env: List<&2, C(F)>, i: Nat) -> C(F):
  match env i:
    case Nil{} j:
      zero(F)
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      lookup(~F, t, j)

def eval(~F: OField, +env: List<&2, C(F)>, e: E.QExpr) -> C(F):
  match e:
    case E.QVar{i}:
      lookup(~F, env, i)
    case E.QCst{c}:
      ofq(~F, c)
    case E.QAdd{a, b}:
      add(F, eval(~F, env, a), eval(~F, env, b))
    case E.QSub{a, b}:
      sub(~F, eval(~F, env, a), eval(~F, env, b))
    case E.QMul{a, b}:
      mul(F, eval(~F, env, a), eval(~F, env, b))
    case E.QNeg{a}:
      neg(F, eval(~F, env, a))
