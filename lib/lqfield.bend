# The canonical rationals again (lib/qfield.bend), with each operation
# matching its first argument before it computes. The values are QF's, and
# so are the laws, but an operation on a term that is not yet a value (a
# symbolic sum in a proof) is stuck at once instead of running the
# rational arithmetic down to the stuck variable. A proof that holds in
# every ordered field and is only needed at some concrete one (Bland's
# rule) checks at this field far faster than at qfield.

import Base
import ../spec/field.bend as O
import ./qfield.bend as QF

def add(+a: QF.QC, +b: QF.QC) -> QF.QC:
  match a:
    case QF.QZ{}:
      QF.add(QF.QZ{}, b)
    case QF.QP{+w}:
      QF.add(QF.QP{w}, b)
    case QF.QN{+w}:
      QF.add(QF.QN{w}, b)

def mul(+a: QF.QC, +b: QF.QC) -> QF.QC:
  match a:
    case QF.QZ{}:
      QF.mul(QF.QZ{}, b)
    case QF.QP{+w}:
      QF.mul(QF.QP{w}, b)
    case QF.QN{+w}:
      QF.mul(QF.QN{w}, b)

def neg(+a: QF.QC) -> QF.QC:
  match a:
    case QF.QZ{}:
      QF.neg(QF.QZ{})
    case QF.QP{+w}:
      QF.neg(QF.QP{w})
    case QF.QN{+w}:
      QF.neg(QF.QN{w})

def inv(+a: QF.QC) -> QF.QC:
  match a:
    case QF.QZ{}:
      QF.inv(QF.QZ{})
    case QF.QP{+w}:
      QF.inv(QF.QP{w})
    case QF.QN{+w}:
      QF.inv(QF.QN{w})

# The operations are QF's
# -----------------------

def add_eq(+a: QF.QC, +b: QF.QC) -> {add(a, b) == QF.add(a, b) : QF.QC}:
  match a:
    case QF.QZ{}:
      {==}
    case QF.QP{+w}:
      {==}
    case QF.QN{+w}:
      {==}

def mul_eq(+a: QF.QC, +b: QF.QC) -> {mul(a, b) == QF.mul(a, b) : QF.QC}:
  match a:
    case QF.QZ{}:
      {==}
    case QF.QP{+w}:
      {==}
    case QF.QN{+w}:
      {==}

def neg_eq(+a: QF.QC) -> {neg(a) == QF.neg(a) : QF.QC}:
  match a:
    case QF.QZ{}:
      {==}
    case QF.QP{+w}:
      {==}
    case QF.QN{+w}:
      {==}

def inv_eq(+a: QF.QC) -> {inv(a) == QF.inv(a) : QF.QC}:
  match a:
    case QF.QZ{}:
      {==}
    case QF.QP{+w}:
      {==}
    case QF.QN{+w}:
      {==}

# The laws, from QF's
# -------------------

def add_assoc(+a: QF.QC, +b: QF.QC, +c: QF.QC) -> {add(add(a, b), c) == add(a, add(b, c)) : QF.QC}:
  %Equal.sym(QF.QC, add(add(a, b), c), QF.add(add(a, b), c), add_eq(add(a, b), c)) : {_ == add(a, add(b, c)) : QF.QC}
  %Equal.sym(QF.QC, add(a, b), QF.add(a, b), add_eq(a, b)) : {QF.add(_, c) == add(a, add(b, c)) : QF.QC}
  %Equal.sym(QF.QC, add(a, add(b, c)), QF.add(a, add(b, c)), add_eq(a, add(b, c))) : {QF.add(QF.add(a, b), c) == _ : QF.QC}
  %Equal.sym(QF.QC, add(b, c), QF.add(b, c), add_eq(b, c)) : {QF.add(QF.add(a, b), c) == QF.add(a, _) : QF.QC}
  QF.add_assoc(a, b, c)

def add_comm(+a: QF.QC, +b: QF.QC) -> {add(a, b) == add(b, a) : QF.QC}:
  %Equal.sym(QF.QC, add(a, b), QF.add(a, b), add_eq(a, b)) : {_ == add(b, a) : QF.QC}
  %Equal.sym(QF.QC, add(b, a), QF.add(b, a), add_eq(b, a)) : {QF.add(a, b) == _ : QF.QC}
  QF.add_comm(a, b)

def add_zero(+a: QF.QC) -> {add(a, QF.zero()) == a : QF.QC}:
  %Equal.sym(QF.QC, add(a, QF.zero()), QF.add(a, QF.zero()), add_eq(a, QF.zero())) : {_ == a : QF.QC}
  QF.add_zero(a)

def add_neg(+a: QF.QC) -> {add(a, neg(a)) == QF.zero() : QF.QC}:
  %Equal.sym(QF.QC, add(a, neg(a)), QF.add(a, neg(a)), add_eq(a, neg(a))) : {_ == QF.zero() : QF.QC}
  %Equal.sym(QF.QC, neg(a), QF.neg(a), neg_eq(a)) : {QF.add(a, _) == QF.zero() : QF.QC}
  QF.add_neg(a)

def mul_assoc(+a: QF.QC, +b: QF.QC, +c: QF.QC) -> {mul(mul(a, b), c) == mul(a, mul(b, c)) : QF.QC}:
  %Equal.sym(QF.QC, mul(mul(a, b), c), QF.mul(mul(a, b), c), mul_eq(mul(a, b), c)) : {_ == mul(a, mul(b, c)) : QF.QC}
  %Equal.sym(QF.QC, mul(a, b), QF.mul(a, b), mul_eq(a, b)) : {QF.mul(_, c) == mul(a, mul(b, c)) : QF.QC}
  %Equal.sym(QF.QC, mul(a, mul(b, c)), QF.mul(a, mul(b, c)), mul_eq(a, mul(b, c))) : {QF.mul(QF.mul(a, b), c) == _ : QF.QC}
  %Equal.sym(QF.QC, mul(b, c), QF.mul(b, c), mul_eq(b, c)) : {QF.mul(QF.mul(a, b), c) == QF.mul(a, _) : QF.QC}
  QF.mul_assoc(a, b, c)

def mul_comm(+a: QF.QC, +b: QF.QC) -> {mul(a, b) == mul(b, a) : QF.QC}:
  %Equal.sym(QF.QC, mul(a, b), QF.mul(a, b), mul_eq(a, b)) : {_ == mul(b, a) : QF.QC}
  %Equal.sym(QF.QC, mul(b, a), QF.mul(b, a), mul_eq(b, a)) : {QF.mul(a, b) == _ : QF.QC}
  QF.mul_comm(a, b)

def mul_one(+a: QF.QC) -> {mul(a, QF.one()) == a : QF.QC}:
  %Equal.sym(QF.QC, mul(a, QF.one()), QF.mul(a, QF.one()), mul_eq(a, QF.one())) : {_ == a : QF.QC}
  QF.mul_one(a)

def mul_add(+a: QF.QC, +b: QF.QC, +c: QF.QC) -> {mul(a, add(b, c)) == add(mul(a, b), mul(a, c)) : QF.QC}:
  %Equal.sym(QF.QC, mul(a, add(b, c)), QF.mul(a, add(b, c)), mul_eq(a, add(b, c))) : {_ == add(mul(a, b), mul(a, c)) : QF.QC}
  %Equal.sym(QF.QC, add(b, c), QF.add(b, c), add_eq(b, c)) : {QF.mul(a, _) == add(mul(a, b), mul(a, c)) : QF.QC}
  %Equal.sym(QF.QC, add(mul(a, b), mul(a, c)), QF.add(mul(a, b), mul(a, c)), add_eq(mul(a, b), mul(a, c))) : {QF.mul(a, QF.add(b, c)) == _ : QF.QC}
  %Equal.sym(QF.QC, mul(a, b), QF.mul(a, b), mul_eq(a, b)) : {QF.mul(a, QF.add(b, c)) == QF.add(_, mul(a, c)) : QF.QC}
  %Equal.sym(QF.QC, mul(a, c), QF.mul(a, c), mul_eq(a, c)) : {QF.mul(a, QF.add(b, c)) == QF.add(QF.mul(a, b), _) : QF.QC}
  QF.mul_add(a, b, c)

def mul_inv(+a: QF.QC, h: {a == QF.zero() : QF.QC} -> Empty) -> {mul(a, inv(a)) == QF.one() : QF.QC}:
  %Equal.sym(QF.QC, mul(a, inv(a)), QF.mul(a, inv(a)), mul_eq(a, inv(a))) : {_ == QF.one() : QF.QC}
  %Equal.sym(QF.QC, inv(a), QF.inv(a), inv_eq(a)) : {QF.mul(a, _) == QF.one() : QF.QC}
  QF.mul_inv(a, h)

def lt_add(+a: QF.QC, +b: QF.QC, +c: QF.QC, h: QF.lt(a, b)) -> QF.lt(add(a, c), add(b, c)):
  %Equal.sym(QF.QC, add(a, c), QF.add(a, c), add_eq(a, c)) : QF.lt(_, add(b, c))
  %Equal.sym(QF.QC, add(b, c), QF.add(b, c), add_eq(b, c)) : QF.lt(QF.add(a, c), _)
  QF.lt_add(a, b, c, h)

def lt_mul(+a: QF.QC, +b: QF.QC, ha: QF.lt(QF.zero(), a), hb: QF.lt(QF.zero(), b)) -> QF.lt(QF.zero(), mul(a, b)):
  %Equal.sym(QF.QC, mul(a, b), QF.mul(a, b), mul_eq(a, b)) : QF.lt(QF.zero(), _)
  QF.lt_mul(a, b, ha, hb)

# The ordered field
# -----------------

def lqfield() -> O.OField:
  O.OField{QF.QC, QF.zero(), QF.one(), a => b => add(a, b), a => b => mul(a, b), a => neg(a), a => inv(a), a => b => QF.lt(a, b),
    a => b => c => add_assoc(a, b, c), a => b => add_comm(a, b), a => add_zero(a), a => add_neg(a),
    a => b => c => mul_assoc(a, b, c), a => b => mul_comm(a, b), a => mul_one(a), a => b => c => mul_add(a, b, c),
    a => h => mul_inv(a, h), a => h => QF.lt_irrefl(a, h), a => b => c => h1 => h2 => QF.lt_trans(a, b, c, h1, h2),
    a => b => QF.lt_total(a, b), a => b => c => h => lt_add(a, b, c, h), a => b => ha => hb => lt_mul(a, b, ha, hb), QF.zero_lt_one()}
