# Telescoping slopes in every ordered field: for an expression e and two
# assignments X1, X2, sl(i, X1, X2, e) is e's slope in variable i, built by
#   slope(a b) = a(X1) slope(b) + b(X2) slope(a),
# so that e(X1) - e(X2) is the sum over i of sl(i) (X1_i - X2_i)
# (slope_ok). Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./karith.bend as KA

# 1 if b, else 0
def find(~F: O.OField, b: Bool) -> O.C(F):
  match b:
    case True{}:
      O.one(F)
    case False{}:
      O.zero(F)

# e's slope in variable i between X1 and X2
def sl(~F: O.OField, +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{j}:
      find(~F, KA.nateq(i, j))
    case E.QCst{q}:
      O.zero(F)
    case E.QAdd{a, b}:
      O.add(F, sl(~F, i, x1, x2, a), sl(~F, i, x1, x2, b))
    case E.QSub{a, b}:
      O.sub(~F, sl(~F, i, x1, x2, a), sl(~F, i, x1, x2, b))
    case E.QMul{+a, +b}:
      O.add(F, O.mul(F, O.eval(~F, x1, a), sl(~F, i, x1, x2, b)), O.mul(F, O.eval(~F, x2, b), sl(~F, i, x1, x2, a)))
    case E.QNeg{a}:
      O.neg(F, sl(~F, i, x1, x2, a))

# the slopes in the cnt variables lo, lo + 1, ...
def srange(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +e: E.QExpr, cnt: Nat, +lo: Nat) -> M.Vec(~F):
  match cnt:
    case 0n:
      Nil{}
    case 1n+k:
      Con{sl(~F, lo, x1, x2, e), srange(~F, x1, x2, e, k, 1n+lo)}
