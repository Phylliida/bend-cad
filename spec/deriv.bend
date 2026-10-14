# bend-cad spec: derivatives of expressions and regular solutions (DESIGN
# §10.2, solve_complete). Trusted; DRAFT FOR REVIEW.
#
# deriv(e, v) is the symbolic partial derivative of e in variable v, by
# the usual rules (sums, differences, negation, the product rule). The
# Jacobian of a list of equations in a list of variables, evaluated at x
# in an ordered field, is the matrix of those derivatives' values. x is a
# regular point of a square system when that matrix has a two-sided
# inverse.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./field.bend as O
import ./mat.bend as M

def qc(+z: S.Z) -> E.QExpr:
  E.QCst{S.Q{z, S.XH{}}}

def eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+j:
      False{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      eq(i, j)

# d x_i / d x_v: 1 when i = v, else 0
def dvar(b: Bool) -> E.QExpr:
  match b:
    case True{}:
      qc(S.Zpos{S.XH{}})
    case False{}:
      qc(S.Z0{})

# d e / d x_v
def deriv(e: E.QExpr, +v: Nat) -> E.QExpr:
  match e:
    case E.QVar{i}:
      dvar(eq(i, v))
    case E.QCst{q}:
      qc(S.Z0{})
    case E.QAdd{a, b}:
      E.QAdd{deriv(a, v), deriv(b, v)}
    case E.QSub{a, b}:
      E.QSub{deriv(a, v), deriv(b, v)}
    case E.QMul{+a, +b}:
      E.QAdd{E.QMul{deriv(a, v), b}, E.QMul{a, deriv(b, v)}}
    case E.QNeg{a}:
      E.QNeg{deriv(a, v)}

# the row of d e / d x_u for u in us, at x
def jrow(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, us: List<&2, Nat>) -> M.Vec(~F):
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      Con{O.eval(~F, x, deriv(e, u)), jrow(~F, x, e, t)}

# the Jacobian of es in the variables us, at x (a row per equation)
def jac(~F: O.OField, +x: M.Vec(~F), es: List<&2, E.QExpr>, +us: List<&2, Nat>) -> M.Mat(~F):
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{jrow(~F, x, e, us), jac(~F, x, t, us)}

def nlen(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+nlen(t)

def elen(es: List<&2, E.QExpr>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, t}:
      1n+elen(t)

# entry (i, j) of A (0 past the ends: matrices are rows read with
# trailing zeros, spec/mat.bend)
def mrow(~F: O.OField, a: M.Mat(~F), i: Nat) -> M.Vec(~F):
  match a i:
    case Nil{} i:
      Nil{}
    case Con{r, t} 0n:
      r
    case Con{r, t} 1n+k:
      mrow(~F, t, k)

def ment(~F: O.OField, +a: M.Mat(~F), +i: Nat, +j: Nat) -> O.C(F):
  O.lookup(~F, mrow(~F, a, i), j)

# A and B agree at (i, j) for the n columns j from j0
def MEq.row(~F: O.OField, +a: M.Mat(~F), +b: M.Mat(~F), +i: Nat, n: Nat, +j: Nat) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+m:
      M.Both({ment(~F, a, i, j) == ment(~F, b, i, j) : O.C(F)}, MEq.row(~F, a, b, i, m, 1n+j))

# A and B agree at every entry (i, j) with i, j < n (rows from i)
def MEq(~F: O.OField, +a: M.Mat(~F), +b: M.Mat(~F), rows: Nat, +i: Nat, +n: Nat) -> Data:
  match rows:
    case 0n:
      Unit
    case 1n+m:
      M.Both(MEq.row(~F, a, b, i, n, 0n), MEq(~F, a, b, m, 1n+i, n))

# Y is a two-sided inverse of A (n by n): A Y = I and Y A = I entry by
# entry. (Not as list equalities: M.ident stores its rows without trailing
# zeros, so a full-length product row never equals it as a list.)
def Inverse(~F: O.OField, +a: M.Mat(~F), +y: M.Mat(~F), +n: Nat) -> Data:
  M.Both(MEq(~F, M.matmul(~F, a, y), M.ident(~F, n), n, 0n, n), MEq(~F, M.matmul(~F, y, a), M.ident(~F, n), n, 0n, n))

# x is a regular point of es in the variables us: as many variables as
# equations, and the Jacobian there has an inverse
def Regular(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +us: List<&2, Nat>) -> Data:
  M.Both({nlen(us) == elen(es) : Nat}, Sigma<&2, &2, M.Mat(~F), y => Inverse(~F, jac(~F, x, es, us), y, nlen(us))>)
