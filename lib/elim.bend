# bend-cad: degree-0 elimination (PLAN-sk13a S2). Equations are integer
# polynomials in normal form (their cleared forms, R.norm(QN.clr(e)));
# monomials are the coordinates. The solved equations so far form rows in
# echelon form, oldest first, one per equation of the basis they came from:
# row j has a pivot monomial pv where its coefficient is nonzero, and
# every later row is 0 at pv. Row j also records how it was made: its
# polynomial is bt times its own equation's plus cb (one integer per
# earlier basis equation) times theirs, with bt positive.
#
# An equation is reduced against the rows in order, fraction-free:
# r := |b| r - sgn(b) a R, where a and b are r's and R's coefficients at
# R's pivot. The residual is 0 at every pivot. If it is 0 the equation is
# a combination of the basis (dropped, with that combination); otherwise
# it becomes a new row, its pivot its largest monomial (1 only when the
# residual is a nonzero constant: a refutation candidate).
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/elimpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ./natring.bend as NR
import ./zring.bend as R
import ./qnorm.bend as QN

# Coefficients
# ------------

def iseq(o: Cmp) -> Bool:
  match o:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

# c if b, else 0
def ifz(b: Bool, c: S.Z) -> S.Z:
  match b:
    case True{}:
      c
    case False{}:
      S.Z0{}

# the coefficient of m in p: the sum over the terms with monomial m
def cz(+m: List<&2, Nat>, p: List<&2, R.ZTerm>) -> S.Z:
  match p:
    case Nil{}:
      S.Z0{}
    case Con{R.ZTerm{c, n}, rest}:
      S.Z.add(ifz(iseq(NR.mcmp(m, n)), c), cz(m, rest))

def pivot.go(p: List<&2, R.ZTerm>, m: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      m
    case Con{R.ZTerm{c, n}, rest}:
      pivot.go(rest, n)

# the largest monomial of p (the last term's)
def pivot(p: List<&2, R.ZTerm>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{R.ZTerm{c, m}, rest}:
      pivot.go(rest, m)

# Combinations (one integer per basis equation, missing entries 0)
# ---------------------------------------------------------------

def vscale(+k: S.Z, u: List<&2, S.Z>) -> List<&2, S.Z>:
  match u:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{S.Z.mul(k, x), vscale(k, t)}

def vadd(u: List<&2, S.Z>, w: List<&2, S.Z>) -> List<&2, S.Z>:
  match u w:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{y, s}:
      Con{y, s}
    case Con{x, t} Nil{}:
      Con{x, t}
    case Con{x, t} Con{y, s}:
      Con{S.Z.add(x, y), vadd(t, s)}

def vsnoc(u: List<&2, S.Z>, x: S.Z) -> List<&2, S.Z>:
  match u:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, vsnoc(t, x)}

def zeros(n: Nat) -> List<&2, S.Z>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{S.Z0{}, zeros(k)}

# Rows and residuals
# ------------------

# a row: polynomial p = bt (its equation) + cb . (earlier ones), pivot pv
type Row is Data:
  Row{p: List<&2, R.ZTerm>, cb: List<&2, S.Z>, bt: S.Pos, pv: List<&2, Nat>}

# a residual of the equation being reduced: p = bt (it) + cb . (basis)
type Res is Data:
  Res{p: List<&2, R.ZTerm>, cb: List<&2, S.Z>, bt: S.Pos}

def babs(b: S.Z) -> S.Pos:
  match b:
    case S.Z0{}:
      S.XH{}
    case S.Zpos{q}:
      q
    case S.Zneg{q}:
      q

# sgn(b) a
def bsgn(b: S.Z, a: S.Z) -> S.Z:
  match b:
    case S.Z0{}:
      a
    case S.Zpos{q}:
      a
    case S.Zneg{q}:
      S.Z.neg(a)

# |b| r - sgn(b) a R, a and b the coefficients of r and R at R's pivot
def step.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos) -> Res:
  match a:
    case S.Z0{}:
      Res{rp, rcb, rbt}
    case S.Zpos{+q}:
      Res{R.padd(R.pscale(S.Zpos{babs(b)}, Nil{}, rp), R.pneg(R.pscale(bsgn(b, S.Zpos{q}), Nil{}, p))),
        vadd(vscale(S.Zpos{babs(b)}, rcb), vscale(S.Z.neg(bsgn(b, S.Zpos{q})), vsnoc(cb, S.Zpos{bt}))), S.Pos.mul(babs(b), rbt)}
    case S.Zneg{+q}:
      Res{R.padd(R.pscale(S.Zpos{babs(b)}, Nil{}, rp), R.pneg(R.pscale(bsgn(b, S.Zneg{q}), Nil{}, p))),
        vadd(vscale(S.Zpos{babs(b)}, rcb), vscale(S.Z.neg(bsgn(b, S.Zneg{q})), vsnoc(cb, S.Zpos{bt}))), S.Pos.mul(babs(b), rbt)}

def step(row: Row, r: Res) -> Res:
  match row r:
    case Row{+p, cb, bt, +pv} Res{+rp, rcb, rbt}:
      step.go(cz(pv, rp), cz(pv, p), rp, rcb, rbt, p, cb, bt)

# r reduced against the rows, oldest first
def reduce(rows: List<&2, Row>, r: Res) -> Res:
  match rows:
    case Nil{}:
      r
    case Con{row, t}:
      reduce(t, step(row, r))

# the residual of e, the basis having k equations
def start(e: E.QExpr, k: Nat) -> Res:
  Res{R.norm(QN.clr(e)), zeros(k), S.XH{}}

def rlen(rows: List<&2, Row>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+rlen(t)

# e's residual against the rows
def resid(+rows: List<&2, Row>, e: E.QExpr) -> Res:
  reduce(rows, start(e, rlen(rows)))

# the residual as a new row
def row_of(r: Res) -> Row:
  match r:
    case Res{+p, cb, bt}:
      Row{p, cb, bt, pivot(p)}

def rsnoc(rows: List<&2, Row>, x: Row) -> List<&2, Row>:
  match rows:
    case Nil{}:
      Con{x, Nil{}}
    case Con{h, t}:
      Con{h, rsnoc(t, x)}
