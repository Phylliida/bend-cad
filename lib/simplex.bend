# bend-cad: exact simplex with Bland's rule (PLAN-sk13a S3), deciding a
# system of linear inequalities over the integers:
#   a_k . y + b_k > 0 (strict) or >= 0,   k < m,   y in Q^n free.
# The general simplex of Dutertre and de Moura. Variables are the m slacks
# s_k = a_k . y (indices 0 .. m-1), each bounded below by
# l_k = -b_k (+ delta if strict), and the n free y's (indices m .. N-1).
# Values are a + b delta, delta a symbolic positive infinitesimal, compared
# lexicographically.
#
# The dictionary is integer, a denominator per row: every variable x has a
# row (D_x > 0, M_x) with D_x x = M_x . (the nonbasic variables); a
# nonbasic x's row is (1, e_x), and every row is 0 at the basic columns.
# The assignment puts each nonbasic bounded variable at its bound and each
# nonbasic free one at 0, so x's value is (M_x . v) / D_x, v the bound
# vector (v_k = l_k for a slack, 0 for a y), and no assignment is stored.
#
# Bland's rule: the leaving variable is the smallest slack below its bound
# (a nonbasic slack is at its bound, so it is basic); the entering one is
# the smallest variable that can raise it: a positive entry of its row, or
# a nonzero entry of a free variable. None leaves: feasible. None enters:
# that row is a Motzkin certificate. Pivoting on p = M_ie sends row i to
# (1, e_i), leaves a row with M_xe = 0 alone, and sends any other row to
# (|p| D_x, |p| M_x - sgn(p) M_xe M_i + sgn(p) M_xe D_i e_i). Read in a
# field, every row R = M / D goes to R - (R_e / R_ie) (R_i - e_i).
#
# The run doubles: run(k) takes 2^k steps by recursion on k, so no large
# fuel number is ever built. With N variables, run(N) finishes (the bases
# visited are distinct by Bland's rule, and there are 2^N of them).
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/simppf.bend and after), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ./elim.bend as EL

# Comparisons
# -----------

def islt(o: Cmp) -> Bool:
  match o:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def lexlt.go(o: Cmp, +b1: S.Z, +b2: S.Z) -> Bool:
  match o:
    case LT{}:
      True{}
    case EQ{}:
      islt(S.Z.cmp(b1, b2))
    case GT{}:
      False{}

# a1 + b1 delta < a2 + b2 delta
def lexlt(+a1: S.Z, +b1: S.Z, +a2: S.Z, +b2: S.Z) -> Bool:
  lexlt.go(S.Z.cmp(a1, a2), b1, b2)

def ind(b: Bool) -> S.Z:
  match b:
    case True{}:
      S.Zpos{S.XH{}}
    case False{}:
      S.Z0{}

def ltn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      False{}
    case 0n 1n+j:
      True{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      ltn(i, j)

def eqn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+j:
      False{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      eqn(i, j)

# Vectors
# -------

def dot(u: List<&2, S.Z>, w: List<&2, S.Z>) -> S.Z:
  match u w:
    case Nil{} Nil{}:
      S.Z0{}
    case Nil{} Con{y, s}:
      S.Z0{}
    case Con{x, t} Nil{}:
      S.Z0{}
    case Con{x, t} Con{y, s}:
      S.Z.add(S.Z.mul(x, y), dot(t, s))

def at(u: List<&2, S.Z>, j: Nat) -> S.Z:
  match u j:
    case Nil{} j:
      S.Z0{}
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+i:
      at(t, i)

def cat(u: List<&2, S.Z>, w: List<&2, S.Z>) -> List<&2, S.Z>:
  match u:
    case Nil{}:
      w
    case Con{x, t}:
      Con{x, cat(t, w)}

# e_i, of length k
def unit(k: Nat, i: Nat) -> List<&2, S.Z>:
  match k i:
    case 0n i:
      Nil{}
    case 1n+j 0n:
      Con{S.Zpos{S.XH{}}, EL.zeros(j)}
    case 1n+j 1n+h:
      Con{S.Z0{}, unit(j, h)}

def vlen(u: List<&2, S.Z>) -> Nat:
  match u:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+vlen(t)

# The problem
# -----------

# a . y + b > 0 (s) or >= 0
type Ineq is Data:
  Ineq{a: List<&2, S.Z>, b: S.Z, s: Bool}

# the inequalities, the number of y's
type LP is Data:
  LP{qs: List<&2, Ineq>, n: Nat}

def LP.qs(lp: LP) -> List<&2, Ineq>:
  match lp:
    case LP{qs, n}:
      qs

def LP.n(lp: LP) -> Nat:
  match lp:
    case LP{qs, n}:
      n

def qlen(qs: List<&2, Ineq>) -> Nat:
  match qs:
    case Nil{}:
      0n
    case Con{q, t}:
      1n+qlen(t)

def LP.m(lp: LP) -> Nat:
  qlen(LP.qs(lp))

# all variables
def LP.nv(+lp: LP) -> Nat:
  Nat.add(LP.m(lp), LP.n(lp))

# the bound vector's real and delta parts: -b_k and [strict] at slack k, 0
# at the y's
def bnd0(qs: List<&2, Ineq>, n: Nat) -> List<&2, S.Z>:
  match qs:
    case Nil{}:
      EL.zeros(n)
    case Con{Ineq{a, b, s}, t}:
      Con{S.Z.neg(b), bnd0(t, n)}

def bnd1(qs: List<&2, Ineq>, n: Nat) -> List<&2, S.Z>:
  match qs:
    case Nil{}:
      EL.zeros(n)
    case Con{Ineq{a, b, s}, t}:
      Con{ind(s), bnd1(t, n)}

def LP.v0(lp: LP) -> List<&2, S.Z>:
  match lp:
    case LP{qs, n}:
      bnd0(qs, n)

def LP.v1(lp: LP) -> List<&2, S.Z>:
  match lp:
    case LP{qs, n}:
      bnd1(qs, n)

# The dictionary
# --------------

# a row: D x = M . (the variables), D > 0
type Rw is Data:
  Rw{d: S.Pos, m: List<&2, S.Z>}

def Rw.d(r: Rw) -> S.Pos:
  match r:
    case Rw{d, m}:
      d

def Rw.m(r: Rw) -> List<&2, S.Z>:
  match r:
    case Rw{d, m}:
      m

# every variable's row, and which are basic
type Tab is Data:
  Tab{rows: List<&2, Rw>, bas: List<&2, Bool>}

def Tab.rows(t: Tab) -> List<&2, Rw>:
  match t:
    case Tab{rows, bas}:
      rows

def Tab.bas(t: Tab) -> List<&2, Bool>:
  match t:
    case Tab{rows, bas}:
      bas

def rowat(rs: List<&2, Rw>, i: Nat) -> Rw:
  match rs i:
    case Nil{} i:
      Rw{S.XH{}, Nil{}}
    case Con{r, t} 0n:
      r
    case Con{r, t} 1n+j:
      rowat(t, j)

# the slacks' rows: s_k = a_k . y
def srows(qs: List<&2, Ineq>, +m: Nat) -> List<&2, Rw>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{Ineq{a, b, s}, t}:
      Con{Rw{S.XH{}, cat(EL.zeros(m), a)}, srows(t, m)}

# the y's rows: e_i, from index i, c of them
def yrows(c: Nat, +k: Nat, +i: Nat) -> List<&2, Rw>:
  match c:
    case 0n:
      Nil{}
    case 1n+j:
      Con{Rw{S.XH{}, unit(k, i)}, yrows(j, k, 1n+i)}

def trues(c: Nat, +b: Bool) -> List<&2, Bool>:
  match c:
    case 0n:
      Nil{}
    case 1n+j:
      Con{b, trues(j, b)}

def bcat(u: List<&2, Bool>, w: List<&2, Bool>) -> List<&2, Bool>:
  match u:
    case Nil{}:
      w
    case Con{x, t}:
      Con{x, bcat(t, w)}

def rcat(u: List<&2, Rw>, w: List<&2, Rw>) -> List<&2, Rw>:
  match u:
    case Nil{}:
      w
    case Con{x, t}:
      Con{x, rcat(t, w)}

# the slacks basic, the y's nonbasic at 0
def init(+lp: LP) -> Tab:
  Tab{rcat(srows(LP.qs(lp), LP.m(lp)), yrows(LP.n(lp), LP.nv(lp), LP.m(lp))), bcat(trues(LP.m(lp), True{}), trues(LP.n(lp), False{}))}

# Bland's choices
# ---------------

# slack q's row is below its bound: M . v < D l
def viol(r: Rw, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>, q: Ineq) -> Bool:
  match r q:
    case Rw{+d, +m} Ineq{a, b, s}:
      lexlt(dot(m, v0), dot(m, v1), S.Z.mul(S.Zpos{d}, S.Z.neg(b)), S.Z.mul(S.Zpos{d}, ind(s)))

def pick(b: Bool, k: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{k}
    case False{}:
      rest

# the smallest slack below its bound, from index k
def leave.go(qs: List<&2, Ineq>, rs: List<&2, Rw>, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>, +k: Nat) -> Maybe<&2, Nat>:
  match qs rs:
    case Nil{} rs:
      None{}
    case Con{q, qt} Nil{}:
      None{}
    case Con{q, qt} Con{r, rt}:
      pick(viol(r, v0, v1, q), k, leave.go(qt, rt, v0, v1, 1n+k))

def leave(+lp: LP, t: Tab) -> Maybe<&2, Nat>:
  leave.go(LP.qs(lp), Tab.rows(t), LP.v0(lp), LP.v1(lp), 0n)

# a variable with entry c in the leaving row can raise it
def helpful(c: S.Z, free: Bool) -> Bool:
  match c:
    case S.Z0{}:
      False{}
    case S.Zpos{p}:
      True{}
    case S.Zneg{p}:
      free

# the smallest variable that can raise the row, from index j (free: j >= m)
def enter.go(r: List<&2, S.Z>, +m: Nat, +j: Nat) -> Maybe<&2, Nat>:
  match r:
    case Nil{}:
      None{}
    case Con{c, t}:
      pick(helpful(c, Nat.is_le(m, j)), j, enter.go(t, m, 1n+j))

# Pivoting
# --------

def iszero(z: S.Z) -> Bool:
  match z:
    case S.Z0{}:
      True{}
    case S.Zpos{p}:
      False{}
    case S.Zneg{p}:
      False{}

# row x with c = M_xe != 0, against the pivot row (di, mi), p = M_ie:
# |p| D_x x = |p| M_x - sgn(p) c M_i + sgn(p) c D_i e_i
def phi.go(b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +i: Nat, +p: S.Z, +len: Nat, +c: S.Z, +r: Rw) -> Rw:
  match b:
    case True{}:
      r
    case False{}:
      Rw{S.Pos.mul(EL.babs(p), Rw.d(r)), EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, Rw.m(r)), EL.vscale(S.Z.neg(EL.bsgn(p, c)), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), unit(len, i)))}

# row x (index k) after the pivot: e_i for x = i, unchanged when M_xe = 0
def phi(b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +r: Rw) -> Rw:
  match b:
    case True{}:
      Rw{S.XH{}, unit(len, i)}
    case False{}:
      phi.go(iszero(at(Rw.m(r), e)), mi, di, i, p, len, at(Rw.m(r), e), r)

def phis(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, Rw>, +k: Nat) -> List<&2, Rw>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{phi(eqn(k, i), mi, di, e, i, p, len, r), phis(mi, di, e, i, p, len, t, 1n+k)}

def setb(bs: List<&2, Bool>, i: Nat, b: Bool) -> List<&2, Bool>:
  match bs i:
    case Nil{} i:
      Nil{}
    case Con{x, t} 0n:
      Con{b, t}
    case Con{x, t} 1n+j:
      Con{x, setb(t, j, b)}

def pivot.go(ri: Rw, +e: Nat, +i: Nat, +len: Nat, rows: List<&2, Rw>, bas: List<&2, Bool>) -> Tab:
  match ri:
    case Rw{+di, +mi}:
      Tab{phis(mi, di, e, i, at(mi, e), len, rows, 0n), setb(setb(bas, i, False{}), e, True{})}

# i leaves, e enters
def pivot(+len: Nat, t: Tab, +i: Nat, +e: Nat) -> Tab:
  match t:
    case Tab{+rows, bas}:
      pivot.go(rowat(rows, i), e, i, len, rows, bas)

# The run
# -------

type Run is Data:
  Go{t: Tab}
  Sat{t: Tab}
  Unsat{t: Tab, i: Nat}

def step.e(+lp: LP, +t: Tab, +i: Nat, me: Maybe<&2, Nat>) -> Run:
  match me:
    case None{}:
      Unsat{t, i}
    case Some{e}:
      Go{pivot(LP.nv(lp), t, i, e)}

def step.l(+lp: LP, +t: Tab, ml: Maybe<&2, Nat>) -> Run:
  match ml:
    case None{}:
      Sat{t}
    case Some{+i}:
      step.e(lp, t, i, enter.go(Rw.m(rowat(Tab.rows(t), i)), LP.m(lp), 0n))

def step(+lp: LP, +t: Tab) -> Run:
  step.l(lp, t, leave(lp, t))

def adv(+lp: LP, r: Run) -> Run:
  match r:
    case Go{+t}:
      step(lp, t)
    case Sat{t}:
      Sat{t}
    case Unsat{t, i}:
      Unsat{t, i}

# 2^k steps
def run(k: Nat, +lp: LP, r: Run) -> Run:
  match k:
    case 0n:
      adv(lp, r)
    case 1n++j:
      run(j, lp, run(j, lp, r))

def solve(+lp: LP) -> Run:
  run(LP.nv(lp), lp, Go{init(lp)})
