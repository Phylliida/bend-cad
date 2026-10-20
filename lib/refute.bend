# bend-cad: deciding degree-0 refutations (PLAN-sk13a S3). Given equations
# es and side conditions ss, is there a Motzkin refutation
#   l_1 e_1 + ... + m_1 s_1 + ... = k   (as polynomials),
# every m >= 0, and k < 0, or k = 0 with a strict side's m > 0?
#
# Linearize: monomials are the unknowns (1 the constant). The equations go
# first, through S2's elimination (lib/elim.bend): each is dropped (a
# combination of the earlier ones) or becomes a row, and the rows are 0 at
# each other's pivots.
# - A row that is a nonzero constant refutes the equations alone.
# - Otherwise each side is reduced against the rows. What is left of it,
#   p_k = bt_k NE(s_k) + cb_k . NE(basis), is 0 at every pivot, and reads
#   a_k . y + b_k over the monomials y that are left. The simplex
#   (lib/simplex.bend) decides those inequalities. Infeasible: its
#   certificate mu >= 0 has sum mu_k p_k = K, a constant, which gives the
#   refutation (m_k = mu_k bt_k den(s_k), and the basis's multipliers from
#   the combinations). Feasible: a linearized point, at which every
#   equation is 0 and every side holds, so no refutation exists (proven
#   later in S3).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ./natring.bend as NR
import ./zring.bend as R
import ./qnorm.bend as QN
import ./elim.bend as EL
import ./simplex.bend as SX

def bnot(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

def isnilp(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def Res.p(r: EL.Res) -> List<&2, R.ZTerm>:
  match r:
    case EL.Res{p, cb, bt}:
      p

def Res.cb(r: EL.Res) -> List<&2, S.Z>:
  match r:
    case EL.Res{p, cb, bt}:
      cb

def Res.bt(r: EL.Res) -> S.Pos:
  match r:
    case EL.Res{p, cb, bt}:
      bt

# The equations' rows
# -------------------

# the rows, and which equations became rows (the others were dropped)
type Walk is Data:
  Walk{rows: List<&2, EL.Row>, keep: List<&2, Bool>}

def Walk.rows(w: Walk) -> List<&2, EL.Row>:
  match w:
    case Walk{rows, keep}:
      rows

def Walk.keep(w: Walk) -> List<&2, Bool>:
  match w:
    case Walk{rows, keep}:
      keep

def walk.next(b: Bool, +rows: List<&2, EL.Row>, r: EL.Res) -> List<&2, EL.Row>:
  match b:
    case True{}:
      rows
    case False{}:
      EL.rsnoc(rows, EL.row_of(r))

def walk.k(b: Bool, w: Walk) -> Walk:
  match w:
    case Walk{rows, keep}:
      Walk{rows, Con{bnot(b), keep}}

def walk(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>) -> Walk:
  match es:
    case Nil{}:
      Walk{rows, Nil{}}
    case Con{e, t}:
      +r = EL.resid(rows, e)
      walk.k(isnilp(Res.p(r)), walk(t, walk.next(isnilp(Res.p(r)), rows, r)))

def Row.p(r: EL.Row) -> List<&2, R.ZTerm>:
  match r:
    case EL.Row{p, cb, bt, pv}:
      p

def Row.cb(r: EL.Row) -> List<&2, S.Z>:
  match r:
    case EL.Row{p, cb, bt, pv}:
      cb

def Row.bt(r: EL.Row) -> S.Pos:
  match r:
    case EL.Row{p, cb, bt, pv}:
      bt

def Row.pv(r: EL.Row) -> List<&2, Nat>:
  match r:
    case EL.Row{p, cb, bt, pv}:
      pv

def iscst(m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# the first row that is a nonzero constant (pivot 1), from index j
def crow(rows: List<&2, EL.Row>, +j: Nat) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      None{}
    case Con{r, t}:
      SX.pick(iscst(Row.pv(r)), j, crow(t, 1n+j))

def rowat(rows: List<&2, EL.Row>, j: Nat) -> EL.Row:
  match rows j:
    case Nil{} j:
      EL.Row{Nil{}, Nil{}, S.XH{}, Nil{}}
    case Con{r, t} 0n:
      r
    case Con{r, t} 1n+i:
      rowat(t, i)

# The sides
# ---------

def sexpr(s: SK.Side) -> E.QExpr:
  match s:
    case SK.Gt0{e}:
      e
    case SK.Ge0{e}:
      e

def strict(s: SK.Side) -> Bool:
  match s:
    case SK.Gt0{e}:
      True{}
    case SK.Ge0{e}:
      False{}

# each side reduced against the rows
def sres(+rows: List<&2, EL.Row>, ss: List<&2, SK.Side>) -> List<&2, EL.Res>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{EL.resid(rows, sexpr(s)), sres(rows, t)}

# the monomials left, sorted, each once
def ins.dec(o: Cmp, +m: List<&2, Nat>, +h: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, r: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match o:
    case LT{}:
      Con{m, Con{h, t}}
    case EQ{}:
      Con{h, t}
    case GT{}:
      Con{h, r}

def ins(+m: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match ys:
    case Nil{}:
      Con{m, Nil{}}
    case Con{+h, +t}:
      ins.dec(NR.mcmp(m, h), m, h, t, ins(m, t))

def insnc(m: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match m:
    case Nil{}:
      ys
    case Con{h, t}:
      ins(Con{h, t}, ys)

def tmons(p: List<&2, R.ZTerm>, ys: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match p:
    case Nil{}:
      ys
    case Con{R.ZTerm{c, m}, t}:
      tmons(t, insnc(m, ys))

def ymons(rs: List<&2, EL.Res>, ys: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      ys
    case Con{r, t}:
      ymons(t, tmons(Res.p(r), ys))

def mlen(ys: List<&2, List<&2, Nat>>) -> Nat:
  match ys:
    case Nil{}:
      0n
    case Con{y, t}:
      1n+mlen(t)

# The linear problem
# ------------------

def coefs(ys: List<&2, List<&2, Nat>>, +p: List<&2, R.ZTerm>) -> List<&2, S.Z>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      Con{EL.cz(y, p), coefs(t, p)}

def ineqs(+ys: List<&2, List<&2, Nat>>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>) -> List<&2, SX.Ineq>:
  match rs ss:
    case Nil{} ss:
      Nil{}
    case Con{r, rt} Nil{}:
      Nil{}
    case Con{+r, rt} Con{s, st}:
      Con{SX.Ineq{coefs(ys, Res.p(r)), EL.cz(Nil{}, Res.p(r)), strict(s)}, ineqs(ys, rt, st)}

def mklp(+ys: List<&2, List<&2, Nat>>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>) -> SX.LP:
  SX.LP{ineqs(ys, rs, ss), mlen(ys)}

# The decision
# ------------

type Dec is Data:
  # row j of the equations is a nonzero constant
  DRow{w: Walk, j: Nat}
  # the sides' residuals, the monomials left, the simplex's answer
  DLp{w: Walk, rs: List<&2, EL.Res>, ys: List<&2, List<&2, Nat>>, r: SX.Run}

def decide.lp(+w: Walk, +rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>, ss: List<&2, SK.Side>) -> Dec:
  DLp{w, rs, ys, SX.solve(mklp(ys, rs, ss))}

def decide.rs(+w: Walk, +rs: List<&2, EL.Res>, ss: List<&2, SK.Side>) -> Dec:
  decide.lp(w, rs, ymons(rs, Nil{}), ss)

def decide.c(+w: Walk, mj: Maybe<&2, Nat>, +ss: List<&2, SK.Side>) -> Dec:
  match mj:
    case Some{j}:
      DRow{w, j}
    case None{}:
      decide.rs(w, sres(Walk.rows(w), ss), ss)

def decide.w(+w: Walk, +ss: List<&2, SK.Side>) -> Dec:
  decide.c(w, crow(Walk.rows(w), 0n), ss)

def decide(es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Dec:
  decide.w(walk(es, Nil{}), ss)

# The refutation
# --------------

type Cert is Data:
  Cert{ls: List<&2, S.Q>, ms: List<&2, S.Q>, k: S.Q}

def qz(z: S.Z) -> S.Q:
  S.Q{z, S.XH{}}

def hd(u: List<&2, S.Z>) -> S.Z:
  match u:
    case Nil{}:
      S.Z0{}
    case Con{x, t}:
      x

def tl(u: List<&2, S.Z>) -> List<&2, S.Z>:
  match u:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

# the multipliers over es from those over the rows' equations (c_j for the
# j-th kept one, times its den), 0 at the dropped ones
def expand(keep: List<&2, Bool>, es: List<&2, E.QExpr>, +cs: List<&2, S.Z>) -> List<&2, S.Q>:
  match keep es:
    case Nil{} es:
      Nil{}
    case Con{b, kt} Nil{}:
      Nil{}
    case Con{True{}, kt} Con{e, et}:
      Con{qz(S.Z.mul(hd(cs), S.Zpos{QN.den(e)})), expand(kt, et, tl(cs))}
    case Con{False{}, kt} Con{e, et}:
      Con{qz(S.Z0{}), expand(kt, et, cs)}

def qzeros(ss: List<&2, SK.Side>) -> List<&2, S.Q>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{qz(S.Z0{}), qzeros(t)}

# -|c|, and the sign that sends c there
def nabs(c: S.Z) -> S.Z:
  match c:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      S.Zneg{p}
    case S.Zneg{p}:
      S.Zneg{p}

def nsgn(c: S.Z) -> S.Z:
  match c:
    case S.Z0{}:
      S.Zneg{S.XH{}}
    case S.Zpos{p}:
      S.Zneg{S.XH{}}
    case S.Zneg{p}:
      S.Zpos{S.XH{}}

# a constant row c: -sgn(c) (its combination) = -|c|
def cert.row(+keep: List<&2, Bool>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +r: EL.Row) -> Cert:
  Cert{expand(keep, es, EL.vscale(nsgn(EL.cz(Nil{}, Row.p(r))), EL.vsnoc(Row.cb(r), S.Zpos{Row.bt(r)}))), qzeros(ss), qz(nabs(EL.cz(Nil{}, Row.p(r))))}

# the simplex's certificate from the leaving slack i's row (D, M): mu_k =
# D at i, -M_ik at the other slacks (m of them), from index k
def mults(+r: List<&2, S.Z>, +i: Nat, +d: S.Pos, m: Nat, +k: Nat) -> List<&2, S.Z>:
  match m:
    case 0n:
      Nil{}
    case 1n+j:
      Con{S.Z.add(S.Z.neg(SX.at(r, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d})), mults(r, i, d, j, 1n+k)}

def reslen(rs: List<&2, EL.Res>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{r, t}:
      1n+reslen(t)

# sum mu_k cb_k (the basis's integer multipliers)
def cbsum(mu: List<&2, S.Z>, rs: List<&2, EL.Res>) -> List<&2, S.Z>:
  match mu rs:
    case Nil{} rs:
      Nil{}
    case Con{u, ut} Nil{}:
      Nil{}
    case Con{u, ut} Con{r, rt}:
      EL.vadd(EL.vscale(u, Res.cb(r)), cbsum(ut, rt))

# sum mu_k b_k
def ksum(mu: List<&2, S.Z>, rs: List<&2, EL.Res>) -> S.Z:
  match mu rs:
    case Nil{} rs:
      S.Z0{}
    case Con{u, ut} Nil{}:
      S.Z0{}
    case Con{u, ut} Con{r, rt}:
      S.Z.add(S.Z.mul(u, EL.cz(Nil{}, Res.p(r))), ksum(ut, rt))

# m_k = mu_k bt_k den(s_k)
def smults(mu: List<&2, S.Z>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>) -> List<&2, S.Q>:
  match mu rs ss:
    case Nil{} rs ss:
      Nil{}
    case Con{u, ut} Nil{} ss:
      Nil{}
    case Con{u, ut} Con{r, rt} Nil{}:
      Nil{}
    case Con{u, ut} Con{r, rt} Con{s, st}:
      Con{qz(S.Z.mul(u, S.Zpos{S.Pos.mul(Res.bt(r), QN.den(sexpr(s)))})), smults(ut, rt, st)}

def cert.lp(+keep: List<&2, Bool>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +rs: List<&2, EL.Res>, +mu: List<&2, S.Z>) -> Cert:
  Cert{expand(keep, es, cbsum(mu, rs)), smults(mu, rs, ss), qz(ksum(mu, rs))}

def cert.run(+keep: List<&2, Bool>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +rs: List<&2, EL.Res>, r: SX.Run) -> Maybe<&2, Cert>:
  match r:
    case SX.Go{t}:
      None{}
    case SX.Sat{t}:
      None{}
    case SX.Unsat{+t, +i}:
      Some{cert.lp(keep, es, ss, rs, mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), reslen(rs), 0n))}

# the refutation, if there is one
def cert(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, d: Dec) -> Maybe<&2, Cert>:
  match d:
    case DRow{+w, j}:
      Some{cert.row(Walk.keep(w), es, ss, rowat(Walk.rows(w), j))}
    case DLp{w, rs, ys, r}:
      cert.run(Walk.keep(w), es, ss, rs, r)

def refute(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Maybe<&2, Cert>:
  cert(es, ss, decide(es, ss))
