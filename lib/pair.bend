# bend-cad: the pair test (PLAN-sk13b B3): given polynomials u, v and the
# echelon rows of a span B, find (a, b), not both 0, with a u + b v in the
# span. If u is in it, (1, 0). Otherwise u joins the rows, and if v is then
# in the span of B and u, with u's coefficient c, then v - c u is in the
# span of B: (-c, 1). Otherwise there is none (lib/pairpf.bend). A hull's
# label test (u, v the encodings of z_b and i z_b) and the frame test
# against K (u, v = Im z, -Re z) are this test.
#
# Untrusted in the sense of the rest of lib/: its properties are proven
# (lib/pairpf.bend), nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV

type Pr is Data:
  Pr{a: S.Q, b: S.Q}

def qdrop(n: Nat, ls: List<&2, S.Q>) -> List<&2, S.Q>:
  match n ls:
    case 0n ls:
      ls
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{l, lt}:
      qdrop(m, lt)

def qhd(ls: List<&2, S.Q>) -> S.Q:
  match ls:
    case Nil{}:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt}:
      l

# the coefficient of the generator after B (0 if there is none)
def lastc(+ls: List<&2, S.Q>, +B: List<&2, E.QExpr>) -> S.Q:
  qhd(qdrop(SV.neqs(B), ls))

def pt.second(b: Bool, +rows2: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr) -> Maybe<&2, Pr>:
  match b:
    case True{}:
      Some{Pr{S.Q.neg(lastc(DV.dropls(DV.rescb(EL.resid(rows2, v)), DV.resbt(EL.resid(rows2, v)), v, EP.qsnoc(B, u)), B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}}
    case False{}:
      None{}

def pt.first(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr) -> Maybe<&2, Pr>:
  match b:
    case True{}:
      Some{Pr{S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}}}
    case False{}:
      pt.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)

# (a, b), not both 0, with a u + b v in the span of B (rows its echelon
# form), or none
def ptest(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr) -> Maybe<&2, Pr>:
  pt.first(EP.isnil(EP.resp(EL.resid(rows, u))), rows, B, u, v)

# a u + b v
def pcomb(+p: Pr, +u: E.QExpr, +v: E.QExpr) -> E.QExpr:
  match p:
    case Pr{a, b}:
      E.QAdd{E.QMul{E.QCst{a}, u}, E.QMul{E.QCst{b}, v}}
