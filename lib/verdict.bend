# bend-cad: the verdict's exact checks (PLAN-sk13a S5): what the plan
# does not cover is certified here, from the answer's classes alone.
# Untrusted code; lib/vrdpf.bend says what a passing check means.
#
# - Every dropped equation's combination (spec/solve.bend: Comb):
#   h - 1 normalizes to 0, every multiplier is on an equation of the
#   system solved (its constraint not red, itself not dropped), and
#   g - (q_1 g_i1 + ... + q_n g_in) normalizes to 0. So wherever the
#   system solved holds, g holds.
# - Every amber constraint's side conditions: one refutation each
#   (spec/solve.bend: Ref) of the premises before it and the side's
#   negation, its signs checked (refok) and its identity normalized to
#   0. So wherever the premises hold, the side does.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./qnorm.bend as QN

# Dropped equations
# -----------------

def qone() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

# the combination's right side, q_1 g_i1 + ... + q_n g_in (the shape of
# spec/solve.bend's lin)
def comb.rhs(+es: List<&2, E.QExpr>, qs: List<&2, SV.Mul>) -> E.QExpr:
  match qs:
    case Nil{}:
      E.QCst{S.Q{S.Z0{}, S.XH{}}}
    case Con{SV.Mul{i, q}, t}:
      E.QAdd{E.QMul{q, SV.eqat(es, i)}, comb.rhs(es, t)}

# equation i is in the system solved
def solved_at(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +i: Nat) -> Bool:
  SV.band(SV.bnot(SV.mem(SV.nth(own, i), red)), SV.bnot(SV.mem(i, ds)))

def comb.solved(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, qs: List<&2, SV.Mul>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{SV.Mul{+i, q}, t}:
      SV.band(solved_at(own, red, ds, i), comb.solved(own, red, ds, t))

def drop.ok(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, d: SV.Drop) -> Bool:
  match d:
    case SV.Drop{+j, SV.Comb{+h, +qs}}:
      SV.band(QN.qzero(E.QSub{h, E.QCst{qone()}}), SV.band(comb.solved(own, red, ds, qs), QN.qzero(E.QSub{SV.eqat(es, j), comb.rhs(es, qs)})))

def drops.ok(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, dd: List<&2, SV.Drop>) -> Bool:
  match dd:
    case Nil{}:
      True{}
    case Con{d, t}:
      SV.band(drop.ok(es, own, red, ds, d), drops.ok(es, own, red, ds, t))

def kdrops.ok(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, k: SV.Class) -> Bool:
  match k:
    case SV.Kept{dd}:
      drops.ok(es, own, red, ds, dd)
    case SV.Amber{dd, rs}:
      drops.ok(es, own, red, ds, dd)
    case SV.Over{j, s, w}:
      True{}
    case SV.Conflict{s}:
      True{}

# every class's dropped equations are certified (red: the red
# constraints, ds: the dropped equations)
def dck(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, cls: List<&2, SV.Class>) -> Bool:
  match cls:
    case Nil{}:
      True{}
    case Con{k, t}:
      SV.band(kdrops.ok(es, own, red, ds, k), dck(es, own, red, ds, t))

# Amber side conditions
# ---------------------

# r refutes the equations es and side conditions ss
def ref.ok(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, r: SV.Ref) -> Bool:
  match r:
    case SV.Ref{+ls, +ms, +k}:
      SV.band(SV.refok(ls, ms, k, es, ss), QN.qzero(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}))

# rs refutes, for each of n side conditions of c from the i-th, the
# premises before c and that side's negation
def refs.ok(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, n: Nat, rs: List<&2, SV.Ref>, +i: Nat) -> Bool:
  match n rs:
    case 0n rs:
      True{}
    case 1n+m Nil{}:
      False{}
    case 1n+m Con{r, t}:
      SV.band(ref.ok(SV.pre_eqs(sk, red, c), SV.neg_pre(sk, red, c, i), r), refs.ok(sk, red, c, m, t, 1n+i))

def kamber.ok(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, k: SV.Class) -> Bool:
  match k:
    case SV.Kept{dd}:
      True{}
    case SV.Amber{dd, rs}:
      refs.ok(sk, red, c, SV.slen(SV.csides(sk, [c])), rs, 0n)
    case SV.Over{j, s, w}:
      True{}
    case SV.Conflict{s}:
      True{}

# every amber constraint's side conditions are certified (cls from
# position c)
def ack(+sk: SK.Sketch, +red: List<&2, Nat>, cls: List<&2, SV.Class>, +c: Nat) -> Bool:
  match cls:
    case Nil{}:
      True{}
    case Con{k, t}:
      SV.band(kamber.ok(sk, red, c, k), ack(sk, red, t, 1n+c))

# Both, from the answer's classes
# -------------------------------

def exact(+sk: SK.Sketch, +cls: List<&2, SV.Class>) -> Bool:
  SV.band(dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls), ack(sk, SV.reds(cls), cls, 0n))
