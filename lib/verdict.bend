# bend-cad: the verdict's exact check (PLAN-sk13a S5): what the plan does
# not cover is certified here, from the answer's classes alone;
# lib/vsdpf.bend says what a passing check means. Dropped equations are
# not checked: each is correct by construction (PLAN-sk13b B4.6;
# lib/dropok.bend, lib/ckpf.bend: why_pass).
#
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
    case SV.Conflict{s, cns}:
      True{}

# every amber constraint's side conditions are certified (cls from
# position c)
def ack(+sk: SK.Sketch, +red: List<&2, Nat>, cls: List<&2, SV.Class>, +c: Nat) -> Bool:
  match cls:
    case Nil{}:
      True{}
    case Con{k, t}:
      SV.band(kamber.ok(sk, red, c, k), ack(sk, red, t, 1n+c))

# From the answer's classes
# -------------------------

def exact(+sk: SK.Sketch, +cls: List<&2, SV.Class>) -> Bool:
  ack(sk, SV.reds(cls), cls, 0n)
