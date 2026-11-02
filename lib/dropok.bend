# bend-cad: what a degree-0 drop's reason establishes (PLAN-sk13b B4.6).
# Proof-side definitions: nothing here runs in the solver. A drop is
# correct by construction (lib/ckpf.bend: why_pass proves every drop the
# pass records passes this), and lib/vrdpf.bend says what passing means:
# - the reason is a constant combination (spec/solve.bend: WLin) whose
#   every equation is in the system solved (its constraint not red,
#   itself not dropped), and g - (q_1 g_i1 + ... + q_n g_in) normalizes
#   to 0. So wherever the system solved holds, g holds.
# A direction drop (WDer) passes no degree-0 test; what its derivation
# establishes is the direction layer's (lib/dirpf.bend: sound).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./qnorm.bend as QN

# the combination's right side, q_1 g_i1 + ... + q_n g_in (the shape of
# spec/solve.bend's lin)
def comb.rhs(+es: List<&2, E.QExpr>, ms: List<&2, SV.Mul>) -> E.QExpr:
  match ms:
    case Nil{}:
      E.QCst{S.Q{S.Z0{}, S.XH{}}}
    case Con{SV.Mul{i, q}, t}:
      E.QAdd{E.QMul{E.QCst{q}, SV.eqat(es, i)}, comb.rhs(es, t)}

# equation i is in the system solved
def solved_at(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +i: Nat) -> Bool:
  SV.band(SV.bnot(SV.mem(SV.nth(own, i), red)), SV.bnot(SV.mem(i, ds)))

def comb.solved(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, ms: List<&2, SV.Mul>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{SV.Mul{+i, q}, t}:
      SV.band(solved_at(own, red, ds, i), comb.solved(own, red, ds, t))

def drop.ok(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, d: SV.Drop) -> Bool:
  match d:
    case SV.Drop{+j, +nd, SV.WLin{+ms}}:
      SV.band(comb.solved(own, red, ds, ms), QN.qzero(E.QSub{SV.eqat(es, j), comb.rhs(es, ms)}))
    case SV.Drop{+j, +nd, SV.WDer{dv}}:
      False{}

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
    case SV.Conflict{s, cns}:
      True{}

# every class's dropped equations pass (red: the red constraints, ds: the
# dropped equations)
def dck(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, cls: List<&2, SV.Class>) -> Bool:
  match cls:
    case Nil{}:
      True{}
    case Con{k, t}:
      SV.band(kdrops.ok(es, own, red, ds, k), dck(es, own, red, ds, t))
