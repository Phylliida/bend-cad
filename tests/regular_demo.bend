# solve_complete's regularity hypothesis (spec/deriv.bend: Regular) can
# hold: a check that its statement is not vacuous by construction (its
# first draft compared matrices as lists, and M.ident stores rows without
# trailing zeros, so no product could ever equal it). In the canonical
# rationals (lib/qfield.bend, where everything computes): A = (0, 0) and
# B = (6, 0) are pinned (the solver's own pins_of), P is at distance 5
# from both, and at P = (3, 4) the Jacobian of the kept system in the free
# variables (P's, as SV.free computes them) is [[6, 8], [-6, 8]], with
# inverse [[1/12, -1/12], [1/16, 1/16]]. The point also solves the system.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/deriv.bend as DV
import ../lib/qfield.bend as QF
import ../lib/solve.bend as SO

def qc(n: S.Pos) -> E.QExpr:
  E.QCst{S.Q{S.Zpos{n}, S.XH{}}}

def five() -> S.Pos:
  S.XI{S.XO{S.XH{}}}

def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}, SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}],
    [SK.Rec{0n, False{}, SK.Distance{0n, 2n, qc(five())}}, SK.Rec{1n, False{}, SK.Distance{1n, 2n, qc(five())}}]}

def q(+n: S.Z, +d: S.Pos) -> QF.QC:
  QF.of_q(S.Q{n, d})

def zi(n: S.Pos) -> S.Z:
  S.Zpos{n}

# (0, 0), (6, 0), (3, 4)
def x() -> List<&2, QF.QC>:
  [q(S.Z0{}, S.XH{}), q(S.Z0{}, S.XH{}), q(zi(S.XO{S.XI{S.XH{}}}), S.XH{}), q(S.Z0{}, S.XH{}), q(zi(S.XI{S.XH{}}), S.XH{}), q(zi(S.XO{S.XO{S.XH{}}}), S.XH{})]

# [[1/12, -1/12], [1/16, 1/16]]
def y() -> List<&2, List<&2, QF.QC>>:
  [[q(zi(S.XH{}), S.XO{S.XO{S.XI{S.XH{}}}}), q(S.Zneg{S.XH{}}, S.XO{S.XO{S.XI{S.XH{}}}})],
   [q(zi(S.XH{}), S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}), q(zi(S.XH{}), S.XO{S.XO{S.XO{S.XO{S.XH{}}}}})]]

# the solver pins A and B
def pins() -> {SO.pins_of(sk()) == [0n, 1n, 2n, 3n] : List<&2, Nat>}:
  {==}

def solves() -> SK.Zeros(~QF.qfield(), x(), SK.Sketch.eqs(SV.mark(SO.red_of(sk()), sk()))):
  ({==}, ({==}, Unit{}))

def regular() -> DV.Regular(~QF.qfield(), x(), SK.Sketch.eqs(SV.mark(SO.red_of(sk()), sk())), SV.free(SO.nvars(sk()), 0n, SO.pins_of(sk()))):
  ({==}, (y(), ((({==}, ({==}, Unit{})), (({==}, ({==}, Unit{})), Unit{})), (({==}, ({==}, Unit{})), (({==}, ({==}, Unit{})), Unit{})))))
