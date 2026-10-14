# The verified solver (lib/solve.bend) run inside Bend's own checker, and
# its laws (lib/solvepf.bend) at concrete sketches.
# - The circle demo (proto/struct_run.bend: a circle about A with a
#   variable radius fixed at 3, P on it and at distance 3 from B), drawn
#   with P at (2, 2): certified, nothing red. In every complete ordered
#   field a geometry in the returned box means the sketch (it has
#   P = (2, √5)); solve_unique then applies too (its hypotheses are met
#   here; an instance is left out of the gate: its type names the solve
#   six times, ~30 s to check).
# - Two points fixed at (0, 0) plus a distance of 3 between them: the
#   distance (the fifth constraint, position 4) is red, explained by 5
#   equations over 4 variables; the rest is certified.
# - The circle demo with |PB| = 10, more than |AB| + r = 7: no geometry
#   exists, and the solver refuses.
# - (From the audit) a midpoint whose y equation is redundant beside
#   x_q = 1: only the midpoint is red (its witness: its y equation and the
#   three y fixes, 4 equations over 3 variables); x_q = 1 stays.
# - The circle demo pins A and B (variables 0..3), held at the drawing.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/solvepf.bend as SP
import ../proto/struct_run.bend as SR
import ../proto/solve_run.bend as R

def ten() -> S.Pos:
  S.XO{S.XI{S.XO{S.XH{}}}}

# the circle demo with |PB| = 10
def far() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Length{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}},
     SK.Ent{2n, False{}, SK.GPoint{5n, 6n}}, SK.Ent{3n, False{}, SK.GCirc{0n, 4n}}],
    [SK.Rec{0n, False{}, SK.Radius{3n, SR.qc(SR.three())}}, SK.Rec{1n, False{}, SK.OnCircle{2n, 3n}}, SK.Rec{2n, False{}, SK.Distance{1n, 2n, SR.qc(ten())}}]}

def zeros4() -> List<&2, S.D>:
  R.ds([0n, 0n, 0n, 0n])

def circle_ok() -> {SO.Out.ok(SO.solve(SR.circle(), R.circle_g0())) == True{} : Bool}:
  {==}

def over_ok() -> {SO.Out.ok(SO.solve(SR.over(), zeros4())) == True{} : Bool}:
  {==}

def over_red() -> {SO.Out.red(SO.solve(SR.over(), zeros4())) == [4n] : List<&2, Nat>}:
  {==}

def far_refused() -> {SO.Out.ok(SO.solve(far(), R.circle_g0())) == False{} : Bool}:
  {==}

def mid_ok() -> {SO.Out.ok(SO.solve(R.mid(), R.mid_g0())) == True{} : Bool}:
  {==}

def mid_red() -> {SO.Out.red(SO.solve(R.mid(), R.mid_g0())) == [3n] : List<&2, Nat>}:
  {==}

def circle_pins() -> {SO.Out.pins(SO.solve(SR.circle(), R.circle_g0())) == [0n, 1n, 2n, 3n] : List<&2, Nat>}:
  {==}

# The laws at these sketches

def circle_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>) -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(SR.circle(), R.circle_g0())), SO.Out.gr(SO.solve(SR.circle(), R.circle_g0())), x) & SK.Sketch.means(~F, x, SV.mark(SO.Out.red(SO.solve(SR.circle(), R.circle_g0())), SR.circle()))):
  SP.solve_exists(~F, ~R, ~H, SR.circle(), R.circle_g0(), circle_ok())

def over_explained() -> {SV.explained(SR.over(), SO.Out.red(SO.solve(SR.over(), zeros4())), SO.Out.why(SO.solve(SR.over(), zeros4()))) == True{} : Bool}:
  SP.solve_red(SR.over(), zeros4(), over_ok())
