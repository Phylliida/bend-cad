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
#   distance (the fifth constraint, position 4) is red, its class Over
#   (5 equations over 4 variables); the rest is kept and certified.
# - The circle demo with |PB| = 10, more than |AB| + r = 7: no geometry
#   exists, and the solver refuses (natively at the full budget too:
#   proto/solve_run.bend).
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
import ../lib/why.bend as WY
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

def over_red() -> {SV.reds(SO.Out.cls(SO.solve(SR.over(), zeros4()))) == [4n] : List<&2, Nat>}:
  {==}

# its class is Over (kind 2), the others Kept (kind 0)
def over_kind() -> {SV.kind(SV.class_at(SO.Out.cls(SO.solve(SR.over(), zeros4())), 4n)) == 2n : Nat}:
  {==}

def over_kept() -> {SV.kind(SV.class_at(SO.Out.cls(SO.solve(SR.over(), zeros4())), 3n)) == 0n : Nat}:
  {==}

# refused over two precisions (64 and 96 bits): every precision fails the
# same way, and all seven of level 0 cost minutes inside the checker
def far_refused() -> {SO.Out.ok(SO.solve_lw(far(), R.circle_g0(), 0n, 2n)) == False{} : Bool}:
  {==}

def mid_ok() -> {SO.Out.ok(SO.solve(R.mid(), R.mid_g0())) == True{} : Bool}:
  {==}

def mid_red() -> {SV.reds(SO.Out.cls(SO.solve(R.mid(), R.mid_g0()))) == [3n] : List<&2, Nat>}:
  {==}

def circle_pins() -> {SO.Out.pins(SO.solve(SR.circle(), R.circle_g0())) == [0n, 1n, 2n, 3n] : List<&2, Nat>}:
  {==}

# The laws at these sketches

def circle_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>) -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(SR.circle(), R.circle_g0())), SO.Out.gr(SO.solve(SR.circle(), R.circle_g0())), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve(SR.circle(), R.circle_g0()))), SR.circle()))):
  SP.solve_exists(~F, ~R, ~H, SR.circle(), R.circle_g0(), 0n, circle_ok())

# the red stage's witness for it is explained (sk-09's syntactic form,
# lib/why.bend; sk-13a's Honest replaces it, PLAN-sk13a.md S4)
def over_explained() -> {WY.explained(SR.over(), SO.red_of(SR.over()), SO.why_of(SR.over())) == True{} : Bool}:
  {==}
