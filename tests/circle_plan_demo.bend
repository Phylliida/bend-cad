# The sketch laws' hypotheses with a variable side condition. A circle
# about A whose radius is a variable r, fixed at 3 by a Radius dimension;
# P lies on it (OnCircle) and at distance 3 from B. A = (0, 0) and
# B = (4, 0) are pinned; the plan solves r (a 1 × 1 block, exact, radius 0)
# and then P with r among its parameters (tests/chain_data.bend: cr_*).
# The circle's side condition r > 0 is checked over the plan's box,
# together with the dimensions' d ≥ 0. Refused: a box in which r may reach
# 0, and a radius of 0 (no box around r = 3 then solves r - 0 = 0).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ./chain_data.bend as D

def c(n: S.Pos) -> E.QExpr:
  E.QCst{S.Q{S.Zpos{n}, S.XH{}}}

def three() -> S.Pos:
  S.XI{S.XH{}}

# points 0 A, 1 B, 2 P; circle 3 about A with radius variable 4
def ents() -> List<&2, SK.Ent>:
  [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}},
   SK.Ent{2n, False{}, SK.GPoint{5n, 6n}}, SK.Ent{3n, False{}, SK.GCirc{0n, 4n}}]

def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Length{}, SK.Coord{}, SK.Coord{}], ents(),
    [SK.Rec{0n, False{}, SK.Radius{3n, c(three())}}, SK.Rec{1n, False{}, SK.OnCircle{2n, 3n}}, SK.Rec{2n, False{}, SK.Distance{1n, 2n, c(three())}}]}

# the same with radius 0
def sk0() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Length{}, SK.Coord{}, SK.Coord{}], ents(),
    [SK.Rec{0n, False{}, SK.Radius{3n, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}, SK.Rec{1n, False{}, SK.OnCircle{2n, 3n}}, SK.Rec{2n, False{}, SK.Distance{1n, 2n, c(three())}}]}

def wf() -> SK.Sketch.wf(sk()):
  ((Unit{}, (Unit{}, (Unit{}, ({==}, Unit{})))), ({==}, (Unit{}, (({==}, {==}), (Unit{}, (({==}, {==}), (Unit{}, Unit{})))))))

def covered() -> {BX.Sketch.within(sk(), List.length(&2, N.NC(KI.dnum()), D.cr_gc())) == True{} : Bool}:
  {==}

def plan_ok() -> {PL.check(~KI.dnum(), SK.Sketch.eqs(sk()), D.cr_gc(), D.cr_gr(), D.cr_plan()) == True{} : Bool}:
  {==}

# r > 0 (the circle), and d ≥ 0 twice (the dimensions), over the box
def sides_ok() -> {PL.check_sides(~KI.dnum(), SK.Sketch.sides(sk()), D.cr_gc(), D.cr_gr()) == True{} : Bool}:
  {==}

def sides_wide() -> {PL.check_sides(~KI.dnum(), SK.Sketch.sides(sk()), D.cr_gc(), D.cr_gr_wide()) == False{} : Bool}:
  {==}

def radius0() -> {PL.check(~KI.dnum(), SK.Sketch.eqs(sk0()), D.cr_gc(), D.cr_gr(), D.cr_plan()) == False{} : Bool}:
  {==}
