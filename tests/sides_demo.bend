# DESIGN §8.6 over the whole vocabulary. The side conditions of
# tests/sketch_demo.bend's sketch (every constraint kind, a circle) are
# certified by the plan checker's check_sides over a box around its
# rational solution, with K = ℚ: radius 1/1000 on every variable, and
# radius 0. The law box_sides then makes them hold at every point of the
# box, in every ordered field. A box in which the aux length of AB, or the
# circle's radius, may be 0 is refused.

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as K
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ./sketch_demo.bend as SD

def recs(ks: List<&2, K.Constraint>) -> List<&2, K.Rec>:
  match ks:
    case Nil{}:
      []
    case Con{k, t}:
      Con{K.Rec{0n, False{}, k}, recs(t)}

def sk() -> K.Sketch:
  K.Sketch{[], SD.ents(), recs(SD.cons())}

def rad(+r: S.Q, n: Nat) -> List<&2, S.Q>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{r, rad(r, m)}

def certified() -> {PL.check_sides(~KI.qnum(), K.Sketch.sides(sk()), SD.good(), rad(SD.q(1n, 1000n), 12n)) == True{} : Bool}:
  {==}

def exact() -> {PL.check_sides(~KI.qnum(), K.Sketch.sides(sk()), SD.good(), rad(SD.q(0n, 1n), 12n)) == True{} : Bool}:
  {==}

# variable i gets radius w, the rest radius r
def rad1(+r: S.Q, +w: S.Q, n: Nat, i: Nat) -> List<&2, S.Q>:
  match n i:
    case 0n i:
      []
    case 1n+m 0n:
      Con{w, rad(r, m)}
    case 1n+m 1n+j:
      Con{r, rad1(r, w, m, j)}

# the aux length of AB (variable 11, value 4) within 5 of 4 may be 0
def aux_may_vanish() -> {PL.check_sides(~KI.qnum(), K.Sketch.sides(sk()), SD.good(), rad1(SD.q(1n, 1000n), SD.q(5n, 1n), 12n, 11n)) == False{} : Bool}:
  {==}

# so may the circle's radius (variable 10, value 5) within 6 of 5
def radius_may_vanish() -> {PL.check_sides(~KI.qnum(), K.Sketch.sides(sk()), SD.good(), rad1(SD.q(1n, 1000n), SD.q(6n, 1n), 12n, 10n)) == False{} : Bool}:
  {==}

# the aux length within 3 of 4 stays positive
def wide_but_fine() -> {PL.check_sides(~KI.qnum(), K.Sketch.sides(sk()), SD.good(), rad1(SD.q(1n, 1000n), SD.q(3n, 1n), 12n, 11n)) == True{} : Bool}:
  {==}
