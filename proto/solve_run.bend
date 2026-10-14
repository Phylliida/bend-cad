# Runs the verified solver (lib/solve.bend) on a few sketches and prints
# its answers. Native: bin/bend proto/solve_run.bend -o <out>; <out> --threads 1

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/solve.bend as SO
import ./struct_run.bend as SR

def shown(xs: List<&2, Nat>) -> String:
  SR.shown(xs)

def showw(ws: List<&2, SV.Why>) -> String:
  match ws:
    case Nil{}:
      ""
    case Con{SV.Why{j, s, w}, t}:
      " [eq " ++ Nat.show(j) ++ " in S {" ++ shown(s) ++ "} over W {" ++ shown(w) ++ "}]" ++ showw(t)

def dlen(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+dlen(t)

def show(o: SO.Out) -> String:
  match o:
    case SO.Out{ok, red, why, gc, gr, plan}:
      "certified " ++ Bool.show(ok) ++ ", box of " ++ Nat.show(dlen(gc)) ++ ", red {" ++ shown(red) ++ "}" ++ showw(why)

def d(n: Nat) -> S.D:
  S.D{S.Z.of_diff(n, 0n), 0n}

def ds(xs: List<&2, Nat>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{d(x), ds(t)}

# the circle demo: A (0, 0), B (4, 0), r 3, P drawn at (2, 2) (exact: (2, √5))
def circle_g0() -> List<&2, S.D>:
  ds([0n, 0n, 4n, 0n, 3n, 2n, 2n])

# a free point
def free() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}], [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}], []}

def ten() -> S.Pos:
  S.XO{S.XI{S.XO{S.XH{}}}}

# the circle demo with |PB| = 10 > |AB| + r = 7: no geometry exists
def far() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Length{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}},
     SK.Ent{2n, False{}, SK.GPoint{5n, 6n}}, SK.Ent{3n, False{}, SK.GCirc{0n, 4n}}],
    [SK.Rec{0n, False{}, SK.Radius{3n, SR.qc(SR.three())}}, SK.Rec{1n, False{}, SK.OnCircle{2n, 3n}}, SK.Rec{2n, False{}, SK.Distance{1n, 2n, SR.qc(ten())}}]}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("circle: " ++ show(SO.solve(SR.circle(), circle_g0())))
    IO.print("over:   " ++ show(SO.solve(SR.over(), ds([0n, 0n, 0n, 0n]))))
    IO.print("free:   " ++ show(SO.solve(free(), ds([5n, 7n]))))
    IO.print("far:    " ++ show(SO.solve(far(), circle_g0())))
