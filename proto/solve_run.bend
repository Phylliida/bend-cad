# Runs the verified solver on a few sketches and prints its answers: the
# word solver the CLI runs (lib/fast.bend), and whether lib/solve.bend's
# reference gives the same boxes (ROADMAP: fast_solve proves it does).
# Native: bin/bend proto/solve_run.bend -o <out>; <out> --threads 1

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/solve.bend as SO
import ../lib/fast.bend as FS
import ../lib/karith.bend as KA
import ./struct_run.bend as SR

def shown(xs: List<&2, Nat>) -> String:
  SR.shown(xs)

# each red constraint's reason, in order
def showc(+sk: SK.Sketch, cs: List<&2, SV.Class>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{SV.Over{+j, s, w}, t}:
      " [its equation " ++ Nat.show(SO.eqlabel(sk, j)) ++ " (eq " ++ Nat.show(j) ++ ") in S {" ++ shown(s) ++ "} over W {" ++ shown(w) ++ "}]" ++ showc(sk, t)
    case Con{SV.Conflict{s}, t}:
      " [conflicts with {" ++ shown(s) ++ "}]" ++ showc(sk, t)
    case Con{SV.Kept{ds}, t}:
      showc(sk, t)
    case Con{SV.Amber{ds, rs}, t}:
      showc(sk, t)

def dlen(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+dlen(t)

def show(+sk: SK.Sketch, o: SO.Out) -> String:
  match o:
    case SO.Out{ok, +cls, pins, gc, gr, plan}:
      "certified " ++ Bool.show(ok) ++ ", box of " ++ Nat.show(dlen(gc)) ++ ", pins {" ++ shown(pins) ++ "}, red {" ++ shown(SV.reds(cls)) ++ "}" ++ showc(sk, cls)

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

def dn(n: Nat) -> S.D:
  S.D{S.Z.of_diff(0n, n), 0n}

def fxq(+i: Nat, +v: Nat, q: S.Q) -> SK.Rec:
  SK.Rec{i, False{}, SK.Fix{v, q}}

# (from the audit) m = (v0, v1), p = (v2, v3), q = (v4, v5), a = p -> q;
# 0: y_m = 0, 1: y_p = 0, 2: y_q = 0, 3: m is the midpoint of a,
# 4: x_m = 0, 5: x_p = -1, 6: x_q = 1. The midpoint's y equation is
# redundant (all three y are fixed); dropping the midpoint alone leaves
# six independent fixes, so it is the only red constraint needed.
def mid() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}},
     SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}, SK.Ent{3n, False{}, SK.GSeg{1n, 2n}}],
    [fxq(0n, 1n, S.Q{S.Z0{}, S.XH{}}), fxq(1n, 3n, S.Q{S.Z0{}, S.XH{}}), fxq(2n, 5n, S.Q{S.Z0{}, S.XH{}}), SK.Rec{3n, False{}, SK.Midpoint{0n, 3n}},
     fxq(4n, 0n, S.Q{S.Z0{}, S.XH{}}), fxq(5n, 2n, S.Q{S.Zneg{S.XH{}}, S.XH{}}), fxq(6n, 4n, S.Q{S.Zpos{S.XH{}}, S.XH{}})]}

def mid_g0() -> List<&2, S.D>:
  [d(0n), d(0n), dn(1n), d(0n), d(3n), d(0n)]

# (from the completeness audit) a point, a circle on it with radius
# variable 2, Radius = 2^-70: 64 bits rounds the radius to 0 and the box
# fails r > 0; the loop retries and 96 bits certifies
def tiny() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Length{}], [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GCirc{0n, 2n}}],
    [SK.Rec{0n, False{}, SK.Radius{1n, E.QCst{S.Q{S.Zpos{S.XH{}}, S.Pos.pow2(70n)}}}}]}

# the same dyadic, mantissa and exponent
def zeq.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def zeq(+a: S.Z, +b: S.Z) -> Bool:
  zeq.go(S.Z.cmp(a, b))

def deqs(xs: List<&2, S.D>, ys: List<&2, S.D>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{+x, xt} Con{+y, yt}:
      KA.band(KA.band(zeq(S.D.man(x), S.D.man(y)), KA.nateq(S.D.exp(x), S.D.exp(y))), deqs(xt, yt))

def beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# the two answers agree: ok, pins and the box exactly
def same(a: SO.Out, b: SO.Out) -> Bool:
  match a b:
    case SO.Out{ok, cls, pins, gc, gr, plan} SO.Out{ok2, cls2, pins2, gc2, gr2, plan2}:
      KA.band(beq(ok, ok2), KA.band(SO.nl_eq(pins, pins2), KA.band(deqs(gc, gc2), deqs(gr, gr2))))

def a1() -> Bool:
  same(FS.wsolve(SR.circle(), circle_g0()), SO.solve(SR.circle(), circle_g0()))

def a2() -> Bool:
  same(FS.wsolve(SR.over(), ds([0n, 0n, 0n, 0n])), SO.solve(SR.over(), ds([0n, 0n, 0n, 0n])))

def a3() -> Bool:
  same(FS.wsolve(free(), ds([5n, 7n])), SO.solve(free(), ds([5n, 7n])))

def a4() -> Bool:
  same(FS.wsolve(far(), circle_g0()), SO.solve(far(), circle_g0()))

def a5() -> Bool:
  same(FS.wsolve(mid(), mid_g0()), SO.solve(mid(), mid_g0()))

def a6() -> Bool:
  same(FS.wsolve(tiny(), ds([0n, 0n, 0n])), SO.solve(tiny(), ds([0n, 0n, 0n])))

def agree() -> Bool:
  KA.band(a1(), KA.band(a2(), KA.band(a3(), KA.band(a4(), KA.band(a5(), a6())))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("circle: " ++ show(SR.circle(), FS.wsolve(SR.circle(), circle_g0())))
    IO.print("over:   " ++ show(SR.over(), FS.wsolve(SR.over(), ds([0n, 0n, 0n, 0n]))))
    IO.print("free:   " ++ show(free(), FS.wsolve(free(), ds([5n, 7n]))))
    IO.print("far:    " ++ show(far(), FS.wsolve(far(), circle_g0())))
    IO.print("mid:    " ++ show(mid(), FS.wsolve(mid(), mid_g0())))
    IO.print("tiny:   " ++ show(tiny(), FS.wsolve(tiny(), ds([0n, 0n, 0n]))))
    IO.print("the reference agrees: " ++ Bool.show(agree()))
