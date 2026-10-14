# Prints the structure (lib/struct.bend) of a few systems: the depth-N
# circle chain, the circle demo, an over-constrained pair, a cyclic pair.
# Native: bin/bend proto/struct_run.bend -o <out> && <out> --threads 1

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../lib/struct.bend as ST

def shown(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      Nat.show(h)
    case Con{h, t}:
      Nat.show(h) ++ " " ++ shown(t)

def showb(bs: List<&2, ST.SkB>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{ST.SkB{es, vs, ps}, t}:
      "  eqs [" ++ shown(es) ++ "] vars [" ++ shown(vs) ++ "] pars [" ++ shown(ps) ++ "]\n" ++ showb(t)

def showr(rs: List<&2, ST.Red>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{ST.Red{e, s, w}, t}:
      "  red eq " ++ Nat.show(e) ++ ": S [" ++ shown(s) ++ "] W [" ++ shown(w) ++ "]\n" ++ showr(t)

def show(sk: ST.Skel) -> String:
  match sk:
    case ST.Skel{vp, ep, np, bs, red}:
      "vp [" ++ shown(vp) ++ "]\nep [" ++ shown(ep) ++ "]\npins " ++ Nat.show(np) ++ "\n" ++ showb(bs) ++ showr(red)

def qc(n: S.Pos) -> E.QExpr:
  E.QCst{S.Q{S.Zpos{n}, S.XH{}}}

def three() -> S.Pos:
  S.XI{S.XH{}}

# the chain: points P_0 .. P_{n+1}, P_k at distance 3 from P_{k-2}, P_{k-1}
def pts(n: Nat, +k: Nat) -> List<&2, SK.Ent>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{SK.Ent{k, False{}, SK.GPoint{Nat.mul(2n, k), 1n+Nat.mul(2n, k)}}, pts(m, 1n+k)}

def cons(n: Nat, +k: Nat) -> List<&2, SK.Rec>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{SK.Rec{Nat.mul(2n, k), False{}, SK.Distance{Nat.sub(k, 2n), k, qc(three())}},
        Con{SK.Rec{1n+Nat.mul(2n, k), False{}, SK.Distance{Nat.sub(k, 1n), k, qc(three())}}, cons(m, 1n+k)}}

def coords(n: Nat) -> List<&2, SK.VKind>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{SK.Coord{}, coords(m)}

def chain(+n: Nat) -> SK.Sketch:
  SK.Sketch{coords(Nat.mul(2n, 2n+n)), pts(2n+n, 0n), cons(n, 2n)}

# the circle demo (tests/circle_plan_demo.bend)
def circle() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Length{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}},
     SK.Ent{2n, False{}, SK.GPoint{5n, 6n}}, SK.Ent{3n, False{}, SK.GCirc{0n, 4n}}],
    [SK.Rec{0n, False{}, SK.Radius{3n, qc(three())}}, SK.Rec{1n, False{}, SK.OnCircle{2n, 3n}}, SK.Rec{2n, False{}, SK.Distance{1n, 2n, qc(three())}}]}

def fx(+v: Nat) -> SK.Rec:
  SK.Rec{v, False{}, SK.Fix{v, S.Q{S.Z0{}, S.XH{}}}}

# two fixed points and a distance between them: one equation too many
def over() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}],
    [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}],
    [fx(0n), fx(1n), fx(2n), fx(3n), SK.Rec{9n, False{}, SK.Distance{0n, 1n, qc(three())}}]}

# x + y = 3, x - y = 1: one block of two
def cyc() -> List<&2, E.QExpr>:
  [E.QSub{E.QAdd{E.QVar{0n}, E.QVar{1n}}, qc(three())}, E.QSub{E.QSub{E.QVar{0n}, E.QVar{1n}}, qc(S.XH{})}]

def run(+sk: SK.Sketch, nv: Nat) -> String:
  show(ST.structure(SK.Sketch.eqs(sk), nv))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("chain 4:\n" ++ run(chain(4n), 12n))
    IO.print("circle:\n" ++ run(circle(), 7n))
    IO.print("over:\n" ++ run(over(), 4n))
    IO.print("cyclic:\n" ++ show(ST.structure(cyc(), 2n)))
