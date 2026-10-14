# Parsing only (for timing proto/plan_chain_run.bend): a depth-N
# circle chain written by tools/gen_plan_chain.py to proto/plan_chain.txt.
# The chain is built as a sketch (points and driving Distance
# constraints); the checker reads the sketch's own exact system
# (Sketch.eqs) and side conditions (Sketch.sides). Untrusted driver.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../lib/certdef.bend as C
import ../spec/sketch.bend as SK
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ./block.bend as B

# Numbers (binary strings, most significant bit first)
# -------

def bit(b: Bool, p: S.Pos) -> S.Pos:
  match b:
    case True{}:
      S.XI{p}
    case False{}:
      S.XO{p}

def pos.go(s: String, acc: S.Pos) -> S.Pos:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      pos.go(t, bit(Char.is_eq(h, '1'), acc))

# the leading digit is 1
def pos(s: String) -> S.Pos:
  match s:
    case SNil{}:
      S.XH{}
    case SCon{h, t}:
      pos.go(t, S.XH{})

def z.of(neg: Bool, zero: Bool, s: String, t: String) -> S.Z:
  match neg zero:
    case True{} _:
      S.Zneg{pos(t)}
    case False{} True{}:
      S.Z0{}
    case False{} False{}:
      S.Zpos{pos(s)}

def z(s: String) -> S.Z:
  match s:
    case SNil{}:
      S.Z0{}
    case SCon{+h, +t}:
      z.of(Char.is_eq(h, '-'), Char.is_eq(h, '0'), SCon{h, t}, t)

def d.of(ps: List<&2, String>) -> S.D:
  match ps:
    case Con{m, Con{e, _}}:
      S.D{z(m), B.tok.nat(e)}
    case _:
      S.D{S.Z0{}, 0n}

def d(s: String) -> S.D:
  d.of(String.split(s, ':'))

def ds(ts: List<&2, String>) -> List<&2, S.D>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      Con{d(t), ds(rest)}

def qc(s: String) -> E.QExpr:
  E.QCst{S.Q{S.Zpos{pos(s)}, S.XH{}}}

# The sketch
# ----------

def pts(n: Nat, +k: Nat) -> List<&2, SK.Ent>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{SK.Ent{k, False{}, SK.GPoint{Nat.mul(2n, k), 1n+Nat.mul(2n, k)}}, pts(m, 1n+k)}

# P_k at distance r from P_{k-2} and s from P_{k-1}
def cons(rs: List<&2, String>, +k: Nat) -> List<&2, SK.Rec>:
  match rs:
    case Con{r, Con{s, t}}:
      Con{SK.Rec{Nat.mul(2n, k), False{}, SK.Distance{Nat.sub(k, 2n), k, qc(r)}},
        Con{SK.Rec{1n+Nat.mul(2n, k), False{}, SK.Distance{Nat.sub(k, 1n), k, qc(s)}}, cons(t, 1n+k)}}
    case _:
      []

def coords(n: Nat) -> List<&2, SK.VKind>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{SK.Coord{}, coords(m)}

def sketch(+n: Nat, rs: List<&2, String>) -> SK.Sketch:
  SK.Sketch{coords(Nat.mul(2n, 2n+n)), pts(2n+n, 0n), cons(rs, 2n)}

# The plan
# --------

def iota(n: Nat, +k: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n+m:
      Con{k, iota(m, 1n+k)}

def cert.of(xs: List<&2, S.D>) -> C.Cert<KI.dnum()>:
  match xs:
    case Con{c0, Con{c1, Con{r0, Con{r1, Con{q, Con{y00, Con{y01, Con{y10, Con{y11, Con{p0, Con{p1, Con{p2, Con{p3, Con{s0, Con{s1, Con{s2, Con{s3, _}}}}}}}}}}}}}}}}}:
      C.Cert{[c0, c1], [r0, r1], q, [[y00, y01], [y10, y11]], [p0, p1, p2, p3], [s0, s1, s2, s3]}
    case _:
      C.Cert{[], [], S.D{S.Z0{}, 0n}, [], [], []}

# block j: unknowns P_{j+2}, parameters P_j, P_{j+1}
def blocks(ls: List<&2, String>, +j: Nat) -> List<&2, PL.PBlock<KI.dnum()>>:
  match ls:
    case Nil{}:
      []
    case Con{l, rest}:
      Con{PL.PBlock{2n, iota(4n, Nat.mul(2n, j)), cert.of(ds(B.toks(l)))}, blocks(rest, 1n+j)}

def nonempty(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      []
    case Con{SNil{}, rest}:
      nonempty(rest)
    case Con{l, rest}:
      Con{l, nonempty(rest)}

def plen(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      1n
    case S.XO{q}:
      1n+plen(q)
    case S.XI{q}:
      1n+plen(q)

def zlen(z: S.Z) -> Nat:
  match z:
    case S.Z0{}:
      0n
    case S.Zpos{p}:
      plen(p)
    case S.Zneg{p}:
      plen(p)

def dsize(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{S.D{m, e}, t}:
      Nat.add(Nat.add(zlen(m), e), dsize(t))

def lsize(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{l, rest}:
      Nat.add(dsize(ds(B.toks(l))), lsize(rest))

def run(ls: List<&2, String>) -> String:
  match ls:
    case Con{meta, Con{gc, Con{gr, Con{rs, bl}}}}:
      "parsed size: " ++ Nat.show(Nat.add(Nat.add(dsize(ds(B.toks(gc))), dsize(ds(B.toks(gr)))), lsize(bl)))
    case _:
      "bad file"

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("proto/plan_chain.txt")
    IO.print(run(nonempty(String.lines(s))))
