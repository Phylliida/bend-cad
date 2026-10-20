# Diagnostic (untrusted): lib/refute.bend's degree-0 decision on
# ./sketch.in (the format of proto/probe_elim.bend), ignoring classes:
# - all: every equation and side condition;
# - each prefix of the constraints (with the entities' sides), as the
#   single pass will ask for Conflict;
# - each side condition's negation against everything else (Implied).
# Prints each answer (ROW: a constant row; UNSAT/SAT: the simplex's), the
# pivots, and the largest D and entry (bits).
# Native: bin/bend proto/probe_refute.bend -o proto/probe_refute.
# Built 2026-10-19 for PLAN-sk13a S3.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/elim.bend as EL
import ../lib/simplex.bend as SX
import ../lib/refute.bend as RF
import ../proto/probe_elim.bend as PE
import ../proto/block.bend as B

type RC is Data:
  RC{r: SX.Run, n: Nat}

def advc(+lp: SX.LP, rc: RC) -> RC:
  match rc:
    case RC{r, n}:
      match r:
        case SX.Go{+t}:
          RC{SX.step(lp, t), 1n+n}
        case SX.Sat{t}:
          RC{SX.Sat{t}, n}
        case SX.Unsat{t, i}:
          RC{SX.Unsat{t, i}, n}

def runc(k: Nat, +lp: SX.LP, rc: RC) -> RC:
  match k:
    case 0n:
      advc(lp, rc)
    case 1n++j:
      runc(j, lp, runc(j, lp, rc))

def rbits(rs: List<&2, SX.Rw>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{SX.Rw{d, r}, t}:
      PE.nmax(PE.nmax(PE.pbits(d), PE.vbits(r)), rbits(t))

def tshow(t: SX.Tab) -> String:
  match t:
    case SX.Tab{rows, bas}:
      " bits " ++ Nat.show(rbits(rows))

def rcshow(rc: RC) -> String:
  match rc:
    case RC{r, n}:
      match r:
        case SX.Go{t}:
          "GO?! pivots " ++ Nat.show(n)
        case SX.Sat{t}:
          "SAT pivots " ++ Nat.show(n) ++ tshow(t)
        case SX.Unsat{t, i}:
          "UNSAT pivots " ++ Nat.show(n) ++ tshow(t)

def lpshow(+lp: SX.LP) -> String:
  "m " ++ Nat.show(SX.LP.m(lp)) ++ " n " ++ Nat.show(SX.LP.n(lp)) ++ " "

def dshow(+ss: List<&2, SK.Side>, d: RF.Dec) -> String:
  match d:
    case RF.DRow{w, j}:
      "ROW " ++ Nat.show(j)
    case RF.DLp{w, +rs, +ys, r}:
      lpshow(RF.mklp(ys, rs, ss)) ++ rcshow(runc(SX.LP.nv(RF.mklp(ys, rs, ss)), RF.mklp(ys, rs, ss), RC{SX.Go{SX.init(RF.mklp(ys, rs, ss))}, 0n}))

def dec(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> String:
  dshow(ss, RF.decide(es, ss))

def upto(c: Nat) -> List<&2, Nat>:
  match c:
    case 0n:
      [0n]
    case 1n++j:
      Con{c, upto(j)}

def prefixes(n: Nat, +sk: SK.Sketch, +c: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+j:
      "  #" ++ Nat.show(c) ++ " " ++ dec(SV.eqs_of(sk, upto(c)), SK.cats(SV.csides(sk, upto(c)), SV.esides(sk))) ++ "\n" ++ prefixes(j, sk, 1n+c)

def drop(ss: List<&2, SK.Side>, i: Nat) -> List<&2, SK.Side>:
  match ss i:
    case Nil{} i:
      Nil{}
    case Con{s, t} 0n:
      t
    case Con{s, t} 1n+k:
      Con{s, drop(t, k)}

def sidesn(ss: List<&2, SK.Side>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{s, t}:
      1n+sidesn(t)

def implied(n: Nat, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +i: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+j:
      "  side " ++ Nat.show(i) ++ " " ++ dec(es, SK.cats(drop(ss, i), [SV.negate(SV.side_at(ss, i))])) ++ "\n" ++ implied(j, es, ss, 1n+i)

def go(+sk: SK.Sketch) -> IO(Unit):
  do IO<Unit>:
    IO.print("all " ++ dec(SK.Sketch.eqs(sk), SK.Sketch.sides(sk)))
    IO.print("prefixes:\n" ++ prefixes(SV.ncons(sk), sk, 0n))
    IO.print("implied:\n" ++ implied(sidesn(SK.Sketch.sides(sk)), SK.Sketch.eqs(sk), SK.Sketch.sides(sk), 0n))

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    go(PE.sk.of(s))
