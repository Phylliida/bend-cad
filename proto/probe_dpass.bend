# Diagnostic (untrusted): lib/dpass.bend's classes (the pass with the
# direction layer) on ./sketch.in (the format of proto/probe_elim.bend),
# one line per constraint, with each drop's and conflict's nd.
# Native: bin/bend proto/probe_dpass.bend -o <out>.
# Built 2026-10-30 for PLAN-sk13b B4.7.

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/pass.bend as PA
import ../lib/dpass.bend as DP
import ../proto/probe_elim.bend as PE
import ../proto/block.bend as B

def nshow(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ Nat.show(h) ++ nshow(t)

def dnd(nd: List<&2, Nat>) -> String:
  match nd:
    case Nil{}:
      ""
    case Con{h, t}:
      "[nd" ++ nshow(Con{h, t}) ++ "]"

def dshow(ds: List<&2, SV.Drop>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{SV.Drop{j, nd, q}, t}:
      " " ++ Nat.show(j) ++ dnd(nd) ++ dshow(t)

def kshow(k: SV.Class) -> String:
  match k:
    case SV.Kept{ds}:
      "kept, dropped:" ++ dshow(ds)
    case SV.Amber{ds, rs}:
      "amber, dropped:" ++ dshow(ds)
    case SV.Over{j, s, w}:
      "over at " ++ Nat.show(j) ++ ", s:" ++ nshow(s) ++ ", w:" ++ nshow(w)
    case SV.Conflict{s, cns}:
      "conflict, support:" ++ nshow(s) ++ ", nd:" ++ nshow(cns)

def cshow(cls: List<&2, SV.Class>, +i: Nat) -> String:
  match cls:
    case Nil{}:
      ""
    case Con{k, t}:
      "  #" ++ Nat.show(i) ++ " " ++ kshow(k) ++ "\n" ++ cshow(t, 1n+i)

def show(+sk: SK.Sketch) -> String:
  cshow(DP.classes2(sk), 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    IO.print(show(PE.sk.of(s)))
