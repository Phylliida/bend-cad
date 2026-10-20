# Diagnostic (untrusted): lib/pass.bend's classes on ./sketch.in (the
# format of proto/probe_elim.bend), one line per constraint.
# Native: bin/bend proto/probe_pass.bend -o proto/probe_pass.
# Built 2026-10-20 for PLAN-sk13a S4.

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/pass.bend as PA
import ../proto/probe_elim.bend as PE
import ../proto/block.bend as B

def nshow(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ Nat.show(h) ++ nshow(t)

def kshow(k: SV.Class) -> String:
  match k:
    case SV.Kept{ds}:
      "kept, dropped:" ++ nshow(SV.drops(ds))
    case SV.Amber{ds, rs}:
      "amber, dropped:" ++ nshow(SV.drops(ds))
    case SV.Over{j, s, w}:
      "over at " ++ Nat.show(j) ++ ", s:" ++ nshow(s) ++ ", w:" ++ nshow(w)
    case SV.Conflict{s}:
      "conflict, support:" ++ nshow(s)

def cshow(cls: List<&2, SV.Class>, +i: Nat) -> String:
  match cls:
    case Nil{}:
      ""
    case Con{k, t}:
      "  #" ++ Nat.show(i) ++ " " ++ kshow(k) ++ "\n" ++ cshow(t, 1n+i)

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    IO.print(cshow(PA.classes(PE.sk.of(s)), 0n))
