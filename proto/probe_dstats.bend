# Diagnostic (untrusted): the shape of lib/dclose.bend's runs on
# ./sketch.in (the format of proto/probe_elim.bend). For each constraint
# c, the closure of the facts of c and every constraint before it, in
# their context (as lib/dconflict.bend's dirref would run it with every
# earlier constraint kept): the rounds, how it ended, and the final
# skeleton's size.
# Native: bin/bend proto/probe_dstats.bend -o <out>.
# Built 2026-10-30 for the closure's performance redesign.

import Base
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ../lib/pass.bend as PA
import ../lib/dclose.bend as DC
import ../lib/kspace.bend as KS
import ../lib/dconflict.bend as DCF
import ../proto/probe_elim.bend as PE
import ../proto/block.bend as B

def upto(n: Nat, +i: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{i, upto(m, 1n+i)}

def len.n(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.n(t)

def len.d(xs: List<&2, DR.Der>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.d(t)

def len.m(xs: List<&2, DC.Mem>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.m(t)

def len.l(xs: List<&2, DC.Link>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.l(t)

def len.f(xs: List<&2, DR.Fact>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.f(t)

def len.r(xs: List<&2, DR.Node>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len.r(t)

def stats.s(+s: DC.Sk) -> String:
  "K " ++ Nat.show(len.d(KS.ks.ds(DC.Sk.k(s)))) ++ ", records " ++ Nat.show(len.m(DC.Sk.ms(s))) ++ ", roots " ++ Nat.show(len.r(DC.roots(DC.Sk.ms(s)))) ++ ", links " ++ Nat.show(len.l(DC.Sk.ls(s)))

def oshow(o: DC.Out) -> String:
  match o:
    case DC.OStep{+s}:
      "step; " ++ stats.s(s)
    case DC.OFix{+s}:
      "fix; " ++ stats.s(s)
    case DC.OOne{d}:
      "one"
    case DC.OVoid{g, dr, di}:
      "void " ++ Nat.show(g)

# the run, counting its rounds
def runc(fuel: Nat, o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +n: Nat) -> String:
  match fuel o:
    case 0n o:
      "rounds " ++ Nat.show(n) ++ ", out of fuel: " ++ oshow(o)
    case 1n+f DC.OStep{s}:
      runc(f, DC.round(es, fs, t, cs, ids, s), es, fs, t, cs, ids, 1n+n)
    case 1n+f o:
      "rounds " ++ Nat.show(n) ++ ", " ++ oshow(o)

def one(+sk: SK.Sketch, +c: Nat) -> String:
  +cs = upto(1n+c, 0n)
  +fs = SV.rfacts(sk, cs)
  +es = SV.ents(sk)
  +cx = SV.eqs_of(sk, cs)
  +sp = DC.sp.of(cx, DC.SP{Nil{}, Nil{}})
  "  #" ++ Nat.show(c) ++ " facts " ++ Nat.show(len.f(fs)) ++ ", fuel " ++ Nat.show(DC.dfuel(es, fs)) ++ ": " ++ runc(DC.dfuel(es, fs), DC.OStep{DC.sk0(es, fs, sp)}, es, fs, DCF.tv(sk), sp, DC.segids(es), 0n) ++ "\n"

def all(n: Nat, +sk: SK.Sketch, +c: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      one(sk, c) ++ all(m, sk, 1n+c)

def ncons(rs: List<&2, SK.Rec>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+ncons(t)

def show(+sk: SK.Sketch) -> String:
  "segments " ++ Nat.show(len.n(DC.segids(SV.ents(sk)))) ++ "\n" ++ all(ncons(PA.recs(sk)), sk, 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    IO.print(show(PE.sk.of(s)))
