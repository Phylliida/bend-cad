# Diagnostic (untrusted): lib/dclose.bend's fast run on ./sketch.in, one
# line printed as each step ends (pipe through a timestamp to time them):
# loop, the runs of proto/probe_dstats.bend; tr, one run (constraint c
# with every one before it), a line per round. main traces constraint 2
# (angle-lines' Angle, whose rounds grow with its numbers).
# Native: bin/bend proto/probe_dtime.bend -o <out>.
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

def one(+sk: SK.Sketch, +c: Nat) -> String:
  +cs = upto(1n+c, 0n)
  +fs = SV.rfacts(sk, cs)
  +es = SV.ents(sk)
  "  #" ++ Nat.show(c) ++ " facts " ++ Nat.show(len.f(fs)) ++ ": " ++ oshow(DC.dclose(es, fs, SV.eqs_of(sk, cs), DCF.tv(sk), DC.dfuel(es, fs)))

def loop(n: Nat, +sk: SK.Sketch, +c: Nat) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(one(sk, c))
        loop(m, sk, 1n+c)

def ncons(rs: List<&2, SK.Rec>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+ncons(t)

# the run for constraint c, one line per round
def tr.o(o: DC.Out) -> String:
  match o:
    case DC.OStep{+s}:
      "step; " ++ stats.s(s)
    case DC.OFix{+s}:
      "fix"
    case DC.OOne{d}:
      "one"
    case DC.OVoid{g, dr, di}:
      "void"

def trace(fuel: Nat, fo: DC.FO, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +oo: List<&2, Nat>, +ids: List<&2, Nat>) -> IO(Unit):
  match fuel fo:
    case 0n fo:
      IO.pure(Unit, Unit{})
    case 1n+f DC.FO{DC.OStep{+s}, +C}:
      do IO<Unit>:
        IO.print("    " ++ stats.s(s))
        trace(f, DC.fround(es, fs, t, cs, oo, ids, s, C), es, fs, t, cs, oo, ids)
    case 1n+f DC.FO{o, C}:
      IO.print("    end: " ++ tr.o(o))

def tr.go(+sk: SK.Sketch, +c: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP) -> IO(Unit):
  +oo = DC.oids(DC.segids(es), es, cs)
  trace(DC.dfuel(es, fs), DC.FO{DC.OStep{DC.sk0(es, fs, cs)}, DC.kc.of(DC.snodes(oo), es, fs, DCF.tv(sk), DC.Sk.k(DC.sk0(es, fs, cs)))}, es, fs, DCF.tv(sk), cs, oo, DC.segids(es))

def tr(+sk: SK.Sketch, +c: Nat) -> IO(Unit):
  tr.go(sk, c, SV.ents(sk), SV.rfacts(sk, upto(1n+c, 0n)), DC.sp.of(SV.eqs_of(sk, upto(1n+c, 0n)), DC.SP{Nil{}, Nil{}}))

def go(+sk: SK.Sketch) -> IO(Unit):
  tr(sk, 2n)

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    go(PE.sk.of(s))
