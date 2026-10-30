# Runs the direction closure (lib/dclose.bend) on small sketches and prints
# what it finds. Native: bin/bend proto/dclose_run.bend -o <out>; <out> --threads 1

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ../spec/_draft13b.bend as SV
import ../lib/elim.bend as EL
import ../lib/kspace.bend as KS
import ../lib/dclose.bend as DC

def es() -> List<&2, SK.Ent>:
  [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}, SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}, SK.Ent{3n, False{}, SK.GPoint{6n, 7n}}, SK.Ent{10n, False{}, SK.GSeg{0n, 1n}}, SK.Ent{11n, False{}, SK.GSeg{1n, 2n}}, SK.Ent{12n, False{}, SK.GSeg{2n, 3n}}]

def coords() -> List<&2, SK.VKind>:
  [SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}]

def skc(cs: List<&2, SK.Rec>) -> SK.Sketch:
  SK.Sketch{coords(), es(), cs}

def shown(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      Nat.show(x)
    case Con{x, t}:
      Nat.show(x) ++ " " ++ shown(t)

def node(n: DR.Node) -> String:
  match n:
    case DR.NFrame{}:
      "F"
    case DR.NSeg{s}:
      Nat.show(s)

def mems(ms: List<&2, DC.Mem>) -> String:
  match ms:
    case Nil{}:
      ""
    case Con{DC.Mem{a, r, w, d}, t}:
      " " ++ node(a) ++ "->" ++ node(r) ++ mems(t)

def llen(ls: List<&2, DC.Link>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+llen(t)

def showo(o: DC.Out) -> String:
  match o:
    case DC.OStep{s}:
      "out of fuel"
    case DC.OFix{DC.Sk{k, ms, ls}}:
      "closed: K rank " ++ Nat.show(EL.rlen(KS.ks.rows(k))) ++ ", forest" ++ mems(ms) ++ ", links " ++ Nat.show(llen(ls))
    case DC.OOne{d}:
      "explodes: 1 in K"
    case DC.OVoid{sg, dr, di}:
      "explodes: open segment " ++ Nat.show(sg) ++ " has its direction in K squared"

def run(+cs: List<&2, SK.Rec>, +own: List<&2, Nat>, +c: Nat) -> String:
  showo(DC.dclose(SV.ents(skc(cs)), SV.rfacts(skc(cs), own), SV.ctx(skc(cs), Nil{}, c), 8n, DC.dfuel(SV.ents(skc(cs)), SV.rfacts(skc(cs), own)))) ++ " (fuel " ++ Nat.show(DC.dfuel(SV.ents(skc(cs)), SV.rfacts(skc(cs), own))) ++ ")"

def fes(fs: List<&2, DR.Fact>) -> List<&2, E.QExpr>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{DR.Fact{e, nd, ds}, t}:
      Con{e, fes(t)}

# facts from the constraints own, the context from those in cx
def run2(+cs: List<&2, SK.Rec>, +own: List<&2, Nat>, +cx: List<&2, Nat>) -> String:
  showo(DC.dclose(SV.ents(skc(cs)), SV.rfacts(skc(cs), own), fes(SV.rfacts(skc(cs), cx)), 8n, DC.dfuel(SV.ents(skc(cs)), SV.rfacts(skc(cs), own)))) ++ " (fuel " ++ Nat.show(DC.dfuel(SV.ents(skc(cs)), SV.rfacts(skc(cs), own))) ++ ")"

def main() -> String:
  "parallel and perpendicular on one pair (sketch 8's shape): " ++ run([SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Perpendicular{10n, 11n}}], [1n, 0n], 1n) ++ "\n" ++
  "parallel alone: " ++ run([SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}], [0n], 0n) ++ "\n" ++
  "a chain 10 || 11 || 12: " ++ run([SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Parallel{11n, 12n}}], [1n, 0n], 1n) ++ "\n" ++
  "10 || 11, 11 _|_ 12, 10 || 12: " ++ run([SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Perpendicular{11n, 12n}}, SK.Rec{2n, False{}, SK.Parallel{10n, 12n}}], [2n, 1n, 0n], 2n) ++ "\n" ++
  "nothing: " ++ run(Nil{}, Nil{}, 0n) ++ "\n" ++
  "horizontal 10, 10 || 11: " ++ run([SK.Rec{0n, False{}, SK.Horizontal{0n, 1n}}, SK.Rec{1n, False{}, SK.Parallel{10n, 11n}}], [1n, 0n], 1n) ++ "\n" ++
  "coincident ends of 10 (a fact), 10 || 11: " ++ run([SK.Rec{0n, False{}, SK.Coincident{0n, 1n}}, SK.Rec{1n, False{}, SK.Parallel{10n, 11n}}], [1n, 0n], 1n) ++ "\n" ++
  "10 collapsed only in the context, 10 || 11: " ++ run2([SK.Rec{0n, False{}, SK.Coincident{0n, 1n}}, SK.Rec{1n, False{}, SK.Parallel{10n, 11n}}], [1n], [1n, 0n]) ++ "\n" ++
  "10 collapsed only in the context, horizontal 11, 10 || 11: " ++ run2([SK.Rec{0n, False{}, SK.Coincident{0n, 1n}}, SK.Rec{1n, False{}, SK.Horizontal{1n, 2n}}, SK.Rec{2n, False{}, SK.Parallel{10n, 11n}}], [2n, 1n], [2n, 1n, 0n]) ++ "\n" ++
  "10 collapsed only in the context, 10 || 11, 10 _|_ 11: " ++ run2([SK.Rec{0n, False{}, SK.Coincident{0n, 1n}}, SK.Rec{1n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{2n, False{}, SK.Perpendicular{10n, 11n}}], [2n, 1n], [2n, 1n, 0n]) ++ "\n" ++
  "horizontal 10, vertical 11, 10 || 11: " ++ run([SK.Rec{0n, False{}, SK.Horizontal{0n, 1n}}, SK.Rec{1n, False{}, SK.Vertical{1n, 2n}}, SK.Rec{2n, False{}, SK.Parallel{10n, 11n}}], [2n, 1n, 0n], 2n) ++ "\n"
