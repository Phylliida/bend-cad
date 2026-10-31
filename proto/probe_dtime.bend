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
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../lib/elim.bend as EL
import ../lib/zring.bend as R

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


# Sizes: bits of the numbers
def nmax(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      b
    case 1n+x 0n:
      1n+x
    case 1n+x 1n+y:
      1n+nmax(x, y)

def pbits(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      1n
    case S.XO{q}:
      1n+pbits(q)
    case S.XI{q}:
      1n+pbits(q)

def zbits(z: S.Z) -> Nat:
  match z:
    case S.Z0{}:
      0n
    case S.Zpos{p}:
      pbits(p)
    case S.Zneg{p}:
      pbits(p)

def qbits(q: S.Q) -> Nat:
  match q:
    case S.Q{n, d}:
      Nat.add(zbits(n), pbits(d))

def polybits(p: List<&2, R.ZTerm>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{R.ZTerm{c, m}, t}:
      nmax(zbits(c), polybits(t))

def rowbits(rs: List<&2, EL.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{EL.Row{p, cb, bt, pv}, t}:
      nmax(polybits(p), rowbits(t))

def ptz(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      0n
    case S.XO{q}:
      1n+ptz(q)
    case S.XI{q}:
      0n

def ztz(z: S.Z) -> Nat:
  match z:
    case S.Z0{}:
      999n
    case S.Zpos{p}:
      ptz(p)
    case S.Zneg{p}:
      ptz(p)

def nmin(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      0n
    case 1n+x 0n:
      0n
    case 1n+x 1n+y:
      1n+nmin(x, y)

def polytz(p: List<&2, R.ZTerm>) -> Nat:
  match p:
    case Nil{}:
      999n
    case Con{R.ZTerm{c, m}, t}:
      nmin(ztz(c), polytz(t))

def rows.show(rs: List<&2, EL.Row>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{EL.Row{+p, cb, bt, pv}, t}:
      " " ++ Nat.show(polybits(p)) ++ "/" ++ Nat.show(polytz(p)) ++ rows.show(t)

def labs.show(ms: List<&2, DC.Mem>) -> String:
  match ms:
    case Nil{}:
      ""
    case Con{DC.Mem{a, r, DR.Lab{S.Q{+cn, +cd}, S.Q{sn, sd}}, d}, t}:
      " " ++ Nat.show(zbits(cn)) ++ "/" ++ Nat.show(ztz(cn)) ++ ":" ++ Nat.show(pbits(cd)) ++ "/" ++ Nat.show(ptz(cd)) ++ labs.show(t)

def ebits(e: E.QExpr) -> Nat:
  match e:
    case E.QVar{i}:
      0n
    case E.QCst{q}:
      qbits(q)
    case E.QAdd{a, b}:
      nmax(ebits(a), ebits(b))
    case E.QSub{a, b}:
      nmax(ebits(a), ebits(b))
    case E.QMul{a, b}:
      nmax(ebits(a), ebits(b))
    case E.QNeg{a}:
      ebits(a)

def esize(e: E.QExpr) -> Nat:
  match e:
    case E.QVar{i}:
      1n
    case E.QCst{q}:
      1n
    case E.QAdd{a, b}:
      1n+Nat.add(esize(a), esize(b))
    case E.QSub{a, b}:
      1n+Nat.add(esize(a), esize(b))
    case E.QMul{a, b}:
      1n+Nat.add(esize(a), esize(b))
    case E.QNeg{a}:
      1n+esize(a)

def labbits(ms: List<&2, DC.Mem>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{DC.Mem{a, r, DR.Lab{c, s}, d}, t}:
      nmax(nmax(qbits(c), qbits(s)), labbits(t))

def dbits(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{DC.Mem{a, r, w, +d}, t}:
      nmax(nmax(ebits(SK.VE.x(DR.Jd.x(DR.concl(es, fs, d)))), ebits(SK.VE.y(DR.Jd.x(DR.concl(es, fs, d))))), dbits(t, es, fs))

def dsize(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{DC.Mem{a, r, w, +d}, t}:
      nmax(esize(SK.VE.x(DR.Jd.x(DR.concl(es, fs, d)))), dsize(t, es, fs))

def sizes(+s: DC.Sk, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> String:
  "\n      rows (bits/twos):" ++ rows.show(KS.ks.rows(DC.Sk.k(s))) ++ "\n      label c num:den (bits/twos):" ++ labs.show(DC.Sk.ms(s)) ++ "\n      K rows " ++ Nat.show(rowbits(KS.ks.rows(DC.Sk.k(s)))) ++ " bits, labels " ++ Nat.show(labbits(DC.Sk.ms(s))) ++ " bits, member forms " ++ Nat.show(dbits(DC.Sk.ms(s), es, fs)) ++ " bits, " ++ Nat.show(dsize(DC.Sk.ms(s), es, fs)) ++ " nodes"

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
        IO.print("    " ++ stats.s(s) ++ sizes(s, es, fs))
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
