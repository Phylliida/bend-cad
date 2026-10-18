# Diagnostic (untrusted): one block of the solver's plan, stage by stage.
# Reads ./sketch.in (gui/solve_cli.bend's format) and ./stage.in = "k p j":
# stage k of block j at precision p. k: 0 size/params/equation sizes,
# 1 Newton steps, 2 the inverse at the drawing, 3 the block's outcome,
# 4 J at Newton's end (or the drawing) as dyadics, 5 each equation's owning
# constraint position, the block's variables and parameters. Parameters
# take their drawn values (an approximation of the plan's gc).
# Native: bin/bend proto/probe_block.bend -o proto/probe_block; see
# tools/diag/README.md. Built 2026-10-18 to find sketch(4)'s dependency.
#
# sketch.in, four lines (numbers decimal unless noted):
#   0: variable kinds, space separated: 0 coord, 1 length, 2 param, 3 aux
#   1: entities, comma separated: "id construction kind args", kind 0 point
#      (x y), 1 segment (p q), 2 circle (c r), 3 arc (s e b)
#   2: constraints, comma separated: "id driven kind args", kinds as in
#      spec/sketch.bend's Constraint order (0 Coincident .. 19 Symmetric);
#      values are rationals "n/d" with n, d in binary, n signed
#   3: the drawn geometry, one dyadic "m:e" (= m 2^-e, m signed binary)
#      per variable
# Output lines: ok, red (constraint ids), pins (variables), gc and gr
# (the certified box's centers and radii as dyadics).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../lib/solve.bend as SO
import ../proto/block.bend as B
import ../lib/numer.bend as NU
import ../lib/struct.bend as ST
import ../lib/plan.bend as PL
import ../spec/solve.bend as SV

# Numbers
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

# binary, the leading digit 1
def pos(s: String) -> S.Pos:
  match s:
    case SNil{}:
      S.XH{}
    case SCon{h, t}:
      pos.go(t, S.XH{})

def z.of(neg: Bool, zero: Bool, s: String, t: String) -> S.Z:
  match neg zero:
    case True{} zero:
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
    case Con{m, Con{e, rest}}:
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

def q.of(ps: List<&2, String>) -> S.Q:
  match ps:
    case Con{n, Con{dd, rest}}:
      S.Q{z(n), pos(dd)}
    case _:
      S.Q{S.Z0{}, S.XH{}}

def q(s: String) -> S.Q:
  q.of(String.split(s, '/'))

def qe(s: String) -> E.QExpr:
  E.QCst{q(s)}

def tb(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Char.is_eq(h, '1')

# Variables
# ---------

def vk.of(k: Nat) -> SK.VKind:
  match k:
    case 0n:
      SK.Coord{}
    case 1n+j:
      match j:
        case 0n:
          SK.Length{}
        case 1n+i:
          match i:
            case 0n:
              SK.Param{}
            case 1n+h:
              SK.Aux{}

def vks.add(t: String, acc: List<&2, SK.VKind>) -> List<&2, SK.VKind>:
  match t:
    case SNil{}:
      acc
    case SCon{h, u}:
      Con{vk.of(B.tok.nat(SCon{h, u})), acc}

def vks(ts: List<&2, String>) -> List<&2, SK.VKind>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      vks.add(t, vks(rest))


# Entities
# --------

def geo.of(k: Nat, a: String, b: String, c: String) -> SK.Geo:
  match k:
    case 0n:
      SK.GPoint{B.tok.nat(a), B.tok.nat(b)}
    case 1n+j:
      match j:
        case 0n:
          SK.GSeg{B.tok.nat(a), B.tok.nat(b)}
        case 1n+i:
          match i:
            case 0n:
              SK.GCirc{B.tok.nat(a), B.tok.nat(b)}
            case 1n+h:
              SK.GArc{B.tok.nat(a), B.tok.nat(b), B.tok.nat(c)}

def ent.of(ts: List<&2, String>) -> Maybe<&2, SK.Ent>:
  match ts:
    case Con{i, Con{cn, Con{k, Con{a, Con{b, Con{c, r}}}}}}:
      Some{SK.Ent{B.tok.nat(i), tb(cn), geo.of(B.tok.nat(k), a, b, c)}}
    case Con{i, Con{cn, Con{k, Con{a, Con{b, r}}}}}:
      Some{SK.Ent{B.tok.nat(i), tb(cn), geo.of(B.tok.nat(k), a, b, "0")}}
    case _:
      None{}

def ents.add(m: Maybe<&2, SK.Ent>, acc: List<&2, SK.Ent>) -> List<&2, SK.Ent>:
  match m:
    case None{}:
      acc
    case Some{e}:
      Con{e, acc}

def ents(ls: List<&2, String>) -> List<&2, SK.Ent>:
  match ls:
    case Nil{}:
      []
    case Con{l, rest}:
      ents.add(ent.of(B.toks(l)), ents(rest))

# Constraints
# -----------

def mk0(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Coincident{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk1(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Horizontal{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk2(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Vertical{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk3(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Concentric{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk4(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.EqualRadius{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk5(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Fix{B.tok.nat(a0), q(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk6(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, r}}}:
      SK.Distance{B.tok.nat(a0), B.tok.nat(a1), qe(a2)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk7(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, r}}}:
      SK.HDistance{B.tok.nat(a0), B.tok.nat(a1), qe(a2)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk8(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, r}}}:
      SK.VDistance{B.tok.nat(a0), B.tok.nat(a1), qe(a2)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk9(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Radius{B.tok.nat(a0), qe(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk10(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Diameter{B.tok.nat(a0), qe(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk11(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, r}}}}}:
      SK.LineDistance{B.tok.nat(a0), B.tok.nat(a1), tb(a2), qe(a3), B.tok.nat(a4)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk12(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, r}}}}}}:
      SK.Angle{B.tok.nat(a0), tb(a1), B.tok.nat(a2), tb(a3), qe(a4), qe(a5)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk13(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.EqualLength{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk14(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Perpendicular{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk15(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Parallel{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk16(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.OnLine{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk17(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.OnCircle{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk18(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, r}}:
      SK.Midpoint{B.tok.nat(a0), B.tok.nat(a1)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def mk19(ts: List<&2, String>) -> SK.Constraint:
  match ts:
    case Con{a0, Con{a1, Con{a2, r}}}:
      SK.Symmetric{B.tok.nat(a0), B.tok.nat(a1), B.tok.nat(a2)}
    case _:
      SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def ck20(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  SK.Fix{0n, S.Q{S.Z0{}, S.XH{}}}

def ck19(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk19(ts)
    case 1n+j:
      ck20(j, ts)

def ck18(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk18(ts)
    case 1n+j:
      ck19(j, ts)

def ck17(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk17(ts)
    case 1n+j:
      ck18(j, ts)

def ck16(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk16(ts)
    case 1n+j:
      ck17(j, ts)

def ck15(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk15(ts)
    case 1n+j:
      ck16(j, ts)

def ck14(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk14(ts)
    case 1n+j:
      ck15(j, ts)

def ck13(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk13(ts)
    case 1n+j:
      ck14(j, ts)

def ck12(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk12(ts)
    case 1n+j:
      ck13(j, ts)

def ck11(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk11(ts)
    case 1n+j:
      ck12(j, ts)

def ck10(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk10(ts)
    case 1n+j:
      ck11(j, ts)

def ck9(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk9(ts)
    case 1n+j:
      ck10(j, ts)

def ck8(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk8(ts)
    case 1n+j:
      ck9(j, ts)

def ck7(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk7(ts)
    case 1n+j:
      ck8(j, ts)

def ck6(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk6(ts)
    case 1n+j:
      ck7(j, ts)

def ck5(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk5(ts)
    case 1n+j:
      ck6(j, ts)

def ck4(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk4(ts)
    case 1n+j:
      ck5(j, ts)

def ck3(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk3(ts)
    case 1n+j:
      ck4(j, ts)

def ck2(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk2(ts)
    case 1n+j:
      ck3(j, ts)

def ck1(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk1(ts)
    case 1n+j:
      ck2(j, ts)

def ck0(k: Nat, ts: List<&2, String>) -> SK.Constraint:
  match k:
    case 0n:
      mk0(ts)
    case 1n+j:
      ck1(j, ts)

def rec.of(ts: List<&2, String>) -> Maybe<&2, SK.Rec>:
  match ts:
    case Con{i, Con{dr, Con{k, rest}}}:
      Some{SK.Rec{B.tok.nat(i), tb(dr), ck0(B.tok.nat(k), rest)}}
    case _:
      None{}

def recs.add(m: Maybe<&2, SK.Rec>, acc: List<&2, SK.Rec>) -> List<&2, SK.Rec>:
  match m:
    case None{}:
      acc
    case Some{e}:
      Con{e, acc}

def recs(ls: List<&2, String>) -> List<&2, SK.Rec>:
  match ls:
    case Nil{}:
      []
    case Con{l, rest}:
      recs.add(rec.of(B.toks(l)), recs(rest))

# Output
# ------

def posbin(p: S.Pos) -> String:
  match p:
    case S.XH{}:
      "1"
    case S.XO{t}:
      posbin(t) ++ "0"
    case S.XI{t}:
      posbin(t) ++ "1"

def zbin(x: S.Z) -> String:
  match x:
    case S.Z0{}:
      "0"
    case S.Zpos{p}:
      posbin(p)
    case S.Zneg{p}:
      "-" ++ posbin(p)

def dshow(x: S.D) -> String:
  match x:
    case S.D{m, e}:
      zbin(m) ++ ":" ++ Nat.show(e)

def dsshow(xs: List<&2, S.D>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ dshow(h) ++ dsshow(t)

def nshow(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ Nat.show(h) ++ nshow(t)

def show(o: SO.Out) -> String:
  match o:
    case SO.Out{ok, red, why, pins, gc, gr, plan}:
      "ok " ++ Bool.show(ok) ++ "\nred" ++ nshow(red) ++ "\npins" ++ nshow(pins) ++ "\ngc" ++ dsshow(gc) ++ "\ngr" ++ dsshow(gr)

# The probe
# ---------

def line(ls: List<&2, String>, k: Nat) -> String:
  match ls k:
    case Nil{} k:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      line(t, j)

def sk.of(+s: String) -> SK.Sketch:
  +ls = String.split(s, '\n')
  SK.Sketch{vks(B.toks(line(ls, 0n))), ents(String.split(line(ls, 1n), ',')), recs(String.split(line(ls, 2n), ','))}

def g0.of(+s: String) -> List<&2, S.D>:
  ds(B.toks(line(String.split(s, '\n'), 3n)))

def nlen(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+nlen(t)

def bsizes(bs: List<&2, ST.SkB>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{ST.SkB{eqs, vars, pars}, t}:
      " " ++ Nat.show(nlen(eqs)) ++ "x" ++ Nat.show(nlen(vars)) ++ "/" ++ Nat.show(nlen(pars)) ++ bsizes(t)

def skshow(s: ST.Skel) -> String:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      "np " ++ Nat.show(np) ++ " blocks (eqs x vars / pars)" ++ bsizes(bs)

def prshow(m: NU.PR) -> String:
  match m:
    case NU.POk{x}:
      "POk"
    case NU.PRetry{}:
      "PRetry"
    case NU.PStop{}:
      "PStop"

# the first block of the plan, its inputs as pblocks builds them
def skel.vp(s: ST.Skel) -> List<&2, Nat>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      vp

def skel.ep(s: ST.Skel) -> List<&2, Nat>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      ep

def skel.np(s: ST.Skel) -> Nat:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      np

def b1.n(bs: List<&2, ST.SkB>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{ST.SkB{es, vs, pars}, t}:
      nlen(es)

def b1.pars(bs: List<&2, ST.SkB>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{ST.SkB{es, vs, pars}, t}:
      pars

def skel.bs(s: ST.Skel) -> List<&2, ST.SkB>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      bs

def g0b(+s: String) -> List<&2, S.D>:
  NU.dpick(g0.of(s), skel.vp(SO.skel_of(sk.of(s))))


def nth.b(bs: List<&2, ST.SkB>, j: Nat) -> List<&2, ST.SkB>:
  match bs j:
    case Nil{} j:
      Nil{}
    case bs 0n:
      bs
    case Con{b, t} 1n+i:
      nth.b(t, i)

# equations before block j
def before(bs: List<&2, ST.SkB>, j: Nat) -> Nat:
  match bs j:
    case Nil{} j:
      0n
    case bs 0n:
      0n
    case Con{ST.SkB{es, vs, pars}, t} 1n+i:
      Nat.add(nlen(es), before(t, i))

def bj(+s: String, +j: Nat) -> List<&2, ST.SkB>:
  nth.b(skel.bs(SO.skel_of(sk.of(s))), j)

def j.n(+s: String, +j: Nat) -> Nat:
  b1.n(bj(s, j))

def j.o(+s: String, +j: Nat) -> Nat:
  Nat.add(skel.np(SO.skel_of(sk.of(s))), before(skel.bs(SO.skel_of(sk.of(s))), j))

def j.pars(+s: String, +j: Nat) -> List<&2, Nat>:
  b1.pars(bj(s, j))

def j.eqs(+s: String, +j: Nat) -> List<&2, E.QExpr>:
  PL.renames(j.o(s, j), j.n(s, j), j.pars(s, j), PL.takeq(j.n(s, j), PL.dropq(before(skel.bs(SO.skel_of(sk.of(s))), j), PL.reorder(skel.vp(SO.skel_of(sk.of(s))), SO.kept(sk.of(s)), skel.ep(SO.skel_of(sk.of(s)))))))

def j.pc(+s: String, +j: Nat) -> List<&2, S.D>:
  NU.dpick(g0b(s), j.pars(s, j))

def j.y0(+s: String, +j: Nat) -> List<&2, S.D>:
  NU.dtake(j.n(s, j), NU.ddrop(j.o(s, j), g0b(s)))

def ncount(k: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +p: Nat, st: NU.NS, +c: Nat) -> String:
  match k st:
    case k NU.NSing{}:
      "singular or diverging at step " ++ Nat.show(c)
    case k NU.NDone{y}:
      "settled at step " ++ Nat.show(c)
    case 0n NU.NMore{y}:
      "not settled after " ++ Nat.show(c)
    case 1n+j NU.NMore{+y}:
      ncount(j, eqs, n, pc, p, NU.classify(y, p, NU.nstep(eqs, n, pc, p, y)), 1n+c)

def mshow(m: Maybe<&2, List<&2, S.D>>) -> String:
  match m:
    case None{}:
      "None"
    case Some{y}:
      "Some"

def mmshow(m: Maybe<&2, List<&2, List<&2, S.D>>>) -> String:
  match m:
    case None{}:
      "None"
    case Some{y}:
      "Some"

def brshow(m: NU.BR) -> String:
  match m:
    case NU.BOk{c}:
      "BOk"
    case NU.BRetry{}:
      "BRetry (no radius)"
    case NU.BStop{}:
      "BStop (Newton or inverse)"

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

def nmax(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b:
      b
    case 1n+i 0n:
      1n+i
    case 1n+i 1n+j:
      1n+nmax(i, j)


def dbits(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{S.D{m, e}, t}:
      nmax(zbits(m), dbits(t))

def dexp(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{S.D{m, e}, t}:
      nmax(e, dexp(t))

# (largest mantissa in bits, largest exponent)
def dstat(+xs: List<&2, S.D>) -> String:
  "bits " ++ Nat.show(dbits(xs)) ++ " exp " ++ Nat.show(dexp(xs))

def dflat(a: List<&2, List<&2, S.D>>) -> List<&2, S.D>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      NU.dapp(r, dflat(t))

def qsize(e: E.QExpr) -> Nat:
  match e:
    case E.QVar{i}:
      1n
    case E.QCst{q}:
      1n
    case E.QAdd{a, b}:
      1n+Nat.add(qsize(a), qsize(b))
    case E.QSub{a, b}:
      1n+Nat.add(qsize(a), qsize(b))
    case E.QMul{a, b}:
      1n+Nat.add(qsize(a), qsize(b))
    case E.QNeg{a}:
      1n+qsize(a)

def qsizes(es: List<&2, E.QExpr>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      " " ++ Nat.show(qsize(e)) ++ qsizes(t)


def dline(xs: List<&2, S.D>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " " ++ dshow(x) ++ dline(t)

def mlines(a: List<&2, List<&2, S.D>>) -> String:
  match a:
    case Nil{}:
      ""
    case Con{r, t}:
      "\nrow" ++ dline(r) ++ mlines(t)

def ystate(m: Maybe<&2, List<&2, S.D>>, +y0: List<&2, S.D>) -> List<&2, S.D>:
  match m:
    case None{}:
      y0
    case Some{y}:
      y

# stage k for block j at precision p: 0 info, 1 Newton, 2 inverse at the
# drawing, 3 the block, 4 J at Newton's end (or the drawing), as dyadics
def kv(+s: String, +j: Nat, q: Nat) -> String:
  match q:
    case 0n:
      ""
    case 1n++r:
      kv(s, j, r) ++ " " ++ Nat.show(SV.nth(SV.owners(sk.of(s)), SV.nth(SO.good_of(sk.of(s)), SV.nth(skel.ep(SO.skel_of(sk.of(s))), Nat.add(before(skel.bs(SO.skel_of(sk.of(s))), j), r)))))

def vv(+s: String, +j: Nat, q: Nat) -> String:
  match q:
    case 0n:
      ""
    case 1n++r:
      vv(s, j, r) ++ " " ++ Nat.show(SV.nth(skel.vp(SO.skel_of(sk.of(s))), Nat.add(j.o(s, j), r)))

def pv(+s: String, ps: List<&2, Nat>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ Nat.show(SV.nth(skel.vp(SO.skel_of(sk.of(s))), h)) ++ pv(s, t)

def jpick4(k: Nat, +j: Nat, +p: Nat, +s: String) -> String:
  match k:
    case 0n:
      "jac" ++ mlines(NU.jac(j.eqs(s, j), j.n(s, j), NU.dapp(ystate(NU.newton(40n, j.eqs(s, j), j.n(s, j), j.pc(s, j), p, NU.NMore{j.y0(s, j)}), j.y0(s, j)), j.pc(s, j))))
    case 1n+a:
      "owners" ++ kv(s, j, j.n(s, j)) ++ "\nvars" ++ vv(s, j, j.n(s, j)) ++ "\npars" ++ pv(s, j.pars(s, j))

def jpick3(k: Nat, +j: Nat, +p: Nat, +s: String) -> String:
  match k:
    case 0n:
      "block: " ++ brshow(NU.block(j.eqs(s, j), j.n(s, j), j.pc(s, j), NU.dzeros(nlen(j.pars(s, j))), j.y0(s, j), p))
    case 1n+a:
      jpick4(a, j, p, s)

def jpick2(k: Nat, +j: Nat, +p: Nat, +s: String) -> String:
  match k:
    case 0n:
      "inverse at drawing: " ++ mmshow(NU.dinverse(j.n(s, j), NU.wbits(p), NU.jac(j.eqs(s, j), j.n(s, j), NU.dapp(j.y0(s, j), j.pc(s, j)))))
    case 1n+a:
      jpick3(a, j, p, s)

def jpick1(k: Nat, +j: Nat, +p: Nat, +s: String) -> String:
  match k:
    case 0n:
      "newton: " ++ ncount(40n, j.eqs(s, j), j.n(s, j), j.pc(s, j), p, NU.NMore{j.y0(s, j)}, 0n)
    case 1n+a:
      jpick2(a, j, p, s)

def jpick(k: Nat, +j: Nat, +p: Nat, +s: String) -> String:
  match k:
    case 0n:
      "block " ++ Nat.show(j) ++ ": n " ++ Nat.show(j.n(s, j)) ++ " o " ++ Nat.show(j.o(s, j)) ++ " pars" ++ nshow(j.pars(s, j)) ++ " eq sizes" ++ qsizes(j.eqs(s, j))
    case 1n+a:
      jpick1(a, j, p, s)

def arg(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} k:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      arg(t, j)

def go(+s: String, +a: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(jpick(arg(B.nats(B.toks(a)), 0n), arg(B.nats(B.toks(a)), 2n), arg(B.nats(B.toks(a)), 1n), s))

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("sketch.in")
    a : String <- B.slurp("stage.in")
    go(s, a)
