# bend-cad: a covered, well-formed sketch's equations use only its
# variables. For the solver's totality (ROADMAP: solve_total). Proofs only.
#
# Sketch.within(sk, n) (spec/box.bend) bounds the variables a sketch
# names: each entity's own and each constraint's dimensions'. The exact
# system's equations (spec/sketch.bend: Constraint.eqs) are built from
# those, through the entities the constraints reference; in a well-formed
# sketch (lib/wfdec.bend: wf_dec) every reference names an entity of the
# right kind, so every variable of every equation is below n, and the
# structure stage's adjacency lists are too (lib/dfspf.bend: adjb).

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./wfdec.bend as WF
import ./listpf.bend as L
import ./dfspf.bend as D

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Booleans
# --------

def and_l(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      {==}

def and_r(a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      absurd({b == True{} : Bool}, KA.ft(h))
    case True{}:
      h

def and_i(a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      absurd({False{} == True{} : Bool}, KA.ft(ha))
    case True{}:
      hb

def lt_bx(a: Nat, b: Nat) -> {BX.lt(a, b) == SV.lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      lt_bx(i, j)

# Expressions to adjacency lists
# ------------------------------

def ev_var.go(+v: Nat, +acc: List<&2, Nat>, +n: Nat, c: Bool, +hv: {SV.lt(v, n) == True{} : Bool}, +ha: {SV.below(acc, n) == True{} : Bool}) -> {SV.below(ST.addv.go(c, v, acc), n) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      L.band_i(SV.lt(v, n), SV.below(acc, n), hv, ha)

# the variables evars lists for e (below n) and acc (below n) are below n
def ev_below(e: E.QExpr, +acc: List<&2, Nat>, +n: Nat, +hw: {BX.QExpr.within(e, n) == True{} : Bool}, +ha: {SV.below(acc, n) == True{} : Bool}) -> {SV.below(ST.evars(e, acc), n) == True{} : Bool}:
  match e:
    case E.QVar{+v}:
      ev_var.go(v, acc, n, ST.mem(v, acc), %lt_bx(v, n) : {_ == True{} : Bool}
        hw, ha)
    case E.QCst{q}:
      ha
    case E.QAdd{+a, +b}:
      ev_below(b, ST.evars(a, acc), n, and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ev_below(a, acc, n, and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ha))
    case E.QSub{+a, +b}:
      ev_below(b, ST.evars(a, acc), n, and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ev_below(a, acc, n, and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ha))
    case E.QMul{+a, +b}:
      ev_below(b, ST.evars(a, acc), n, and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ev_below(a, acc, n, and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), hw), ha))
    case E.QNeg{+a}:
      ev_below(a, acc, n, hw, ha)

def rev_below(xs: List<&2, Nat>, +acc: List<&2, Nat>, +n: Nat, +h: {SV.below(xs, n) == True{} : Bool}, +ha: {SV.below(acc, n) == True{} : Bool}) -> {SV.below(ST.rev.go(xs, acc), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+x, +t}:
      rev_below(t, Con{x, acc}, n, L.band_r(SV.lt(x, n), SV.below(t, n), h), L.band_i(SV.lt(x, n), SV.below(acc, n), L.band_l(SV.lt(x, n), SV.below(t, n), h), ha))

# every equation of es is within n
def ewithin(es: List<&2, E.QExpr>, +n: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(BX.QExpr.within(e, n), ewithin(t, n))

def adjb_of(es: List<&2, E.QExpr>, +n: Nat, +h: {ewithin(es, n) == True{} : Bool}) -> {D.adjb(ST.adj(es), n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.band_i(SV.below(ST.rev(ST.evars(e, Nil{})), n), D.adjb(ST.adj(t), n), rev_below(ST.evars(e, Nil{}), Nil{}, n, ev_below(e, Nil{}, n, and_l(BX.QExpr.within(e, n), ewithin(t, n), h), {==}), {==}), adjb_of(t, n, and_r(BX.QExpr.within(e, n), ewithin(t, n), h)))

def ewithin_cat(a: List<&2, E.QExpr>, +b: List<&2, E.QExpr>, +n: Nat, +ha: {ewithin(a, n) == True{} : Bool}, +hb: {ewithin(b, n) == True{} : Bool}) -> {ewithin(SK.cat(a, b), n) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+e, +t}:
      and_i(BX.QExpr.within(e, n), ewithin(SK.cat(t, b), n), and_l(BX.QExpr.within(e, n), ewithin(t, n), ha), ewithin_cat(t, b, n, and_r(BX.QExpr.within(e, n), ewithin(t, n), ha), hb))

# Entities
# --------

def ptin(+p: SK.Pt, +n: Nat) -> Bool:
  Bool.and(BX.lt(SK.Pt.x(p), n), BX.lt(SK.Pt.y(p), n))

# what Sketch.within says of a found entity's variables
def geow(m: Maybe<&2, SK.Geo>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{SK.GPoint{x, y}}:
      Bool.and(BX.lt(x, n), BX.lt(y, n))
    case Some{SK.GSeg{p, q}}:
      True{}
    case Some{SK.GCirc{c, r}}:
      BX.lt(r, n)
    case Some{SK.GArc{s, f, b}}:
      BX.lt(b, n)

# what wf_dec says of a found entity's references
def georef(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{SK.GPoint{x, y}}:
      True{}
    case Some{SK.GSeg{+p, +q}}:
      KA.band(WF.ispt(es, p), WF.ispt(es, q))
    case Some{SK.GCirc{+c, r}}:
      WF.ispt(es, c)
    case Some{SK.GArc{+s, +f, b}}:
      KA.band(WF.ispt(es, s), WF.ispt(es, f))

def gw(+eid: Nat, +cst: Bool, g: SK.Geo, +n: Nat, +h: {BX.Ent.within(SK.Ent{eid, cst, g}, n) == True{} : Bool}) -> {geow(Some{g}, n) == True{} : Bool}:
  match g:
    case SK.GPoint{x, y}:
      h
    case SK.GSeg{p, q}:
      {==}
    case SK.GCirc{c, r}:
      h
    case SK.GArc{s, f, b}:
      h

def gr(+es: List<&2, SK.Ent>, +eid: Nat, +cst: Bool, g: SK.Geo, +h: {WF.ent(es, SK.Ent{eid, cst, g}) == True{} : Bool}) -> {georef(es, Some{g}) == True{} : Bool}:
  match g:
    case SK.GPoint{x, y}:
      {==}
    case SK.GSeg{p, q}:
      h
    case SK.GCirc{c, r}:
      h
    case SK.GArc{s, f, b}:
      h

def pick_w(b: Bool, +g: SK.Geo, +rest: Maybe<&2, SK.Geo>, +n: Nat, +hg: {geow(Some{g}, n) == True{} : Bool}, +hr: {geow(rest, n) == True{} : Bool}) -> {geow(SK.find.pick(b, g, rest), n) == True{} : Bool}:
  match b:
    case True{}:
      hg
    case False{}:
      hr

def pick_r(+es: List<&2, SK.Ent>, b: Bool, +g: SK.Geo, +rest: Maybe<&2, SK.Geo>, +hg: {georef(es, Some{g}) == True{} : Bool}, +hr: {georef(es, rest) == True{} : Bool}) -> {georef(es, SK.find.pick(b, g, rest)) == True{} : Bool}:
  match b:
    case True{}:
      hg
    case False{}:
      hr

def find_w(+a: Nat, xs: List<&2, SK.Ent>, +n: Nat, +hw: {BX.Sketch.within.ents(xs, n) == True{} : Bool}) -> {geow(SK.find(a, xs), n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{SK.Ent{+eid, +cst, +g}, +t}:
      pick_w(Nat.is_eq(eid, a), g, SK.find(a, t), n, gw(eid, cst, g, n, and_l(BX.Ent.within(SK.Ent{eid, cst, g}, n), BX.Sketch.within.ents(t, n), hw)), find_w(a, t, n, and_r(BX.Ent.within(SK.Ent{eid, cst, g}, n), BX.Sketch.within.ents(t, n), hw)))

def find_r(+es: List<&2, SK.Ent>, +a: Nat, xs: List<&2, SK.Ent>, +he: {WF.ents(es, xs) == True{} : Bool}) -> {georef(es, SK.find(a, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{SK.Ent{+eid, +cst, +g}, +t}:
      pick_r(es, Nat.is_eq(eid, a), g, SK.find(a, t), gr(es, eid, cst, g, KA.band_l(WF.ent(es, SK.Ent{eid, cst, g}), WF.ents(es, t), he)), find_r(es, a, t, KA.band_r(WF.ent(es, SK.Ent{eid, cst, g}), WF.ents(es, t), he)))

def ptok.go(m: Maybe<&2, SK.Geo>, +n: Nat, +hp: {SK.is_pt(m) == True{} : Bool}, +hg: {geow(m, n) == True{} : Bool}) -> {ptin(SK.pt.of(m), n) == True{} : Bool}:
  match m:
    case None{}:
      absurd({ptin(SK.Pt{0n, 0n}, n) == True{} : Bool}, KA.ft(hp))
    case Some{SK.GPoint{x, y}}:
      hg
    case Some{SK.GSeg{p, q}}:
      absurd({ptin(SK.Pt{0n, 0n}, n) == True{} : Bool}, KA.ft(hp))
    case Some{SK.GCirc{c, r}}:
      absurd({ptin(SK.Pt{0n, 0n}, n) == True{} : Bool}, KA.ft(hp))
    case Some{SK.GArc{s, f, b}}:
      absurd({ptin(SK.Pt{0n, 0n}, n) == True{} : Bool}, KA.ft(hp))

# a referenced point's coordinates are within n
def ptok(+es: List<&2, SK.Ent>, +a: Nat, +n: Nat, +hp: {WF.ispt(es, a) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}) -> {ptin(SK.pt(es, a), n) == True{} : Bool}:
  ptok.go(SK.find(a, es), n, hp, find_w(a, es, n, hw))

def segok.go(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>, +n: Nat, +hs: {SK.is_seg(m) == True{} : Bool}, +hr: {georef(es, m) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}) -> {Bool.and(ptin(SK.Seg.p(SK.seg.of(es, m)), n), ptin(SK.Seg.q(SK.seg.of(es, m)), n)) == True{} : Bool}:
  match m:
    case None{}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), ptin(SK.Pt{0n, 0n}, n)) == True{} : Bool}, KA.ft(hs))
    case Some{SK.GPoint{x, y}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), ptin(SK.Pt{0n, 0n}, n)) == True{} : Bool}, KA.ft(hs))
    case Some{SK.GSeg{+p, +q}}:
      and_i(ptin(SK.pt(es, p), n), ptin(SK.pt(es, q), n), ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.ispt(es, q), hr), hw), ptok(es, q, n, KA.band_r(WF.ispt(es, p), WF.ispt(es, q), hr), hw))
    case Some{SK.GCirc{c, r}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), ptin(SK.Pt{0n, 0n}, n)) == True{} : Bool}, KA.ft(hs))
    case Some{SK.GArc{s, f, b}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), ptin(SK.Pt{0n, 0n}, n)) == True{} : Bool}, KA.ft(hs))

# a referenced segment's ends are within n
def segok(+es: List<&2, SK.Ent>, +a: Nat, +n: Nat, +hs: {WF.isseg(es, a) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}, +he: {WF.ents(es, es) == True{} : Bool}) -> {Bool.and(ptin(SK.Seg.p(SK.seg(es, a)), n), ptin(SK.Seg.q(SK.seg(es, a)), n)) == True{} : Bool}:
  segok.go(es, SK.find(a, es), n, hs, find_r(es, a, es, he), hw)

def circok.go(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>, +n: Nat, +hc: {SK.is_circ(m) == True{} : Bool}, +hr: {georef(es, m) == True{} : Bool}, +hg: {geow(m, n) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}) -> {Bool.and(ptin(SK.Circ.c(SK.circ.of(es, m)), n), BX.lt(SK.Circ.r(SK.circ.of(es, m)), n)) == True{} : Bool}:
  match m:
    case None{}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), BX.lt(0n, n)) == True{} : Bool}, KA.ft(hc))
    case Some{SK.GPoint{x, y}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), BX.lt(0n, n)) == True{} : Bool}, KA.ft(hc))
    case Some{SK.GSeg{p, q}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), BX.lt(0n, n)) == True{} : Bool}, KA.ft(hc))
    case Some{SK.GCirc{+c, +r}}:
      and_i(ptin(SK.pt(es, c), n), BX.lt(r, n), ptok(es, c, n, hr, hw), hg)
    case Some{SK.GArc{s, f, b}}:
      absurd({Bool.and(ptin(SK.Pt{0n, 0n}, n), BX.lt(0n, n)) == True{} : Bool}, KA.ft(hc))

# a referenced circle's center and radius are within n
def circok(+es: List<&2, SK.Ent>, +c: Nat, +n: Nat, +hc: {WF.iscirc(es, c) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}, +he: {WF.ents(es, es) == True{} : Bool}) -> {Bool.and(ptin(SK.Circ.c(SK.circ(es, c)), n), BX.lt(SK.Circ.r(SK.circ(es, c)), n)) == True{} : Bool}:
  circok.go(es, SK.find(c, es), n, hc, find_r(es, c, es, he), find_w(c, es, n, hw), hw)

def dsegok(+es: List<&2, SK.Ent>, +a: Nat, rev: Bool, +n: Nat, +h: {Bool.and(ptin(SK.Seg.p(SK.seg(es, a)), n), ptin(SK.Seg.q(SK.seg(es, a)), n)) == True{} : Bool}) -> {Bool.and(ptin(SK.Seg.p(SK.dseg(es, a, rev)), n), ptin(SK.Seg.q(SK.dseg(es, a, rev)), n)) == True{} : Bool}:
  match rev:
    case False{}:
      h
    case True{}:
      and_i(ptin(SK.Seg.q(SK.seg(es, a)), n), ptin(SK.Seg.p(SK.seg(es, a)), n), and_r(ptin(SK.Seg.p(SK.seg(es, a)), n), ptin(SK.Seg.q(SK.seg(es, a)), n), h), and_l(ptin(SK.Seg.p(SK.seg(es, a)), n), ptin(SK.Seg.q(SK.seg(es, a)), n), h))

# Expression builders
# -------------------

def w(+e: E.QExpr, +n: Nat) -> Bool:
  BX.QExpr.within(e, n)

def vw(+v: SK.VE, +n: Nat) -> Bool:
  Bool.and(w(SK.VE.x(v), n), w(SK.VE.y(v), n))

def vx(+v: SK.VE, +n: Nat, +h: {vw(v, n) == True{} : Bool}) -> {w(SK.VE.x(v), n) == True{} : Bool}:
  and_l(w(SK.VE.x(v), n), w(SK.VE.y(v), n), h)

def vy(+v: SK.VE, +n: Nat, +h: {vw(v, n) == True{} : Bool}) -> {w(SK.VE.y(v), n) == True{} : Bool}:
  and_r(w(SK.VE.x(v), n), w(SK.VE.y(v), n), h)

# within(e1 op e2)
def w2(+a: E.QExpr, +b: E.QExpr, +n: Nat, +ha: {w(a, n) == True{} : Bool}, +hb: {w(b, n) == True{} : Bool}) -> {Bool.and(w(a, n), w(b, n)) == True{} : Bool}:
  and_i(w(a, n), w(b, n), ha, hb)

def vw_pt(p: SK.Pt, +n: Nat, +h: {ptin(p, n) == True{} : Bool}) -> {vw(SK.Pt.ve(p), n) == True{} : Bool}:
  match p:
    case SK.Pt{x, y}:
      h

def vw_sub(+a: SK.VE, +b: SK.VE, +n: Nat, +ha: {vw(a, n) == True{} : Bool}, +hb: {vw(b, n) == True{} : Bool}) -> {vw(SK.VE.sub(a, b), n) == True{} : Bool}:
  and_i(w(E.QSub{SK.VE.x(a), SK.VE.x(b)}, n), w(E.QSub{SK.VE.y(a), SK.VE.y(b)}, n), w2(SK.VE.x(a), SK.VE.x(b), n, vx(a, n, ha), vx(b, n, hb)), w2(SK.VE.y(a), SK.VE.y(b), n, vy(a, n, ha), vy(b, n, hb)))

def w_dot(+a: SK.VE, +b: SK.VE, +n: Nat, +ha: {vw(a, n) == True{} : Bool}, +hb: {vw(b, n) == True{} : Bool}) -> {w(SK.VE.dot(a, b), n) == True{} : Bool}:
  and_i(w(E.QMul{SK.VE.x(a), SK.VE.x(b)}, n), w(E.QMul{SK.VE.y(a), SK.VE.y(b)}, n), w2(SK.VE.x(a), SK.VE.x(b), n, vx(a, n, ha), vx(b, n, hb)), w2(SK.VE.y(a), SK.VE.y(b), n, vy(a, n, ha), vy(b, n, hb)))

def w_cross(+a: SK.VE, +b: SK.VE, +n: Nat, +ha: {vw(a, n) == True{} : Bool}, +hb: {vw(b, n) == True{} : Bool}) -> {w(SK.VE.cross(a, b), n) == True{} : Bool}:
  and_i(w(E.QMul{SK.VE.x(a), SK.VE.y(b)}, n), w(E.QMul{SK.VE.y(a), SK.VE.x(b)}, n), w2(SK.VE.x(a), SK.VE.y(b), n, vx(a, n, ha), vy(b, n, hb)), w2(SK.VE.y(a), SK.VE.x(b), n, vy(a, n, ha), vx(b, n, hb)))

def w_norm2(+a: SK.VE, +n: Nat, +ha: {vw(a, n) == True{} : Bool}) -> {w(SK.VE.norm2(a), n) == True{} : Bool}:
  w_dot(a, a, n, ha, ha)

def vw_rot(+c: E.QExpr, +s: E.QExpr, +a: SK.VE, +n: Nat, +hc: {w(c, n) == True{} : Bool}, +hs: {w(s, n) == True{} : Bool}, +ha: {vw(a, n) == True{} : Bool}) -> {vw(SK.VE.rot(c, s, a), n) == True{} : Bool}:
  and_i(w(E.QSub{E.QMul{c, SK.VE.x(a)}, E.QMul{s, SK.VE.y(a)}}, n), w(E.QAdd{E.QMul{s, SK.VE.x(a)}, E.QMul{c, SK.VE.y(a)}}, n), and_i(w(E.QMul{c, SK.VE.x(a)}, n), w(E.QMul{s, SK.VE.y(a)}, n), w2(c, SK.VE.x(a), n, hc, vx(a, n, ha)), w2(s, SK.VE.y(a), n, hs, vy(a, n, ha))), and_i(w(E.QMul{s, SK.VE.x(a)}, n), w(E.QMul{c, SK.VE.y(a)}, n), w2(s, SK.VE.x(a), n, hs, vx(a, n, ha)), w2(c, SK.VE.y(a), n, hc, vy(a, n, ha))))

def vw_dir(+g: SK.Seg, +n: Nat, +h: {Bool.and(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n)) == True{} : Bool}) -> {vw(SK.Seg.dir(g), n) == True{} : Bool}:
  vw_sub(SK.Pt.ve(SK.Seg.q(g)), SK.Pt.ve(SK.Seg.p(g)), n, vw_pt(SK.Seg.q(g), n, and_r(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n), h)), vw_pt(SK.Seg.p(g), n, and_l(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n), h)))

def seg_p(+g: SK.Seg, +n: Nat, +h: {Bool.and(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n)) == True{} : Bool}) -> {ptin(SK.Seg.p(g), n) == True{} : Bool}:
  and_l(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n), h)

def seg_q(+g: SK.Seg, +n: Nat, +h: {Bool.and(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n)) == True{} : Bool}) -> {ptin(SK.Seg.q(g), n) == True{} : Bool}:
  and_r(ptin(SK.Seg.p(g), n), ptin(SK.Seg.q(g), n), h)

def pt_x(+p: SK.Pt, +n: Nat, +h: {ptin(p, n) == True{} : Bool}) -> {BX.lt(SK.Pt.x(p), n) == True{} : Bool}:
  and_l(BX.lt(SK.Pt.x(p), n), BX.lt(SK.Pt.y(p), n), h)

def pt_y(+p: SK.Pt, +n: Nat, +h: {ptin(p, n) == True{} : Bool}) -> {BX.lt(SK.Pt.y(p), n) == True{} : Bool}:
  and_r(BX.lt(SK.Pt.x(p), n), BX.lt(SK.Pt.y(p), n), h)

# the mirror equations (spec/sketch.bend: sym.eqs)
def w_sym(+p: SK.VE, +q: SK.VE, +a: SK.VE, +b: SK.VE, +n: Nat, +hp: {vw(p, n) == True{} : Bool}, +hq: {vw(q, n) == True{} : Bool}, +ha: {vw(a, n) == True{} : Bool}, +hb: {vw(b, n) == True{} : Bool}) -> {ewithin(SK.sym.eqs(p, q, a, b), n) == True{} : Bool}:
  +ww = SK.VE.sub(b, a)
  +u = SK.VE.sub(p, a)
  +v = SK.VE.sub(q, a)
  +hw = vw_sub(b, a, n, hb, ha)
  +hu = vw_sub(p, a, n, hp, ha)
  +hv = vw_sub(q, a, n, hq, ha)
  +xx = {E.QMul{SK.VE.x(ww), SK.VE.x(ww)} : E.QExpr}
  +yy = {E.QMul{SK.VE.y(ww), SK.VE.y(ww)} : E.QExpr}
  +xy = {E.QMul{SK.VE.x(ww), SK.VE.y(ww)} : E.QExpr}
  +nn = {E.QAdd{xx, yy} : E.QExpr}
  +hxx = w2(SK.VE.x(ww), SK.VE.x(ww), n, vx(ww, n, hw), vx(ww, n, hw))
  +hyy = w2(SK.VE.y(ww), SK.VE.y(ww), n, vy(ww, n, hw), vy(ww, n, hw))
  +hxy = w2(SK.VE.x(ww), SK.VE.y(ww), n, vx(ww, n, hw), vy(ww, n, hw))
  +hnn = w2(xx, yy, n, hxx, hyy)
  +e1 = {E.QSub{E.QMul{nn, SK.VE.x(v)}, E.QAdd{E.QMul{E.QSub{xx, yy}, SK.VE.x(u)}, E.QMul{E.QAdd{xy, xy}, SK.VE.y(u)}}} : E.QExpr}
  +e2 = {E.QSub{E.QMul{nn, SK.VE.y(v)}, E.QAdd{E.QMul{E.QAdd{xy, xy}, SK.VE.x(u)}, E.QMul{E.QSub{yy, xx}, SK.VE.y(u)}}} : E.QExpr}
  +h1 = w2(E.QMul{nn, SK.VE.x(v)}, E.QAdd{E.QMul{E.QSub{xx, yy}, SK.VE.x(u)}, E.QMul{E.QAdd{xy, xy}, SK.VE.y(u)}}, n, w2(nn, SK.VE.x(v), n, hnn, vx(v, n, hv)), w2(E.QMul{E.QSub{xx, yy}, SK.VE.x(u)}, E.QMul{E.QAdd{xy, xy}, SK.VE.y(u)}, n, w2(E.QSub{xx, yy}, SK.VE.x(u), n, w2(xx, yy, n, hxx, hyy), vx(u, n, hu)), w2(E.QAdd{xy, xy}, SK.VE.y(u), n, w2(xy, xy, n, hxy, hxy), vy(u, n, hu))))
  +h2 = w2(E.QMul{nn, SK.VE.y(v)}, E.QAdd{E.QMul{E.QAdd{xy, xy}, SK.VE.x(u)}, E.QMul{E.QSub{yy, xx}, SK.VE.y(u)}}, n, w2(nn, SK.VE.y(v), n, hnn, vy(v, n, hv)), w2(E.QMul{E.QAdd{xy, xy}, SK.VE.x(u)}, E.QMul{E.QSub{yy, xx}, SK.VE.y(u)}, n, w2(E.QAdd{xy, xy}, SK.VE.x(u), n, w2(xy, xy, n, hxy, hxy), vx(u, n, hu)), w2(E.QSub{yy, xx}, SK.VE.y(u), n, w2(yy, xx, n, hyy, hxx), vy(u, n, hu))))
  and_i(w(e1, n), ewithin([e2], n), h1, and_i(w(e2, n), True{}, h2, {==}))

# Constraints
# -----------

def one(+e: E.QExpr, +n: Nat, +h: {w(e, n) == True{} : Bool}) -> {ewithin([e], n) == True{} : Bool}:
  and_i(w(e, n), True{}, h, {==})

def two(+e1: E.QExpr, +e2: E.QExpr, +n: Nat, +h1: {w(e1, n) == True{} : Bool}, +h2: {w(e2, n) == True{} : Bool}) -> {ewithin([e1, e2], n) == True{} : Bool}:
  and_i(w(e1, n), ewithin([e2], n), h1, one(e2, n, h2))

# each constraint's equations are within n
def cw(+es: List<&2, SK.Ent>, k: SK.Constraint, +n: Nat, +hk: {BX.Constraint.within(k, n) == True{} : Bool}, +hr: {WF.crefs(es, k) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}, +he: {WF.ents(es, es) == True{} : Bool}) -> {ewithin(SK.Constraint.eqs(es, k), n) == True{} : Bool}:
  match k:
    case SK.Coincident{a, b}:
      {==}
    case SK.Horizontal{a, b}:
      {==}
    case SK.Vertical{a, b}:
      {==}
    case SK.Concentric{a, b}:
      {==}
    case SK.EqualRadius{a, b}:
      {==}
    case SK.Fix{+v, +c}:
      one(E.QSub{SK.var(v), E.QCst{c}}, n, and_i(BX.lt(v, n), True{}, hk, {==}))
    case SK.Distance{+p, +q, +d}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +pq = ptok(es, q, n, KA.band_r(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +dv = SK.VE.sub(SK.Pt.ve(SK.pt(es, q)), SK.Pt.ve(SK.pt(es, p)))
      one(E.QSub{SK.VE.norm2(dv), E.QMul{d, d}}, n, w2(SK.VE.norm2(dv), E.QMul{d, d}, n, w_norm2(dv, n, vw_sub(SK.Pt.ve(SK.pt(es, q)), SK.Pt.ve(SK.pt(es, p)), n, vw_pt(SK.pt(es, q), n, pq), vw_pt(SK.pt(es, p), n, pp))), w2(d, d, n, hk, hk)))
    case SK.HDistance{+p, +q, +d}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +pq = ptok(es, q, n, KA.band_r(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +xq = SK.var(SK.Pt.x(SK.pt(es, q)))
      +xp = SK.var(SK.Pt.x(SK.pt(es, p)))
      one(E.QSub{E.QSub{xq, xp}, d}, n, w2(E.QSub{xq, xp}, d, n, w2(xq, xp, n, pt_x(SK.pt(es, q), n, pq), pt_x(SK.pt(es, p), n, pp)), hk))
    case SK.VDistance{+p, +q, +d}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +pq = ptok(es, q, n, KA.band_r(WF.ispt(es, p), WF.ispt(es, q), hr), hw)
      +yq = SK.var(SK.Pt.y(SK.pt(es, q)))
      +yp = SK.var(SK.Pt.y(SK.pt(es, p)))
      one(E.QSub{E.QSub{yq, yp}, d}, n, w2(E.QSub{yq, yp}, d, n, w2(yq, yp, n, pt_y(SK.pt(es, q), n, pq), pt_y(SK.pt(es, p), n, pp)), hk))
    case SK.Radius{+c, +d}:
      +co = circok(es, c, n, hr, hw, he)
      +r = SK.var(SK.Circ.r(SK.circ(es, c)))
      one(E.QSub{r, d}, n, w2(r, d, n, and_r(ptin(SK.Circ.c(SK.circ(es, c)), n), BX.lt(SK.Circ.r(SK.circ(es, c)), n), co), hk))
    case SK.Diameter{+c, +d}:
      +co = circok(es, c, n, hr, hw, he)
      +r = SK.var(SK.Circ.r(SK.circ(es, c)))
      +hr2 = and_r(ptin(SK.Circ.c(SK.circ(es, c)), n), BX.lt(SK.Circ.r(SK.circ(es, c)), n), co)
      one(E.QSub{E.QAdd{r, r}, d}, n, w2(E.QAdd{r, r}, d, n, w2(r, r, n, hr2, hr2), hk))
    case SK.LineDistance{+p, +a, +rev, +d, +l}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.isseg(es, a), hr), hw)
      +sa = segok(es, a, n, KA.band_r(WF.ispt(es, p), WF.isseg(es, a), hr), hw, he)
      +g = SK.dseg(es, a, rev)
      +ds = dsegok(es, a, rev, n, sa)
      +hd = and_l(w(d, n), BX.lt(l, n), hk)
      +hl = and_r(w(d, n), BX.lt(l, n), hk)
      +u = SK.VE.sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(g)))
      +lv = SK.var(l)
      two(E.QSub{SK.VE.cross(SK.Seg.dir(g), u), E.QMul{d, lv}}, E.QSub{E.QMul{lv, lv}, SK.VE.norm2(SK.Seg.dir(SK.seg(es, a)))}, n, w2(SK.VE.cross(SK.Seg.dir(g), u), E.QMul{d, lv}, n, w_cross(SK.Seg.dir(g), u, n, vw_dir(g, n, ds), vw_sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(g)), n, vw_pt(SK.pt(es, p), n, pp), vw_pt(SK.Seg.p(g), n, seg_p(g, n, ds)))), w2(d, lv, n, hd, hl)), w2(E.QMul{lv, lv}, SK.VE.norm2(SK.Seg.dir(SK.seg(es, a))), n, w2(lv, lv, n, hl, hl), w_norm2(SK.Seg.dir(SK.seg(es, a)), n, vw_dir(SK.seg(es, a), n, sa))))
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      +sa = segok(es, a, n, KA.band_l(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +sb = segok(es, b, n, KA.band_r(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +da = SK.Seg.dir(SK.dseg(es, a, ra))
      +db = SK.Seg.dir(SK.dseg(es, b, rb))
      one(SK.VE.cross(SK.VE.rot(c, s, da), db), n, w_cross(SK.VE.rot(c, s, da), db, n, vw_rot(c, s, da, n, and_l(w(c, n), w(s, n), hk), and_r(w(c, n), w(s, n), hk), vw_dir(SK.dseg(es, a, ra), n, dsegok(es, a, ra, n, sa))), vw_dir(SK.dseg(es, b, rb), n, dsegok(es, b, rb, n, sb))))
    case SK.EqualLength{+a, +b}:
      +sa = segok(es, a, n, KA.band_l(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +sb = segok(es, b, n, KA.band_r(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +da = SK.Seg.dir(SK.seg(es, a))
      +db = SK.Seg.dir(SK.seg(es, b))
      one(E.QSub{SK.VE.norm2(da), SK.VE.norm2(db)}, n, w2(SK.VE.norm2(da), SK.VE.norm2(db), n, w_norm2(da, n, vw_dir(SK.seg(es, a), n, sa)), w_norm2(db, n, vw_dir(SK.seg(es, b), n, sb))))
    case SK.Perpendicular{+a, +b}:
      +sa = segok(es, a, n, KA.band_l(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +sb = segok(es, b, n, KA.band_r(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      one(SK.VE.dot(SK.Seg.dir(SK.seg(es, a)), SK.Seg.dir(SK.seg(es, b))), n, w_dot(SK.Seg.dir(SK.seg(es, a)), SK.Seg.dir(SK.seg(es, b)), n, vw_dir(SK.seg(es, a), n, sa), vw_dir(SK.seg(es, b), n, sb)))
    case SK.Parallel{+a, +b}:
      +sa = segok(es, a, n, KA.band_l(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      +sb = segok(es, b, n, KA.band_r(WF.isseg(es, a), WF.isseg(es, b), hr), hw, he)
      one(SK.VE.cross(SK.Seg.dir(SK.seg(es, a)), SK.Seg.dir(SK.seg(es, b))), n, w_cross(SK.Seg.dir(SK.seg(es, a)), SK.Seg.dir(SK.seg(es, b)), n, vw_dir(SK.seg(es, a), n, sa), vw_dir(SK.seg(es, b), n, sb)))
    case SK.OnLine{+p, +a}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.isseg(es, a), hr), hw)
      +sa = segok(es, a, n, KA.band_r(WF.ispt(es, p), WF.isseg(es, a), hr), hw, he)
      +g = SK.seg(es, a)
      +u = SK.VE.sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(g)))
      one(SK.VE.cross(SK.Seg.dir(g), u), n, w_cross(SK.Seg.dir(g), u, n, vw_dir(g, n, sa), vw_sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(g)), n, vw_pt(SK.pt(es, p), n, pp), vw_pt(SK.Seg.p(g), n, seg_p(g, n, sa)))))
    case SK.OnCircle{+p, +c}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), WF.iscirc(es, c), hr), hw)
      +co = circok(es, c, n, KA.band_r(WF.ispt(es, p), WF.iscirc(es, c), hr), hw, he)
      +cc = SK.Circ.c(SK.circ(es, c))
      +r = SK.var(SK.Circ.r(SK.circ(es, c)))
      +hr2 = and_r(ptin(cc, n), BX.lt(SK.Circ.r(SK.circ(es, c)), n), co)
      +u = SK.VE.sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(cc))
      one(E.QSub{SK.VE.norm2(u), E.QMul{r, r}}, n, w2(SK.VE.norm2(u), E.QMul{r, r}, n, w_norm2(u, n, vw_sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(cc), n, vw_pt(SK.pt(es, p), n, pp), vw_pt(cc, n, and_l(ptin(cc, n), BX.lt(SK.Circ.r(SK.circ(es, c)), n), co)))), w2(r, r, n, hr2, hr2)))
    case SK.Midpoint{+m, +a}:
      +pm = ptok(es, m, n, KA.band_l(WF.ispt(es, m), WF.isseg(es, a), hr), hw)
      +sa = segok(es, a, n, KA.band_r(WF.ispt(es, m), WF.isseg(es, a), hr), hw, he)
      +g = SK.seg(es, a)
      +ps = seg_p(g, n, sa)
      +qs = seg_q(g, n, sa)
      +xm = SK.var(SK.Pt.x(SK.pt(es, m)))
      +ym = SK.var(SK.Pt.y(SK.pt(es, m)))
      +xa = SK.var(SK.Pt.x(SK.Seg.p(g)))
      +xb = SK.var(SK.Pt.x(SK.Seg.q(g)))
      +ya = SK.var(SK.Pt.y(SK.Seg.p(g)))
      +yb = SK.var(SK.Pt.y(SK.Seg.q(g)))
      two(E.QSub{E.QAdd{xm, xm}, E.QAdd{xa, xb}}, E.QSub{E.QAdd{ym, ym}, E.QAdd{ya, yb}}, n, w2(E.QAdd{xm, xm}, E.QAdd{xa, xb}, n, w2(xm, xm, n, pt_x(SK.pt(es, m), n, pm), pt_x(SK.pt(es, m), n, pm)), w2(xa, xb, n, pt_x(SK.Seg.p(g), n, ps), pt_x(SK.Seg.q(g), n, qs))), w2(E.QAdd{ym, ym}, E.QAdd{ya, yb}, n, w2(ym, ym, n, pt_y(SK.pt(es, m), n, pm), pt_y(SK.pt(es, m), n, pm)), w2(ya, yb, n, pt_y(SK.Seg.p(g), n, ps), pt_y(SK.Seg.q(g), n, qs))))
    case SK.Symmetric{+p, +q, +a}:
      +pp = ptok(es, p, n, KA.band_l(WF.ispt(es, p), KA.band(WF.ispt(es, q), WF.isseg(es, a)), hr), hw)
      +hqa = KA.band_r(WF.ispt(es, p), KA.band(WF.ispt(es, q), WF.isseg(es, a)), hr)
      +pq = ptok(es, q, n, KA.band_l(WF.ispt(es, q), WF.isseg(es, a), hqa), hw)
      +sa = segok(es, a, n, KA.band_r(WF.ispt(es, q), WF.isseg(es, a), hqa), hw, he)
      +g = SK.seg(es, a)
      w_sym(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.pt(es, q)), SK.Pt.ve(SK.Seg.p(g)), SK.Pt.ve(SK.Seg.q(g)), n, vw_pt(SK.pt(es, p), n, pp), vw_pt(SK.pt(es, q), n, pq), vw_pt(SK.Seg.p(g), n, seg_p(g, n, sa)), vw_pt(SK.Seg.q(g), n, seg_q(g, n, sa)))

def eqs_go(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +n: Nat, +hc: {BX.Sketch.within.cons(cs, n) == True{} : Bool}, +hr: {WF.cons(es, cs) == True{} : Bool}, +hw: {BX.Sketch.within.ents(es, n) == True{} : Bool}, +he: {WF.ents(es, es) == True{} : Bool}) -> {ewithin(SK.Sketch.eqs.go(es, cs), n) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, +k}, +t}:
      eqs_go(es, t, n, and_r(BX.Constraint.within(k, n), BX.Sketch.within.cons(t, n), hc), KA.band_r(WF.cmerge(es, k), WF.cons(es, t), KA.band_r(WF.crefs(es, k), KA.band(WF.cmerge(es, k), WF.cons(es, t)), hr)), hw, he)
    case Con{SK.Rec{id, False{}, +k}, +t}:
      ewithin_cat(SK.Constraint.eqs(es, k), SK.Sketch.eqs.go(es, t), n, cw(es, k, n, and_l(BX.Constraint.within(k, n), BX.Sketch.within.cons(t, n), hc), KA.band_l(WF.crefs(es, k), KA.band(WF.cmerge(es, k), WF.cons(es, t)), hr), hw, he), eqs_go(es, t, n, and_r(BX.Constraint.within(k, n), BX.Sketch.within.cons(t, n), hc), KA.band_r(WF.cmerge(es, k), WF.cons(es, t), KA.band_r(WF.crefs(es, k), KA.band(WF.cmerge(es, k), WF.cons(es, t)), hr)), hw, he))

# a covered sketch passing the check: its adjacency lists are below n
def cov(sk: SK.Sketch, +n: Nat, +hcov: {BX.Sketch.within(sk, n) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {D.adjb(ST.adj(SK.Sketch.eqs(sk)), n) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      adjb_of(SK.Sketch.eqs.go(es, cs), n, eqs_go(es, cs, n, and_r(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), hcov), KA.band_r(WF.ents(es, es), WF.cons(es, cs), hwf), and_l(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), hcov), KA.band_l(WF.ents(es, es), WF.cons(es, cs), hwf)))
