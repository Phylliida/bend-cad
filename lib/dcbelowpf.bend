# bend-cad: the closure's forms are below the tag variable t (PLAN-sk13b
# B3). With t past every point's coordinates (DC.zb), every node's
# direction is below t (zdir_below); rotations, i and the K-squared
# generators' forms keep it (vb_gmul, vb_imul, vb_kre, vb_kim). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./seppf.bend as SP
import ./listpf.bend as LP2
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dclose.bend as DC

# Points and segments
# -------------------

def PtB(p: SK.Pt, +t: Nat) -> Data:
  match p:
    case SK.Pt{x, y}:
      SK.Both({SV.lt(x, t) == True{} : Bool}, {SV.lt(y, t) == True{} : Bool})

def GB(m: Maybe<&2, SK.Geo>, +t: Nat) -> Data:
  match m:
    case Some{g}:
      {DC.ptsb.g(g, t) == True{} : Bool}
    case None{}:
      Unit

def ptof.g(g: SK.Geo, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hg: {DC.ptsb.g(g, t) == True{} : Bool}) -> PtB(SK.pt.of(Some{g}), t):
  match g:
    case SK.GPoint{+x, +y}:
      (LP2.band_l(SV.lt(x, t), SV.lt(y, t), hg), LP2.band_r(SV.lt(x, t), SV.lt(y, t), hg))
    case SK.GSeg{p, q}:
      (h0, h0)
    case SK.GCirc{c, r}:
      (h0, h0)
    case SK.GArc{s, e, b}:
      (h0, h0)

def ptof_below(m: Maybe<&2, SK.Geo>, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, hm: GB(m, t)) -> PtB(SK.pt.of(m), t):
  match m:
    case Some{g}:
      ptof.g(g, t, h0, hm)
    case None{}:
      (h0, h0)

def find_gb.pick(b: Bool, +g: SK.Geo, +rest: Maybe<&2, SK.Geo>, +t: Nat, hg: {DC.ptsb.g(g, t) == True{} : Bool}, hr: GB(rest, t)) -> GB(SK.find.pick(b, g, rest), t):
  match b:
    case True{}:
      hg
    case False{}:
      hr

def find_gb(+id: Nat, es: List<&2, SK.Ent>, +t: Nat, +h: {DC.ptsb(es, t) == True{} : Bool}) -> GB(SK.find(id, es), t):
  match es:
    case Nil{}:
      Unit{}
    case Con{SK.Ent{+eid, c, +g}, +tl}:
      find_gb.pick(Nat.is_eq(eid, id), g, SK.find(id, tl), t, LP2.band_l(DC.ptsb.g(g, t), DC.ptsb(tl, t), h), find_gb(id, tl, t, LP2.band_r(DC.ptsb.g(g, t), DC.ptsb(tl, t), h)))

def pt_below(+es: List<&2, SK.Ent>, +id: Nat, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +h: {DC.ptsb(es, t) == True{} : Bool}) -> PtB(SK.pt(es, id), t):
  ptof_below(SK.find(id, es), t, h0, find_gb(id, es, t, h))

def sub_below(pq: SK.Pt, pp: SK.Pt, +t: Nat, hq: PtB(pq, t), hp: PtB(pp, t)) -> HP.VBelow(SK.VE.sub(SK.Pt.ve(pq), SK.Pt.ve(pp)), t):
  match pq pp:
    case SK.Pt{+a, +b} SK.Pt{+c, +d}:
      (ha, hb) = hq
      (hc, hd) = hp
      (HP.band_tt(SV.lt(a, t), SV.lt(c, t), ha, hc), HP.band_tt(SV.lt(b, t), SV.lt(d, t), hb, hd))

def segof.g(+es: List<&2, SK.Ent>, g: SK.Geo, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool}) -> HP.VBelow(SK.Seg.dir(SK.seg.of(es, Some{g})), t):
  match g:
    case SK.GPoint{x, y}:
      sub_below(SK.Pt{0n, 0n}, SK.Pt{0n, 0n}, t, (h0, h0), (h0, h0))
    case SK.GSeg{+p, +q}:
      sub_below(SK.pt(es, q), SK.pt(es, p), t, pt_below(es, q, t, h0, hp), pt_below(es, p, t, h0, hp))
    case SK.GCirc{c, r}:
      sub_below(SK.Pt{0n, 0n}, SK.Pt{0n, 0n}, t, (h0, h0), (h0, h0))
    case SK.GArc{s, e, b}:
      sub_below(SK.Pt{0n, 0n}, SK.Pt{0n, 0n}, t, (h0, h0), (h0, h0))

def segof_below(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool}) -> HP.VBelow(SK.Seg.dir(SK.seg.of(es, m)), t):
  match m:
    case Some{g}:
      segof.g(es, g, t, h0, hp)
    case None{}:
      sub_below(SK.Pt{0n, 0n}, SK.Pt{0n, 0n}, t, (h0, h0), (h0, h0))

# every node's direction is below t
def zdir_below(+es: List<&2, SK.Ent>, +t: Nat, n: DR.Node, +hz: {DC.zb(es, t) == True{} : Bool}) -> HP.VBelow(DR.zdir(es, n), t):
  match n:
    case DR.NFrame{}:
      ({==}, {==})
    case DR.NSeg{+s}:
      segof_below(es, SK.find(s, es), t, LP2.band_l(SV.lt(0n, t), DC.ptsb(es, t), hz), LP2.band_r(SV.lt(0n, t), DC.ptsb(es, t), hz))

# Forms
# -----

# a rotation keeps it
def vb_gmul(g: DR.Lab, +x: SK.VE, +t: Nat, h: HP.VBelow(x, t)) -> HP.VBelow(DR.gmul(g, x), t):
  match g:
    case DR.Lab{c, s}:
      (+hx, +hy) = h
      (HP.band_tt(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t), hx, hy), HP.band_tt(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t), hx, hy))

# so does i
def vb_imul(+x: SK.VE, +t: Nat, h: HP.VBelow(x, t)) -> HP.VBelow(DR.imul(x), t):
  (hx, hy) = h
  (hy, hx)

# and so do K squared's forms (k, 0) and (0, k)
def vb_kre(+r: SK.VE, +e: E.QExpr, +t: Nat, h: HP.VBelow(r, t), he: {SP.vbelow(e, t) == True{} : Bool})
  -> HP.VBelow(SK.VE.add(DR.vlin(DR.qz(), r, DR.qz(), r), SK.VE{e, DR.zeroe()}), t):
  (+hx, +hy) = h
  (HP.band_tt(SV.band(SP.vbelow(SK.VE.x(r), t), SP.vbelow(SK.VE.x(r), t)), SP.vbelow(e, t), HP.band_tt(SP.vbelow(SK.VE.x(r), t), SP.vbelow(SK.VE.x(r), t), hx, hx), he),
   HP.band_tt(SV.band(SP.vbelow(SK.VE.y(r), t), SP.vbelow(SK.VE.y(r), t)), True{}, HP.band_tt(SP.vbelow(SK.VE.y(r), t), SP.vbelow(SK.VE.y(r), t), hy, hy), {==}))

def vb_kim(+r: SK.VE, +e: E.QExpr, +t: Nat, h: HP.VBelow(r, t), he: {SP.vbelow(e, t) == True{} : Bool})
  -> HP.VBelow(SK.VE.add(DR.vlin(DR.qz(), r, DR.qz(), r), SK.VE{DR.zeroe(), e}), t):
  (+hx, +hy) = h
  (HP.band_tt(SV.band(SP.vbelow(SK.VE.x(r), t), SP.vbelow(SK.VE.x(r), t)), True{}, HP.band_tt(SP.vbelow(SK.VE.x(r), t), SP.vbelow(SK.VE.x(r), t), hx, hx), {==}),
   HP.band_tt(SV.band(SP.vbelow(SK.VE.y(r), t), SP.vbelow(SK.VE.y(r), t)), SP.vbelow(e, t), HP.band_tt(SP.vbelow(SK.VE.y(r), t), SP.vbelow(SK.VE.y(r), t), hy, hy), he))
