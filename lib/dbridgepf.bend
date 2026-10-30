# bend-cad: the refutation decision at the sketch's level (PLAN-sk13b
# B4.2). For c with the constraints cs, lib/drefpf.bend's LRefOk over
# their facts, their sides and their positions with kinds (lib/dconflict
# angl, which the Angle check reads) is the spec's RefOk, both ways, so no
# LRefOk means no RefOk. And the closure's bound holds: t = 1 + n is past
# the sketch's points and the variables of any constraints' facts, for a
# sketch covered by n. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./listpf.bend as LI
import ./kbpf.bend as KB
import ./covpf.bend as CV
import ./wfdec.bend as WF
import ./pass.bend as PA
import ./seppf.bend as SP
import ./hspacepf.bend as HP
import ./dcbelowpf.bend as BL
import ./conflict.bend as CO
import ./dclose.bend as DC
import ./dref.bend as DF
import ./drefpf.bend as DRF
import ./dconflict.bend as DCF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Positions with kinds
# --------------------

def ain.some(+p: Nat, +kc: SK.Constraint, n: Nat, h: {DRF.aat(Nil{}, n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>}) -> Empty:
  KA.ft(Equal.cong(Maybe<&2, DF.Ang>, Bool, m => DRF.ag.some(m), None{}, Some{DF.Ang{p, kc}}, h))

def ain.hd(+sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, +k: SK.Constraint, +p: Nat, +kc: SK.Constraint, +em: {SV.kind_at(sk, q) == Some{k} : Maybe<&2, SK.Constraint>},
  +h: {Some{DF.Ang{q, k}} == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>}) -> M.Both({SV.mem(p, Con{q, t}) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}):
  +ep = Equal.cong(Maybe<&2, DF.Ang>, Nat, m => DRF.ag.p(m), Some{DF.Ang{q, k}}, Some{DF.Ang{p, kc}}, h)
  +ek = Equal.cong(Maybe<&2, DF.Ang>, SK.Constraint, m => DRF.ag.k(m), Some{DF.Ang{q, k}}, Some{DF.Ang{p, kc}}, h)
  ((%ep : {SV.bor(SV.eq(_, q), SV.mem(_, t)) == True{} : Bool} LI.bor_l(SV.eq(q, q), SV.mem(q, t), LI.eq_refl(q))),
   (%ep : {SV.kind_at(sk, _) == Some{kc} : Maybe<&2, SK.Constraint>}
     (%ek : {SV.kind_at(sk, q) == Some{_} : Maybe<&2, SK.Constraint>}
       em)))

def ain.tl(+sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, +p: Nat, +kc: SK.Constraint, h: M.Both({SV.mem(p, t) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}))
  -> M.Both({SV.mem(p, Con{q, t}) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}):
  (hm, hk) = h
  (LI.bor_r(SV.eq(p, q), SV.mem(p, t), hm), hk)

def ain.p(m: Maybe<&2, SK.Constraint>, +sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, n: Nat, +p: Nat, +kc: SK.Constraint, +em: {SV.kind_at(sk, q) == m : Maybe<&2, SK.Constraint>},
  h: {DRF.aat(DCF.angl.p(m, q, DCF.angl(sk, t)), n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>},
  ih: @j: Nat -> {DRF.aat(DCF.angl(sk, t), j) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>} -> M.Both({SV.mem(p, t) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}))
  -> M.Both({SV.mem(p, Con{q, t}) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}):
  match m n:
    case None{} n:
      ain.tl(sk, q, t, p, kc, ih(n, h))
    case Some{+k} 0n:
      ain.hd(sk, q, t, k, p, kc, em, h)
    case Some{+k} 1n+j:
      ain.tl(sk, q, t, p, kc, ih(j, h))

# an entry of angl is a member with its kind
def ain_of(cs: List<&2, Nat>, +sk: SK.Sketch, n: Nat, +p: Nat, +kc: SK.Constraint, h: {DRF.aat(DCF.angl(sk, cs), n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>})
  -> M.Both({SV.mem(p, cs) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}):
  match cs:
    case Nil{}:
      absurd(M.Both({SV.mem(p, Nil{}) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}), ain.some(p, kc, n, h))
    case Con{+q, +t}:
      ain.p(SV.kind_at(sk, q), sk, q, t, n, p, kc, {==}, h, j => hj => ain_of(t, sk, j, p, kc, hj))

def ato.p(m: Maybe<&2, SK.Constraint>, +sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, +p: Nat, +kc: SK.Constraint, +em: {SV.kind_at(sk, q) == m : Maybe<&2, SK.Constraint>}, hin: DRF.AngIn(p, kc, DCF.angl(sk, t)))
  -> DRF.AngIn(p, kc, DCF.angl.p(m, q, DCF.angl(sk, t))):
  match m:
    case None{}:
      hin
    case Some{+k}:
      (j, ej) = hin
      (1n+j, ej)

def ato.q(+sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, +kc: SK.Constraint, hk: {SV.kind_at(sk, q) == Some{kc} : Maybe<&2, SK.Constraint>})
  -> DRF.AngIn(q, kc, DCF.angl.p(SV.kind_at(sk, q), q, DCF.angl(sk, t))):
  (%Equal.sym(Maybe<&2, SK.Constraint>, SV.kind_at(sk, q), Some{kc}, hk) : DRF.AngIn(q, kc, DCF.angl.p(_, q, DCF.angl(sk, t)))
    (0n, {==}))

def ato.c(b: Bool, +sk: SK.Sketch, +q: Nat, +t: List<&2, Nat>, +p: Nat, +kc: SK.Constraint, eb: {SV.eq(p, q) == b : Bool}, hm: {SV.bor(b, SV.mem(p, t)) == True{} : Bool},
  hk: {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}, ih: {SV.mem(p, t) == True{} : Bool} -> DRF.AngIn(p, kc, DCF.angl(sk, t)))
  -> DRF.AngIn(p, kc, DCF.angl.p(SV.kind_at(sk, q), q, DCF.angl(sk, t))):
  match b:
    case True{}:
      +e = LI.eq_ok(p, q, eb)
      (%Equal.sym(Nat, p, q, e) : DRF.AngIn(_, kc, DCF.angl.p(SV.kind_at(sk, q), q, DCF.angl(sk, t)))
        ato.q(sk, q, t, kc,
          (%e : {SV.kind_at(sk, _) == Some{kc} : Maybe<&2, SK.Constraint>}
            hk)))
    case False{}:
      ato.p(SV.kind_at(sk, q), sk, q, t, p, kc, {==}, ih(hm))

# a member with its kind is an entry of angl
def ain_to(cs: List<&2, Nat>, +sk: SK.Sketch, +p: Nat, +kc: SK.Constraint, hm: {SV.mem(p, cs) == True{} : Bool}, +hk: {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>})
  -> DRF.AngIn(p, kc, DCF.angl(sk, cs)):
  match cs:
    case Nil{}:
      absurd(DRF.AngIn(p, kc, Nil{}), KA.ft(hm))
    case Con{+q, +t}:
      ato.c(SV.eq(p, q), sk, q, t, p, kc, {==}, hm, hk, a => ain_to(t, sk, p, kc, a, hk))

# The bridge
# ----------

def ain.use(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool, +kc: SK.Constraint,
  hb: M.Both({SV.mem(p, Con{c, cs}) == True{} : Bool}, {SV.kind_at(sk, p) == Some{kc} : Maybe<&2, SK.Constraint>}),
  ra: DR.RefAngle(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, dr, di, kc, fst))
  -> {SV.mem(p, Con{c, cs}) == True{} : Bool} & SV.RefAngle.at(sk, c, cs, cx, dr, di, SV.kind_at(sk, p), fst):
  (hm, hk) = hb
  (hm, (%Equal.sym(Maybe<&2, SK.Constraint>, SV.kind_at(sk, p), Some{kc}, hk) : SV.RefAngle.at(sk, c, cs, cx, dr, di, _, fst)
    ra))

def lra.of(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool,
  h: DRF.AngOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, DCF.angl(sk, Con{c, cs}), dr, di, p, fst))
  -> {SV.mem(p, Con{c, cs}) == True{} : Bool} & SV.RefAngle.at(sk, c, cs, cx, dr, di, SV.kind_at(sk, p), fst):
  (+kc, r1) = h
  (hin, ra) = r1
  (n, en) = hin
  ain.use(sk, c, cs, cx, dr, di, p, fst, kc, ain_of(Con{c, cs}, sk, n, p, kc, en), ra)

# LRefOk, at the sketch's level, is RefOk
def lref_of(r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>,
  h: DRF.LRefOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, CO.supp.ss(sk, c, cs), DCF.angl(sk, Con{c, cs}), r)) -> SV.RefOk(sk, c, cs, cx, r):
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      h
    case DR.RColl{+dr, +di, +s}:
      h
    case DR.RAngle{+dr, +di, +p, +fst}:
      lra.of(sk, c, cs, cx, dr, di, p, fst, h)

def lra.m(m: Maybe<&2, SK.Constraint>, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool,
  +em: {SV.kind_at(sk, p) == m : Maybe<&2, SK.Constraint>}, hm: {SV.mem(p, Con{c, cs}) == True{} : Bool}, ra: SV.RefAngle.at(sk, c, cs, cx, dr, di, m, fst))
  -> DRF.AngOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, DCF.angl(sk, Con{c, cs}), dr, di, p, fst):
  match m:
    case None{}:
      absurd(DRF.AngOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, DCF.angl(sk, Con{c, cs}), dr, di, p, fst), ra)
    case Some{+kc}:
      (kc, (ain_to(Con{c, cs}, sk, p, kc, hm, em), ra))

# RefOk is LRefOk at the sketch's level
def lref_to(r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, h: SV.RefOk(sk, c, cs, cx, r))
  -> DRF.LRefOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, CO.supp.ss(sk, c, cs), DCF.angl(sk, Con{c, cs}), r):
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      h
    case DR.RColl{+dr, +di, +s}:
      h
    case DR.RAngle{+dr, +di, +p, +fst}:
      (hm, ra) = h
      lra.m(SV.kind_at(sk, p), sk, c, cs, cx, dr, di, p, fst, {==}, hm, ra)

def nodir.go(+r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>,
  h: DRF.NoLRef(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, CO.supp.ss(sk, c, cs), DCF.angl(sk, Con{c, cs})), hr: SV.RefOk(sk, c, cs, cx, r)) -> Empty:
  h(r, lref_to(r, sk, c, cs, cx, hr))

# no LRefOk means no RefOk
def nodir_of(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>,
  h: DRF.NoLRef(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), cx, CO.supp.ss(sk, c, cs), DCF.angl(sk, Con{c, cs}))) -> SV.NoDirRef(sk, c, cs, cx):
  r => nodir.go(r, sk, c, cs, cx, h)

# Coverage
# --------

def lt1(+a: Nat, +n: Nat, h: {BX.lt(a, n) == True{} : Bool}) -> {SV.lt(a, 1n+n) == True{} : Bool}:
  KB.lt_up(a, n, (%CV.lt_bx(a, n) : {_ == True{} : Bool} h))

def pg(g: SK.Geo, +id: Nat, +cst: Bool, +n: Nat, +h: {BX.Ent.within(SK.Ent{id, cst, g}, n) == True{} : Bool}) -> {DC.ptsb.g(g, 1n+n) == True{} : Bool}:
  match g:
    case SK.GPoint{+x, +y}:
      LI.band_i(SV.lt(x, 1n+n), SV.lt(y, 1n+n), lt1(x, n, CV.and_l(BX.lt(x, n), BX.lt(y, n), h)), lt1(y, n, CV.and_r(BX.lt(x, n), BX.lt(y, n), h)))
    case SK.GSeg{p, q}:
      {==}
    case SK.GCirc{c, r}:
      {==}
    case SK.GArc{s, e, b}:
      {==}

def ptsb_of(es: List<&2, SK.Ent>, +n: Nat, +h: {BX.Sketch.within.ents(es, n) == True{} : Bool}) -> {DC.ptsb(es, 1n+n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{SK.Ent{+id, +cst, +g}, +t}:
      LI.band_i(DC.ptsb.g(g, 1n+n), DC.ptsb(t, 1n+n), pg(g, id, cst, n, CV.and_l(BX.Ent.within(SK.Ent{id, cst, g}, n), BX.Sketch.within.ents(t, n), h)),
        ptsb_of(t, n, CV.and_r(BX.Ent.within(SK.Ent{id, cst, g}, n), BX.Sketch.within.ents(t, n), h)))

# t = 1 + n is past the sketch's points
def zb_of(sk: SK.Sketch, +n: Nat, +hw: {BX.Sketch.within(sk, n) == True{} : Bool}) -> {DC.zb(SV.ents(sk), 1n+n) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      LI.band_i(SV.lt(0n, 1n+n), DC.ptsb(es, 1n+n), {==}, ptsb_of(es, n, CV.and_l(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), hw)))

def vb_of(e: E.QExpr, +n: Nat, +h: {BX.QExpr.within(e, n) == True{} : Bool}) -> {SP.vbelow(e, 1n+n) == True{} : Bool}:
  match e:
    case E.QVar{+i}:
      lt1(i, n, h)
    case E.QCst{c}:
      {==}
    case E.QAdd{+a, +b}:
      LI.band_i(SP.vbelow(a, 1n+n), SP.vbelow(b, 1n+n), vb_of(a, n, CV.and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)), vb_of(b, n, CV.and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)))
    case E.QSub{+a, +b}:
      LI.band_i(SP.vbelow(a, 1n+n), SP.vbelow(b, 1n+n), vb_of(a, n, CV.and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)), vb_of(b, n, CV.and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)))
    case E.QMul{+a, +b}:
      LI.band_i(SP.vbelow(a, 1n+n), SP.vbelow(b, 1n+n), vb_of(a, n, CV.and_l(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)), vb_of(b, n, CV.and_r(BX.QExpr.within(a, n), BX.QExpr.within(b, n), h)))
    case E.QNeg{+a}:
      vb_of(a, n, h)

def segp(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool}) -> BL.PtB(SK.Seg.p(SK.seg.of(es, m)), t):
  match m:
    case Some{g}:
      match g:
        case SK.GSeg{+p, q}:
          BL.pt_below(es, p, t, h0, hp)
        case SK.GPoint{x, y}:
          (h0, h0)
        case SK.GCirc{c, r}:
          (h0, h0)
        case SK.GArc{s, e, b}:
          (h0, h0)
    case None{}:
      (h0, h0)

def segq(+es: List<&2, SK.Ent>, m: Maybe<&2, SK.Geo>, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool}) -> BL.PtB(SK.Seg.q(SK.seg.of(es, m)), t):
  match m:
    case Some{g}:
      match g:
        case SK.GSeg{p, +q}:
          BL.pt_below(es, q, t, h0, hp)
        case SK.GPoint{x, y}:
          (h0, h0)
        case SK.GCirc{c, r}:
          (h0, h0)
        case SK.GArc{s, e, b}:
          (h0, h0)
    case None{}:
      (h0, h0)

def dseg_below(+es: List<&2, SK.Ent>, +b: Nat, rev: Bool, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool}) -> HP.VBelow(SK.Seg.dir(SK.dseg(es, b, rev)), t):
  match rev:
    case False{}:
      BL.segof_below(es, SK.find(b, es), t, h0, hp)
    case True{}:
      BL.sub_below(SK.Seg.p(SK.seg(es, b)), SK.Seg.q(SK.seg(es, b)), t, segp(es, SK.find(b, es), t, h0, hp), segq(es, SK.find(b, es), t, h0, hp))

def vbb(+x: SK.VE, +t: Nat, h: HP.VBelow(x, t)) -> {SV.band(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t)) == True{} : Bool}:
  (a, b) = h
  LI.band_i(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t), a, b)

def fbds_ang(c: E.QExpr, s: E.QExpr, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +t: Nat, +h0: {SV.lt(0n, t) == True{} : Bool}, +hp: {DC.ptsb(es, t) == True{} : Bool})
  -> {DC.fb.ds(DR.dstat.angle(es, a, ra, b, rb, c, s), t) == True{} : Bool}:
  match c:
    case E.QCst{+qc}:
      match s:
        case E.QCst{+qs}:
          vbb(DR.gmul(DR.Lab{qc, S.Q.neg(qs)}, SK.Seg.dir(SK.dseg(es, b, rb))), t, BL.vb_gmul(DR.Lab{qc, S.Q.neg(qs)}, SK.Seg.dir(SK.dseg(es, b, rb)), t, dseg_below(es, b, rb, t, h0, hp)))
        case E.QVar{i}:
          {==}
        case E.QAdd{x, y}:
          {==}
        case E.QSub{x, y}:
          {==}
        case E.QMul{x, y}:
          {==}
        case E.QNeg{x}:
          {==}
    case E.QVar{i}:
      {==}
    case E.QAdd{x, y}:
      {==}
    case E.QSub{x, y}:
      {==}
    case E.QMul{x, y}:
      {==}
    case E.QNeg{x}:
      {==}

def fbds_k(k: SK.Constraint, +es: List<&2, SK.Ent>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool}) -> {DC.fb.ds(DR.dstat(es, k), t) == True{} : Bool}:
  match k:
    case SK.Parallel{+a, +b}:
      vbb(DR.zseg(es, b), t, BL.zdir_below(es, t, DR.NSeg{b}, hz))
    case SK.Perpendicular{+a, +b}:
      vbb(DR.imul(DR.zseg(es, b)), t, BL.vb_imul(DR.zseg(es, b), t, BL.zdir_below(es, t, DR.NSeg{b}, hz)))
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      fbds_ang(c, s, es, a, ra, b, rb, t, LI.band_l(SV.lt(0n, t), DC.ptsb(es, t), hz), LI.band_r(SV.lt(0n, t), DC.ptsb(es, t), hz))
    case SK.OnLine{+p, +a}:
      vbb(SK.VE.sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(SK.seg(es, a)))), t,
        BL.sub_below(SK.pt(es, p), SK.Seg.p(SK.seg(es, a)), t, BL.pt_below(es, p, t, LI.band_l(SV.lt(0n, t), DC.ptsb(es, t), hz), LI.band_r(SV.lt(0n, t), DC.ptsb(es, t), hz)),
          segp(es, SK.find(a, es), t, LI.band_l(SV.lt(0n, t), DC.ptsb(es, t), hz), LI.band_r(SV.lt(0n, t), DC.ptsb(es, t), hz))))
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
    case SK.Fix{v, q}:
      {==}
    case SK.Distance{p, q, d}:
      {==}
    case SK.HDistance{p, q, d}:
      {==}
    case SK.VDistance{p, q, d}:
      {==}
    case SK.Radius{c, d}:
      {==}
    case SK.Diameter{c, d}:
      {==}
    case SK.LineDistance{p, a, rev, d, l}:
      {==}
    case SK.EqualLength{a, b}:
      {==}
    case SK.OnCircle{p, c}:
      {==}
    case SK.Midpoint{m, a}:
      {==}
    case SK.Symmetric{p, q, a}:
      {==}

# a constraint's direction statement is below t
def fbds_of(m: Maybe<&2, SK.Constraint>, +es: List<&2, SK.Ent>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool}) -> {DC.fb.ds(SV.dstat_of(es, m), t) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      fbds_k(k, es, t, hz)

def fb_pick(b: Bool, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>, +rest: List<&2, DR.Fact>, +t: Nat, he: {SP.vbelow(e, t) == True{} : Bool}, hd: {DC.fb.ds(ds, t) == True{} : Bool}, hr: {DC.fb(rest, t) == True{} : Bool})
  -> {DC.fb(SV.facts.pick(b, DR.Fact{e, nd, ds}, rest), t) == True{} : Bool}:
  match b:
    case True{}:
      LI.band_i(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(rest, t)), he, LI.band_i(DC.fb.ds(ds, t), DC.fb(rest, t), hd, hr))
    case False{}:
      hr

# the facts of the equations xs (from position k) are below t
def fb_go(xs: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +wn: Bool, +k: Nat, +n: Nat,
  +hw: {CV.ewithin(xs, n) == True{} : Bool}, +hz: {DC.zb(SV.ents(sk), 1n+n) == True{} : Bool}) -> {DC.fb(SV.facts.go(xs, own, cs, sk, cls, wn, k), 1n+n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fb_pick(SV.mem(SV.nth(own, k), cs), e, SV.fnd.pick(wn, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k))), SV.facts.go(t, own, cs, sk, cls, wn, 1n+k), 1n+n,
        vb_of(e, n, CV.and_l(BX.QExpr.within(e, n), CV.ewithin(t, n), hw)), fbds_of(SV.kind_at(sk, SV.nth(own, k)), SV.ents(sk), 1n+n, hz),
        fb_go(t, own, cs, sk, cls, wn, 1n+k, n, CV.and_r(BX.QExpr.within(e, n), CV.ewithin(t, n), hw), hz))

# a covered, well-formed sketch's equations are within n
def ew_of(sk: SK.Sketch, +n: Nat, +hcov: {BX.Sketch.within(sk, n) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {CV.ewithin(SK.Sketch.eqs(sk), n) == True{} : Bool}:
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      CV.eqs_go(es, cs, n, CV.and_r(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), hcov), KA.band_r(WF.ents(es, es), WF.cons(es, cs), hwf),
        CV.and_l(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), hcov), KA.band_l(WF.ents(es, es), WF.cons(es, cs), hwf))

# the closure's bound for the pass: past the points, and past the facts of
# any constraints
def zb_tv(+sk: SK.Sketch, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}) -> {DC.zb(SV.ents(sk), DCF.tv(sk)) == True{} : Bool}:
  zb_of(sk, PA.nvars(sk), hcov)

def fb_rf(+sk: SK.Sketch, +cs: List<&2, Nat>, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {DC.fb(SV.rfacts(sk, cs), DCF.tv(sk)) == True{} : Bool}:
  fb_go(SK.Sketch.eqs(sk), SV.owners(sk), cs, sk, Nil{}, False{}, 0n, PA.nvars(sk), ew_of(sk, PA.nvars(sk), hcov, hwf), zb_tv(sk, hcov))
