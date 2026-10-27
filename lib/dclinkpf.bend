# bend-cad: the closure's new links are right (PLAN-sk13b B3). A
# collapsed set's derivation of a member y is VD at c, below t, the same as
# y (rep_der_ok: Full by par-void, Free by the hull, Tied by
# lib/dctiedpf.bend). Every basis label its tests return gives a member
# and is nonzero (basis_ok); so are the frame's and the roots' (basis_k_ok,
# basis_free_ok). So both kinds of new link keep the links' invariants
# (lks_ok). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qalg.bend as QA
import ./identpf.bend as ID
import ./listpf.bend as LP2
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./spanpf.bend as SN
import ./pair.bend as PT
import ./pairpf.bend as PP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./lab.bend as LB
import ./labpf.bend as LP
import ./labnzpf.bend as NZ
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcderpf.bend as DD
import ./dcmergepf.bend as MG
import ./dcreppf.bend as RP
import ./dctiedpf.bend as TD

def absurd(-A: Type, x: Empty) -> A:
  match x:

# what a derivation of y at c gives
def DerOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +d: DR.Der, +y: SK.VE) -> Data:
  SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isp(DR.concl(es, fs, d)), {DR.Jd.a(DR.concl(es, fs, d)) == a : DR.Node})), HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), y))

# Derivations from a collapsed set
# --------------------------------

def full_der.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, +y: SK.VE, +hy: HP.VBelow(y, t),
  kx: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, c)))), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, c))))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, c))))), SK.VE.x(DR.zseg(es, c))))),
  ky: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, c)))), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, c))))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, c))))), SK.VE.y(DR.zseg(es, c))))))
  -> DerOk(es, fs, ctx, t, DR.NSeg{c}, DR.DVoid{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, c))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, c))), DR.NSeg{c}, y}, y):
  (vx, r1) = kx
  (ix, sx) = r1
  (vy, s1) = ky
  (iy, sy) = s1
  ((((vx, (vy, (ix, (iy, (sx, sy))))), ({==}, {==})), hy), MG.samevd_refl(y))

# y in c's set: its derivation is VD at c, below t, the same as y
def rep_der_ok(r: DC.Rep, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, +y: SK.VE,
  +hr: RP.RepOk(es, fs, ctx, t, k, c, r), +hk: IV.KInvD(es, fs, ctx, t, k), hin: {DC.rep.inb(r, t, y) == True{} : Bool}, +hy: HP.VBelow(y, t), +hz: {DC.zb(es, t) == True{} : Bool})
  -> DerOk(es, fs, ctx, t, DR.NSeg{c}, DC.rep.der(r, es, fs, t, k, c, y), y):
  match r:
    case DC.RFull{}:
      full_der.go(es, fs, ctx, t, k, c, y, hy,
        DD.ks_der_okd(es, fs, ctx, t, k, SK.VE.x(DR.zseg(es, c)), hk, LP2.band_l(KS.ks.inb(k, SK.VE.x(DR.zseg(es, c))), KS.ks.inb(k, SK.VE.y(DR.zseg(es, c))), hr)),
        DD.ks_der_okd(es, fs, ctx, t, k, SK.VE.y(DR.zseg(es, c)), hk, LP2.band_r(KS.ks.inb(k, SK.VE.x(DR.zseg(es, c))), KS.ks.inb(k, SK.VE.y(DR.zseg(es, c))), hr)))
    case DC.RFree{+h}:
      DD.hs_der_okd(es, fs, ctx, DR.NSeg{c}, t, h, y, hr, hin, hy, BL.zdir_below(es, t, DR.NSeg{c}, hz))
    case DC.RTied{+u, +du, +s}:
      (hti, htie) = hr
      TD.tied_ok(es, fs, ctx, t, c, u, du, s, y, hti, htie, hz, hin, hy)

# The tied label test
# -------------------

def cross_gmul.at(+p: List<&2, S.Q>, +uu: SK.VE, +a: S.Q, +b: S.Q, +z: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.cross(uu, DR.gmul(DR.Lab{a, b}, z))), E.qeval(p, PT.pcomb(PT.Pr{a, b}, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z))))):
  LQ.q_trans(E.qeval(p, SK.VE.cross(uu, DR.gmul(DR.Lab{a, b}, z))), E.qeval(p, SK.VE.cross(uu, DR.vlin(a, z, b, DR.imul(z)))), E.qeval(p, PT.pcomb(PT.Pr{a, b}, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z)))),
    QA.sub_cong(S.Q.mul(E.qeval(p, SK.VE.x(uu)), S.Q.add(S.Q.mul(b, E.qeval(p, SK.VE.x(z))), S.Q.mul(a, E.qeval(p, SK.VE.y(z))))), S.Q.mul(E.qeval(p, SK.VE.x(uu)), S.Q.add(S.Q.mul(a, E.qeval(p, SK.VE.y(z))), S.Q.mul(b, E.qeval(p, SK.VE.x(z))))),
      S.Q.mul(E.qeval(p, SK.VE.y(uu)), S.Q.sub(S.Q.mul(a, E.qeval(p, SK.VE.x(z))), S.Q.mul(b, E.qeval(p, SK.VE.y(z))))), S.Q.mul(E.qeval(p, SK.VE.y(uu)), S.Q.add(S.Q.mul(a, E.qeval(p, SK.VE.x(z))), S.Q.mul(b, S.Q.neg(E.qeval(p, SK.VE.y(z)))))),
      LQ.q_mul_cong_r(E.qeval(p, SK.VE.x(uu)), S.Q.add(S.Q.mul(b, E.qeval(p, SK.VE.x(z))), S.Q.mul(a, E.qeval(p, SK.VE.y(z)))), S.Q.add(S.Q.mul(a, E.qeval(p, SK.VE.y(z))), S.Q.mul(b, E.qeval(p, SK.VE.x(z)))), LQ.q_add_comm(S.Q.mul(b, E.qeval(p, SK.VE.x(z))), S.Q.mul(a, E.qeval(p, SK.VE.y(z))))),
      LQ.q_mul_cong_r(E.qeval(p, SK.VE.y(uu)), S.Q.sub(S.Q.mul(a, E.qeval(p, SK.VE.x(z))), S.Q.mul(b, E.qeval(p, SK.VE.y(z)))), S.Q.add(S.Q.mul(a, E.qeval(p, SK.VE.x(z))), S.Q.mul(b, S.Q.neg(E.qeval(p, SK.VE.y(z))))),
        LQ.q_add_cong_r(S.Q.mul(a, E.qeval(p, SK.VE.x(z))), S.Q.neg(S.Q.mul(b, E.qeval(p, SK.VE.y(z)))), S.Q.mul(b, S.Q.neg(E.qeval(p, SK.VE.y(z)))), LQ.q_sym(S.Q.mul(b, S.Q.neg(E.qeval(p, SK.VE.y(z)))), S.Q.neg(S.Q.mul(b, E.qeval(p, SK.VE.y(z)))), QA.mneg(b, E.qeval(p, SK.VE.y(z))))))),
    TD.cross_vlin.at(p, uu, a, z, b, DR.imul(z)))

def cross_gmul(+uu: SK.VE, +a: S.Q, +b: S.Q, +z: SK.VE) -> SV.Ident(SK.VE.cross(uu, DR.gmul(DR.Lab{a, b}, z)), PT.pcomb(PT.Pr{a, b}, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z)))):
  p => cross_gmul.at(p, uu, a, b, z)

def tlab_ok.some(p: PT.Pr, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +uu: SK.VE, +z: SK.VE, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z))) == Some{p} : Maybe<&2, PT.Pr>}, hw: {Some{LB.lab_of(p)} == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(SK.VE.cross(uu, DR.gmul(w, z)), B):
  match p:
    case PT.Pr{+a, +bb}:
      %LP.lsome_inj(DR.Lab{a, bb}, w, hw) : SN.InSpan(SK.VE.cross(uu, DR.gmul(_, z)), B)
      PP.in_tr(PT.pcomb(PT.Pr{a, bb}, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z))), SK.VE.cross(uu, DR.gmul(DR.Lab{a, bb}, z)), B,
        PP.ptest_ok(rows, B, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z)), hr, hl, PT.Pr{a, bb}, hm), cross_gmul(uu, a, bb, z))

def tlab_ok.go(m: Maybe<&2, PT.Pr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +uu: SK.VE, +z: SK.VE, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, SK.VE.cross(uu, z), SK.VE.cross(uu, DR.imul(z))) == m : Maybe<&2, PT.Pr>}, hw: {LB.lab_map(m) == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(SK.VE.cross(uu, DR.gmul(w, z)), B):
  match m:
    case Some{p}:
      tlab_ok.some(p, rows, B, uu, z, w, hr, hl, hm, hw)
    case None{}:
      absurd(SN.InSpan(SK.VE.cross(uu, DR.gmul(w, z)), B), LP.lnone_some(w, hw))

# a label the tied test finds gives a member
def ts_lab_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, s: DC.TS, +z: SK.VE, +w: DR.Lab,
  hti: RP.TInvD(es, fs, ctx, r, t, u, s), hw: {DC.ts.lab(es, fs, u, s, z) == Some{w} : Maybe<&2, DR.Lab>}) -> {DC.ts.inb(s, u, DR.gmul(w, z)) == True{} : Bool}:
  match s:
    case DC.TS{+rows, +ds}:
      (+hr, r1) = hti
      (+hl, ha) = r1
      SN.zero_of_in(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.gmul(w, z)), hr, hl,
        tlab_ok.go(PT.ptest(rows, DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), z), SK.VE.cross(DC.lform(u), DR.imul(z))), rows, DC.crosses(es, fs, u, ds), DC.lform(u), z, w, hr, hl, {==}, hw))

def ts_lab_nz(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +s: DC.TS, +z: SK.VE, +w: DR.Lab, hw: {DC.ts.lab(es, fs, u, s, z) == Some{w} : Maybe<&2, DR.Lab>}) -> NZ.Nz(w):
  NZ.lab_nz(PT.ptest(DC.ts.rows(s), DC.crosses(es, fs, u, DC.ts.ds(s)), SK.VE.cross(DC.lform(u), z), SK.VE.cross(DC.lform(u), DR.imul(z))), DC.ts.rows(s), DC.crosses(es, fs, u, DC.ts.ds(s)),
    SK.VE.cross(DC.lform(u), z), SK.VE.cross(DC.lform(u), DR.imul(z)), w, {==}, hw)

# Bases
# -----

# every label of ws gives a member of r's set, and is nonzero
def BOk(+r: DC.Rep, +t: Nat, +z: SK.VE, ws: List<&2, DR.Lab>) -> Data:
  match ws:
    case Nil{}:
      Unit
    case Con{+w, tl}:
      SK.Both({DC.rep.inb(r, t, DR.gmul(w, z)) == True{} : Bool}, SK.Both(NZ.Nz(w), BOk(r, t, z, tl)))

def bpair_ok(b: Bool, +r: DC.Rep, +t: Nat, +z: SK.VE, +w: DR.Lab, eb: {b == DC.rep.inb(r, t, DR.gmul(LB.lmul(DC.li(), w), z)) : Bool},
  +hw: {DC.rep.inb(r, t, DR.gmul(w, z)) == True{} : Bool}, +nw: NZ.Nz(w)) -> BOk(r, t, z, DC.bpair(b, w)):
  match b:
    case True{}:
      (hw, (nw, (Equal.sym(Bool, True{}, DC.rep.inb(r, t, DR.gmul(LB.lmul(DC.li(), w), z)), eb), (NZ.nz_mul(DC.li(), w, NZ.nz_i(), nw), Unit{}))))
    case False{}:
      (hw, (nw, Unit{}))

def basis_free_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +h: HS.HS, +z: SK.VE,
  +em: {LB.hs.lab(es, fs, t, h, z) == m : Maybe<&2, DR.Lab>}, +hi: IV.HInvD(es, fs, ctx, r, t, h)) -> BOk(DC.RFree{h}, t, z, DC.basis.free(m, t, h, z)):
  match m:
    case None{}:
      Unit{}
    case Some{+w}:
      bpair_ok(HS.hs.inb(h, DR.gmul(LB.lmul(DC.li(), w), z), t), DC.RFree{h}, t, z, w, {==}, LP.hs_lab_ok(es, fs, ctx, r, t, h, z, w, IV.hinv_of(es, fs, ctx, r, t, h, hi), em), NZ.hs_lab_nz(es, fs, t, h, z, w, em))

def basis_tied_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, +du: DR.Der, +s: DC.TS, +z: SK.VE,
  +em: {DC.ts.lab(es, fs, u, s, z) == m : Maybe<&2, DR.Lab>}, +hti: RP.TInvD(es, fs, ctx, r, t, u, s)) -> BOk(DC.RTied{u, du, s}, t, z, DC.basis.tied(m, u, s, z)):
  match m:
    case None{}:
      Unit{}
    case Some{+w}:
      bpair_ok(DC.ts.inb(s, u, DR.gmul(LB.lmul(DC.li(), w), z)), DC.RTied{u, du, s}, t, z, w, {==}, ts_lab_ok(es, fs, ctx, r, t, u, s, z, w, hti, em), ts_lab_nz(es, fs, u, s, z, w, em))

# a collapsed set's basis labels give members and are nonzero
def basis_ok(r: DC.Rep, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, +z: SK.VE, hr: RP.RepOk(es, fs, ctx, t, k, c, r))
  -> BOk(r, t, z, DC.rep.basis(r, es, fs, t, z)):
  match r:
    case DC.RFull{}:
      ({==}, ({==}, ({==}, ({==}, Unit{}))))
    case DC.RFree{+h}:
      basis_free_ok(LB.hs.lab(es, fs, t, h, z), es, fs, ctx, DR.NSeg{c}, t, h, z, {==}, hr)
    case DC.RTied{+u, +du, +s}:
      (hti, htie) = hr
      basis_tied_ok(DC.ts.lab(es, fs, u, s, z), es, fs, ctx, DR.NSeg{c}, t, u, du, s, z, {==}, hti)

# the frame's: Im(w z) in K, and nonzero
def BK(+k: KS.KS, +z: SK.VE, ws: List<&2, DR.Lab>) -> Data:
  match ws:
    case Nil{}:
      Unit
    case Con{+w, tl}:
      SK.Both({KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}, SK.Both(NZ.Nz(w), BK(k, z, tl)))

def bpairk_ok(b: Bool, +k: KS.KS, +z: SK.VE, +w: DR.Lab, eb: {b == KS.ks.inb(k, SK.VE.y(DR.gmul(LB.lmul(DC.li(), w), z))) : Bool},
  +hw: {KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}, +nw: NZ.Nz(w)) -> BK(k, z, DC.bpair(b, w)):
  match b:
    case True{}:
      (hw, (nw, (Equal.sym(Bool, True{}, KS.ks.inb(k, SK.VE.y(DR.gmul(LB.lmul(DC.li(), w), z))), eb), (NZ.nz_mul(DC.li(), w, NZ.nz_i(), nw), Unit{}))))
    case False{}:
      (hw, (nw, Unit{}))

def basis_k_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +z: SK.VE,
  +em: {LB.ks.lab(es, fs, k, z) == m : Maybe<&2, DR.Lab>}, +hk: IV.KInvD(es, fs, ctx, t, k)) -> BK(k, z, DC.basis.k(m, k, z)):
  match m:
    case None{}:
      Unit{}
    case Some{+w}:
      bpairk_ok(KS.ks.inb(k, SK.VE.y(DR.gmul(LB.lmul(DC.li(), w), z))), k, z, w, {==}, LP.ks_lab_ok(es, fs, ctx, k, z, w, IV.kinv_of(es, fs, ctx, t, k, hk), em), NZ.ks_lab_nz(es, fs, k, z, w, em))

# New links
# ---------

def LNz(l: DC.Link) -> Data:
  match l:
    case DC.Link{c, b, +w, d}:
      NZ.Nz(w)

def OptL(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, m: Maybe<&2, DC.Link>) -> Data:
  match m:
    case Some{+l}:
      SK.Both(GN.LOkD(es, fs, ctx, t, l), LNz(l))
    case None{}:
      Unit

def OptW(+r: DC.Rep, +t: Nat, +z: SK.VE, m: Maybe<&2, DR.Lab>) -> Data:
  match m:
    case Some{+w}:
      SK.Both({DC.rep.inb(r, t, DR.gmul(w, z)) == True{} : Bool}, NZ.Nz(w))
    case None{}:
      Unit

def lk.pick_ok(f: Bool, +r: DC.Rep, +t: Nat, +z: SK.VE, +w: DR.Lab, +hw: {DC.rep.inb(r, t, DR.gmul(w, z)) == True{} : Bool}, +nw: NZ.Nz(w), +rest: Maybe<&2, DR.Lab>, hr: OptW(r, t, z, rest))
  -> OptW(r, t, z, DC.lk.pick(f, w, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      (hw, nw)

def lk.first_ok(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>, +r: DC.Rep, +t: Nat, +z: SK.VE, hb: BOk(r, t, z, ws)) -> OptW(r, t, z, DC.lk.first(ws, stored)):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +tl}:
      (hw, r1) = hb
      (nw, rt) = r1
      lk.pick_ok(DC.qspan(stored, w), r, t, z, w, hw, nw, DC.lk.first(tl, stored), lk.first_ok(tl, stored, r, t, z, rt))

def derok_lok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +w: DR.Lab, +d: DR.Der, h: DerOk(es, fs, ctx, t, DR.NSeg{c}, d, DR.gmul(w, DR.zdir(es, b))))
  -> GN.LOkD(es, fs, ctx, t, DC.Link{c, b, w, d}):
  (vb, sv) = h
  (vpa, bx) = vb
  (v, r1) = vpa
  (p, ea) = r1
  (v, (p, (ea, (sv, bx))))

def lk.mk_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, +rep: DC.Rep, +b: DR.Node,
  hm: OptW(rep, t, DR.zdir(es, b), m), +hr: RP.RepOk(es, fs, ctx, t, k, c, rep), +hk: IV.KInvD(es, fs, ctx, t, k), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest)) -> OptL(es, fs, ctx, t, DC.lk.mk(m, es, fs, t, k, c, rep, b, rest)):
  match m:
    case None{}:
      hrest
    case Some{+w}:
      (hin, nw) = hm
      (derok_lok(es, fs, ctx, t, c, b, w, DC.rep.der(rep, es, fs, t, k, c, DR.gmul(w, DR.zdir(es, b))),
         rep_der_ok(rep, es, fs, ctx, t, k, c, DR.gmul(w, DR.zdir(es, b)), hr, hk, hin, BL.vb_gmul(w, DR.zdir(es, b), t, BL.zdir_below(es, t, b, hz)), hz)), nw)

def lk.c.if_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node,
  +hr: RP.RepOk(es, fs, ctx, t, DC.Sk.k(s), c, rep), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest)) -> OptL(es, fs, ctx, t, DC.lk.c.if(f, es, fs, t, s, c, rep, b, rest)):
  match f:
    case True{}:
      hrest
    case False{}:
      lk.mk_ok(DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), es, fs, ctx, t, DC.Sk.k(s), c, rep, b,
        lk.first_ok(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b), rep, t, DR.zdir(es, b), basis_ok(rep, es, fs, ctx, t, DC.Sk.k(s), c, DR.zdir(es, b), hr)),
        hr, hk, hz, rest, hrest)

# the links from c's set are right
def lk.c_ok(bs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep,
  +hr: RP.RepOk(es, fs, ctx, t, DC.Sk.k(s), c, rep), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hz: {DC.zb(es, t) == True{} : Bool}) -> OptL(es, fs, ctx, t, DC.lk.c(bs, es, fs, t, s, c, rep)):
  match bs:
    case Nil{}:
      Unit{}
    case Con{+b, +tl}:
      lk.c.if_ok(DC.node_eq(b, DR.NSeg{c}), es, fs, ctx, t, s, c, rep, b, hr, hk, hz, DC.lk.c(tl, es, fs, t, s, c, rep), lk.c_ok(tl, es, fs, ctx, t, s, c, rep, hr, hk, hz))

# Links turned in from a root
# ---------------------------

def OptK2(+k: KS.KS, +z: SK.VE, m: Maybe<&2, DR.Lab>) -> Data:
  match m:
    case Some{+w}:
      SK.Both({KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}, NZ.Nz(w))
    case None{}:
      Unit

def lkr.pickk(f: Bool, +k: KS.KS, +z: SK.VE, +w: DR.Lab, +hw: {KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}, +nw: NZ.Nz(w), +rest: Maybe<&2, DR.Lab>, hr: OptK2(k, z, rest))
  -> OptK2(k, z, DC.lk.pick(f, w, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      (hw, nw)

def lkr.first_k(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>, +k: KS.KS, +z: SK.VE, hb: BK(k, z, ws)) -> OptK2(k, z, DC.lk.r.first(ws, stored)):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +tl}:
      (hw, r1) = hb
      (nw, rt) = r1
      lkr.pickk(DC.qspan(stored, DR.Lab.conj(w)), k, z, w, hw, nw, DC.lk.r.first(tl, stored), lkr.first_k(tl, stored, k, z, rt))

def lkr.first_h(ws: List<&2, DR.Lab>, +stored: List<&2, DR.Lab>, +r: DC.Rep, +t: Nat, +z: SK.VE, hb: BOk(r, t, z, ws)) -> OptW(r, t, z, DC.lk.r.first(ws, stored)):
  match ws:
    case Nil{}:
      Unit{}
    case Con{+w, +tl}:
      (hw, r1) = hb
      (nw, rt) = r1
      lk.pick_ok(DC.qspan(stored, DR.Lab.conj(w)), r, t, z, w, hw, nw, DC.lk.r.first(tl, stored), lkr.first_h(tl, stored, r, t, z, rt))

# the turn into c of a derivation dw of par(r, w z_c)
def lkr.link(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +r: DR.Node, +w: DR.Lab, +dw: DR.Der, +hz: {DC.zb(es, t) == True{} : Bool},
  hd: DerOk(es, fs, ctx, t, r, dw, DR.gmul(w, DR.zseg(es, c))), nw: NZ.Nz(w))
  -> OptL(es, fs, ctx, t, Some{DC.Link{c, r, DR.Lab.conj(w), DR.DTurn{dw, DR.Lab.conj(w), DR.NSeg{c}}}}):
  (vb, sv) = hd
  (vpa, bx) = vb
  (v, r1) = vpa
  (p, ea) = r1
  (((v, (p, MG.ccw(es, fs, dw, w, DR.NSeg{c}, sv))), ({==}, ({==}, (RP.zref(es, DR.Lab.conj(w), DR.Jd.a(DR.concl(es, fs, dw)), r, ea),
     BL.vb_gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dw))), t, BL.zdir_below(es, t, DR.Jd.a(DR.concl(es, fs, dw)), hz)))))), NZ.nz_conj(w, nw))

def full_frame(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +y: SK.VE, +hy: HP.VBelow(y, t),
  kd: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.y(y))), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(y)))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(y)))), SK.VE.y(y)))))
  -> DerOk(es, fs, ctx, t, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(y)), y}, y):
  (v, r1) = kd
  (ik, sd) = r1
  ((((v, (ik, sd)), ({==}, {==})), hy), MG.samevd_refl(y))

def lkr.frame(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +w: DR.Lab, hw: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(w, DR.zseg(es, c)))) == True{} : Bool}, nw: NZ.Nz(w),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hz: {DC.zb(es, t) == True{} : Bool})
  -> OptL(es, fs, ctx, t, Some{DC.Link{c, DR.NFrame{}, DR.Lab.conj(w), DR.DTurn{DC.lk.r.der(DC.node_eq(DR.NFrame{}, DR.NFrame{}), es, fs, t, s, DR.NFrame{}, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}}):
  lkr.link(es, fs, ctx, t, c, DR.NFrame{}, w, DR.DFrame{KS.ks.der(es, fs, DC.Sk.k(s), SK.VE.y(DR.gmul(w, DR.zseg(es, c)))), DR.gmul(w, DR.zseg(es, c))}, hz,
    full_frame(es, fs, ctx, t, DC.Sk.k(s), DR.gmul(w, DR.zseg(es, c)), BL.vb_gmul(w, DR.zseg(es, c), t, BL.zdir_below(es, t, DR.NSeg{c}, hz)),
      DD.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), SK.VE.y(DR.gmul(w, DR.zseg(es, c))), hk, hw)), nw)

def lkr.mk_f(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, er: {r == DR.NFrame{} : DR.Node},
  hm: OptK2(DC.Sk.k(s), DR.zseg(es, c), m), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest)) -> OptL(es, fs, ctx, t, DC.lk.r.mk(m, es, fs, t, s, c, r, rest)):
  match m:
    case None{}:
      hrest
    case Some{+w}:
      (hw, nw) = hm
      %Equal.sym(DR.Node, r, DR.NFrame{}, er) : OptL(es, fs, ctx, t, Some{DC.Link{c, _, DR.Lab.conj(w), DR.DTurn{DC.lk.r.der(DC.node_eq(_, DR.NFrame{}), es, fs, t, s, _, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}})
      lkr.frame(es, fs, ctx, t, s, c, w, hw, nw, hk, hz)

def lkr.mk_h(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, ef: {False{} == DC.node_eq(r, DR.NFrame{}) : Bool},
  hm: OptW(DC.RFree{DC.rhull(es, fs, t, s, r)}, t, DR.zseg(es, c), m), +hi: IV.HInvD(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r)), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest)) -> OptL(es, fs, ctx, t, DC.lk.r.mk(m, es, fs, t, s, c, r, rest)):
  match m:
    case None{}:
      hrest
    case Some{+w}:
      (hw, nw) = hm
      %ef : OptL(es, fs, ctx, t, Some{DC.Link{c, r, DR.Lab.conj(w), DR.DTurn{DC.lk.r.der(_, es, fs, t, s, r, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}})
      lkr.link(es, fs, ctx, t, c, r, w, DC.lk.r.der(False{}, es, fs, t, s, r, DR.gmul(w, DR.zseg(es, c))), hz,
        DD.hs_der_okd(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), DR.gmul(w, DR.zseg(es, c)), hi, hw, BL.vb_gmul(w, DR.zseg(es, c), t, BL.zdir_below(es, t, DR.NSeg{c}, hz)), BL.zdir_below(es, t, r, hz)), nw)

def lkr.one(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, ef: {f == DC.node_eq(r, DR.NFrame{}) : Bool},
  +hi: IV.HInvD(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r)), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest))
  -> OptL(es, fs, ctx, t, DC.lk.r.mk(DC.lk.r.first(DC.lk.r.basis(f, es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), es, fs, t, s, c, r, rest)):
  match f:
    case True{}:
      lkr.mk_f(DC.lk.r.first(DC.basis.k(LB.ks.lab(es, fs, DC.Sk.k(s), DR.zseg(es, c)), DC.Sk.k(s), DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), es, fs, ctx, t, s, c, r,
        GN.node_eq_ok(r, DR.NFrame{}, Equal.sym(Bool, True{}, DC.node_eq(r, DR.NFrame{}), ef)),
        lkr.first_k(DC.basis.k(LB.ks.lab(es, fs, DC.Sk.k(s), DR.zseg(es, c)), DC.Sk.k(s), DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r), DC.Sk.k(s), DR.zseg(es, c),
          basis_k_ok(LB.ks.lab(es, fs, DC.Sk.k(s), DR.zseg(es, c)), es, fs, ctx, t, DC.Sk.k(s), DR.zseg(es, c), {==}, hk)),
        hk, hz, rest, hrest)
    case False{}:
      lkr.mk_h(DC.lk.r.first(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c)), t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), es, fs, ctx, t, s, c, r, ef,
        lkr.first_h(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c)), t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r), DC.RFree{DC.rhull(es, fs, t, s, r)}, t, DR.zseg(es, c),
          basis_free_ok(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c)), es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), DR.zseg(es, c), {==}, hi)),
        hi, hz, rest, hrest)

# the links turned in from the roots are right
def lk.r_ok(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, hro: MG.AllOpenD(es, ctx, rs),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OptL(es, fs, ctx, t, DC.lk.r(rs, es, fs, t, s, c)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (orr, rt) = hro
      lkr.one(DC.node_eq(r, DR.NFrame{}), es, fs, ctx, t, s, c, r, {==}, GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb), hk, hz,
        DC.lk.r(tl, es, fs, t, s, c), lk.r_ok(tl, es, fs, ctx, t, s, c, rt, hk, hms, hls, hz, hb))

def lfirst_ok(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, hm: OptL(es, fs, ctx, t, m), +rest: Maybe<&2, DC.Link>, hr: OptL(es, fs, ctx, t, rest))
  -> OptL(es, fs, ctx, t, DC.lfirst(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

def lks.go_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>,
  +hr: RP.RepOk(es, fs, ctx, t, DC.Sk.k(s), c, rep), +hro: MG.AllOpenD(es, ctx, rs),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  +rest: Maybe<&2, DC.Link>, hrest: OptL(es, fs, ctx, t, rest)) -> OptL(es, fs, ctx, t, DC.lks.go(f, es, fs, t, s, c, rep, bs, rs, rest)):
  match f:
    case True{}:
      hrest
    case False{}:
      lfirst_ok(DC.lk.c(bs, es, fs, t, s, c, rep), es, fs, ctx, t, lk.c_ok(bs, es, fs, ctx, t, s, c, rep, hr, hk, hz),
        DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest), lfirst_ok(DC.lk.r(rs, es, fs, t, s, c), es, fs, ctx, t, lk.r_ok(rs, es, fs, ctx, t, s, c, hro, hk, hms, hls, hz, hb), rest, hrest))

# the first new link keeps the links' invariants
def lks_ok(cids: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +hro: MG.AllOpenD(es, ctx, rs),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> OptL(es, fs, ctx, t, DC.lks(cids, es, fs, t, s, bs, rs)):
  match cids:
    case Nil{}:
      Unit{}
    case Con{+c, +tl}:
      lks.go_ok(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, c, DC.crep(es, fs, t, s, c), bs, rs, RP.crep_ok(es, fs, ctx, t, s, c, hk, hms, hls, hmsn, hlsn, hz, hb), hro, hk, hms, hls, hz, hb,
        DC.lks(tl, es, fs, t, s, bs, rs), lks_ok(tl, es, fs, ctx, t, s, bs, rs, hro, hk, hms, hls, hmsn, hlsn, hz, hb))
