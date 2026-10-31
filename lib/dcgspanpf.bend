# bend-cad: everything K gets is in the bases' span (PLAN-sk13b B3,
# termination). Every node's direction is (vs_zdir: F's and the sketch
# segments' are bases, and any other segment's is 0). So is every form the
# closure's generators prove: a member record's is a rotation of its
# node's direction, a statement's is a fact's form rotated, a link turned
# and passed through is a rotation of a direction, and K squared's are
# K's generators (rgens_vs, kgens_vs, kept by hull folds and chains). So a
# frame-back or complex-line fact is in the span (fback_s, clxs_s), and K's
# generators stay in it (KSpan: kinit_span, ks_add_span). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./listpf.bend as LP2
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS
import ./spanpf.bend as SN
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcgenpf.bend as GN
import ./dcshapepf.bend as SH
import ./dcreprpf.bend as RR
import ./dcbasepf.bend as BS
import ./dckslpf.bend as KL
import ./pair.bend as PT
import ./drvpf.bend as DV

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Directions
# ----------

def vs_catr(+A: List<&2, E.QExpr>, +C: List<&2, E.QExpr>, +x: SK.VE, +h: BS.VS(x, C)) -> BS.VS(x, DC.qcat(A, C)):
  (BS.in_catr(A, C, SK.VE.x(x), BS.vs.x(x, C, h)), BS.in_catr(A, C, SK.VE.y(x), BS.vs.y(x, C, h)))

def vs_dn.hd(+es: List<&2, SK.Ent>, +h0: DR.Node, +t: List<&2, DR.Node>) -> BS.VS(DR.zdir(es, h0), DC.dbases(es, Con{h0, t})):
  (BS.in_hd(SK.VE.x(DR.zdir(es, h0)), Con{SK.VE.y(DR.zdir(es, h0)), DC.dbases(es, t)}),
   BS.in_tl(SK.VE.y(DR.zdir(es, h0)), SK.VE.x(DR.zdir(es, h0)), Con{SK.VE.y(DR.zdir(es, h0)), DC.dbases(es, t)}, BS.in_hd(SK.VE.y(DR.zdir(es, h0)), DC.dbases(es, t))))

def vs_dn.go(g: Bool, +es: List<&2, SK.Ent>, +n: DR.Node, +h0: DR.Node, +t: List<&2, DR.Node>, eg: {g == DC.node_eq(n, h0) : Bool}, h: {SV.bor(g, SH.nmem(n, t)) == True{} : Bool},
  ih: {SH.nmem(n, t) == True{} : Bool} -> BS.VS(DR.zdir(es, n), DC.dbases(es, t))) -> BS.VS(DR.zdir(es, n), DC.dbases(es, Con{h0, t})):
  match g:
    case True{}:
      %Equal.sym(DR.Node, n, h0, GN.node_eq_ok(n, h0, Equal.sym(Bool, True{}, DC.node_eq(n, h0), eg))) : BS.VS(DR.zdir(es, _), DC.dbases(es, Con{h0, t}))
      vs_dn.hd(es, h0, t)
    case False{}:
      BS.vs_tl(DR.zdir(es, n), SK.VE.x(DR.zdir(es, h0)), Con{SK.VE.y(DR.zdir(es, h0)), DC.dbases(es, t)}, BS.vs_tl(DR.zdir(es, n), SK.VE.y(DR.zdir(es, h0)), DC.dbases(es, t), ih(h)))

# a listed node's direction is in its bases' span
def vs_dn(+es: List<&2, SK.Ent>, ns: List<&2, DR.Node>, +n: DR.Node, h: {SH.nmem(n, ns) == True{} : Bool}) -> BS.VS(DR.zdir(es, n), DC.dbases(es, ns)):
  match ns:
    case Nil{}:
      absurd(BS.VS(DR.zdir(es, n), Nil{}), KA.ft(h))
    case Con{+h0, +t}:
      vs_dn.go(DC.node_eq(n, h0), es, n, h0, t, {==}, h, x => vs_dn(es, t, n, x))

def vs_z0(+B: List<&2, E.QExpr>) -> BS.VS(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}}), B):
  ((Nil{}, {==}), (Nil{}, {==}))

def vs_zseg.g(g: SK.Geo, +es: List<&2, SK.Ent>, +c: Nat, eg: {SK.find(c, es) == Some{g} : Maybe<&2, SK.Geo>}) -> BS.VS(DR.zseg(es, c), DC.dbases(es, DC.snodes(DC.segids(es)))):
  match g:
    case SK.GSeg{+p, +q}:
      vs_dn(es, DC.snodes(DC.segids(es)), DR.NSeg{c}, RR.seg_in(es, c, p, q, eg))
    case SK.GPoint{+x, +y}:
      %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GPoint{x, y}}, eg) : BS.VS(SK.Seg.dir(SK.seg.of(es, _)), DC.dbases(es, DC.snodes(DC.segids(es))))
      vs_z0(DC.dbases(es, DC.snodes(DC.segids(es))))
    case SK.GCirc{+cc, +r}:
      %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GCirc{cc, r}}, eg) : BS.VS(SK.Seg.dir(SK.seg.of(es, _)), DC.dbases(es, DC.snodes(DC.segids(es))))
      vs_z0(DC.dbases(es, DC.snodes(DC.segids(es))))
    case SK.GArc{+a, +e, +b}:
      %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GArc{a, e, b}}, eg) : BS.VS(SK.Seg.dir(SK.seg.of(es, _)), DC.dbases(es, DC.snodes(DC.segids(es))))
      vs_z0(DC.dbases(es, DC.snodes(DC.segids(es))))

def vs_zseg.m(mg: Maybe<&2, SK.Geo>, +es: List<&2, SK.Ent>, +c: Nat, eg: {SK.find(c, es) == mg : Maybe<&2, SK.Geo>}) -> BS.VS(DR.zseg(es, c), DC.dbases(es, DC.snodes(DC.segids(es)))):
  match mg:
    case None{}:
      %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), None{}, eg) : BS.VS(SK.Seg.dir(SK.seg.of(es, _)), DC.dbases(es, DC.snodes(DC.segids(es))))
      vs_z0(DC.dbases(es, DC.snodes(DC.segids(es))))
    case Some{+g}:
      vs_zseg.g(g, es, c, eg)

def bases_d(+es: List<&2, SK.Ent>) -> List<&2, E.QExpr>:
  DC.dbases(es, Con{DR.NFrame{}, DC.snodes(DC.segids(es))})

# every node's direction is in the bases' span
def vs_zdir(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, n: DR.Node) -> BS.VS(DR.zdir(es, n), DC.bases(es, fs)):
  match n:
    case DR.NFrame{}:
      vs_catr(DC.fbases(fs), bases_d(es), DR.zdir(es, DR.NFrame{}), vs_dn.hd(es, DR.NFrame{}, DC.snodes(DC.segids(es))))
    case DR.NSeg{+c}:
      vs_catr(DC.fbases(fs), bases_d(es), DR.zseg(es, c),
        BS.vs_tl(DR.zseg(es, c), SK.VE.x(DR.zdir(es, DR.NFrame{})), Con{SK.VE.y(DR.zdir(es, DR.NFrame{})), DC.dbases(es, DC.snodes(DC.segids(es)))},
          BS.vs_tl(DR.zseg(es, c), SK.VE.y(DR.zdir(es, DR.NFrame{})), DC.dbases(es, DC.snodes(DC.segids(es))), vs_zseg.m(SK.find(c, es), es, c, {==}))))

# Generator lists
# ---------------

def AllVS(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, tl}:
      SK.Both(BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs)), AllVS(tl, es, fs))

def allvs_dcat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hx: AllVS(xs, es, fs), hy: AllVS(ys, es, fs)) -> AllVS(DC.dcat(xs, ys), es, fs):
  match xs:
    case Nil{}:
      hy
    case Con{+x, +t}:
      (a, b) = hx
      (a, allvs_dcat(t, ys, es, fs, b, hy))

def allvs_dpick(b: Bool, +x: DR.Der, +rest: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hx: BS.VS(DR.Jd.x(DR.concl(es, fs, x)), DC.bases(es, fs)), hr: AllVS(rest, es, fs))
  -> AllVS(DC.dpick(b, x, rest), es, fs):
  match b:
    case True{}:
      (hx, hr)
    case False{}:
      hr

def allvs_dcatif(b: Bool, +xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hx: AllVS(xs, es, fs), hy: AllVS(ys, es, fs)) -> AllVS(DC.dcatif(b, xs, ys), es, fs):
  match b:
    case True{}:
      allvs_dcat(xs, ys, es, fs, hx, hy)
    case False{}:
      hy

def allvs_snoc(ds: List<&2, DR.Der>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: AllVS(ds, es, fs), hd: BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs))) -> AllVS(KS.dsnoc(ds, d), es, fs):
  match ds:
    case Nil{}:
      (hd, Unit{})
    case Con{+x, +t}:
      (a, b) = h
      (a, allvs_snoc(t, d, es, fs, b, hd))

def allvs_ddrop(n: Nat, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: AllVS(ds, es, fs)) -> AllVS(DC.ddrop(n, ds), es, fs):
  match n ds:
    case 0n ds:
      h
    case 1n+m Nil{}:
      Unit{}
    case 1n+m Con{+d, +t}:
      (a, b) = h
      allvs_ddrop(m, t, es, fs, b)

# The roots' generators
# ---------------------

def allvs_pprems(ix: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> AllVS(DC.pprems(ix), es, fs):
  match ix:
    case Nil{}:
      Unit{}
    case Con{+i, +t}:
      (BS.fs_in(fs, i, bases_d(es)), allvs_pprems(t, es, fs))

def allvs_lstats(ps: List<&2, DR.Der>, +a: DR.Node, +w: DR.Lab, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: AllVS(ps, es, fs)) -> AllVS(DC.lstats(ps, a, w, d), es, fs):
  match ps:
    case Nil{}:
      Unit{}
    case Con{+p, +t}:
      (hp, ht) = h
      (BS.vs_gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.Jd.x(DR.concl(es, fs, p)), DC.bases(es, fs), hp), allvs_lstats(t, a, w, d, es, fs, ht))

def allvs_llinks(ls: List<&2, DC.Link>, +a: DR.Node, +w: DR.Lab, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> AllVS(DC.llinks(ls, a, w, d), es, fs):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c, +b, +wl, +dl}, +t}:
      allvs_dpick(DC.node_eq(b, a), DC.thr(d, w, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), DC.llinks(t, a, w, d), es, fs,
        BS.vs_gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl)))), DC.bases(es, fs),
          BS.vs_gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))), DC.bases(es, fs), vs_zdir(es, fs, DR.Jd.a(DR.concl(es, fs, dl))))),
        allvs_llinks(t, a, w, d, es, fs))

# a member record's own form
def mrec_vs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, h: GN.MOkD(es, fs, ctx, t, DC.Mem{a, r, w, d}))
  -> BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs)):
  (h1, r1) = h
  (h2, r2) = r1
  (h3, r3) = r2
  (h4, r4) = r3
  BS.vs_tr(DR.gmul(w, DR.zdir(es, a)), DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs), BS.vs_gmul(w, DR.zdir(es, a), DC.bases(es, fs), vs_zdir(es, fs, a)), h4)

def allvs_mgens(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ls: List<&2, DC.Link>, m: DC.Mem, h: GN.MOkD(es, fs, ctx, t, m)) -> AllVS(DC.mgens(fs, ls, m), es, fs):
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      (mrec_vs(es, fs, ctx, t, a, r, w, d, h),
       allvs_dcat(DC.lstats(DC.pprems(DC.nstats(fs, a)), a, w, d), DC.llinks(ls, a, w, d), es, fs,
         allvs_lstats(DC.pprems(DC.nstats(fs, a)), a, w, d, es, fs, allvs_pprems(DC.nstats(fs, a), es, fs)), allvs_llinks(ls, a, w, d, es, fs)))

# a root's generators are in the bases' span
def allvs_rgens(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>, h: GN.MsOk(es, fs, ctx, t, ms))
  -> AllVS(DC.rgens(fs, r, ms, ls), es, fs):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m, +tl}:
      (hm, ht) = h
      allvs_dcatif(DC.node_eq(DC.Mem.r(m), r), DC.mgens(fs, ls, m), DC.rgens(fs, r, tl, ls), es, fs, allvs_mgens(es, fs, ctx, t, ls, m, hm), allvs_rgens(es, fs, ctx, t, r, tl, ls, ht))

# K squared's generators
def allvs_kgens(+r: DR.Node, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: KL.AllIn(KS.kexprs(es, fs, ds), DC.bases(es, fs))) -> AllVS(DC.kgens(r, ds), es, fs):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (+hd, ht) = h
      (BS.vs_add(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), SK.VE{DR.Jd.e(DR.concl(es, fs, d)), DR.zeroe()}, DC.bases(es, fs),
         BS.vs_vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), DC.bases(es, fs), vs_zdir(es, fs, r), vs_zdir(es, fs, r)), (hd, SN.in_zero(DC.bases(es, fs)))),
       (BS.vs_add(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), SK.VE{DR.zeroe(), DR.Jd.e(DR.concl(es, fs, d))}, DC.bases(es, fs),
          BS.vs_vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), DC.bases(es, fs), vs_zdir(es, fs, r), vs_zdir(es, fs, r)), (SN.in_zero(DC.bases(es, fs)), hd)),
        allvs_kgens(r, tl, es, fs, ht)))

def hadd_vs.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +rr: EL.Res, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: AllVS(ds, es, fs),
  hd: BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs))) -> AllVS(HS.hs.ds(HS.hs.pick(b, rows, ds, rr, d)), es, fs):
  match b:
    case True{}:
      h
    case False{}:
      allvs_snoc(ds, d, es, fs, h, hd)

def hadd_vs(h: HS.HS, +t: Nat, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hh: AllVS(HS.hs.ds(h), es, fs), hd: BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs)))
  -> AllVS(HS.hs.ds(HS.hs.add(es, fs, t, h, d)), es, fs):
  match h:
    case HS.HS{+rows, +ds}:
      hadd_vs.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d, es, fs, hh, hd)

# a hull fold keeps only generators it was given
def hfold_vs(gs: List<&2, DR.Der>, +h: HS.HS, +t: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hg: AllVS(gs, es, fs), hh: AllVS(HS.hs.ds(h), es, fs))
  -> AllVS(HS.hs.ds(DC.hfold(gs, es, fs, t, h)), es, fs):
  match gs:
    case Nil{}:
      hh
    case Con{+g, +tl}:
      (a, b) = hg
      hfold_vs(tl, HS.hs.add(es, fs, t, h, g), t, es, fs, b, hadd_vs(h, t, g, es, fs, hh, a))

# a root's hull
def rhull_vs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  hk: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), DC.bases(es, fs))) -> AllVS(HS.hs.ds(DC.rhull(es, fs, t, s, r)), es, fs):
  hfold_vs(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), DC.khull(es, fs, t, DC.Sk.k(s), r), t, es, fs, allvs_rgens(es, fs, ctx, t, r, DC.Sk.ms(s), DC.Sk.ls(s), hm),
    hfold_vs(DC.kgens(r, KS.ks.ds(DC.Sk.k(s))), HS.hs0(), t, es, fs, allvs_kgens(r, KS.ks.ds(DC.Sk.k(s)), es, fs, hk), Unit{}))

def pchain_vs.pick(b: Bool, +r: DR.Node, +l: S.Q, +d: DR.Der, +rest: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hd: BS.VS(DR.Jd.x(DR.concl(es, fs, d)), DC.bases(es, fs)), ih: BS.VS(DR.Jd.x(DR.concl(es, fs, rest)), DC.bases(es, fs)))
  -> BS.VS(DR.Jd.x(DR.concl(es, fs, HS.pc.pick(b, l, d, rest))), DC.bases(es, fs)):
  match b:
    case True{}:
      BS.vs_vlin(l, DR.Jd.x(DR.concl(es, fs, d)), DR.qo(), DR.Jd.x(DR.concl(es, fs, rest)), DC.bases(es, fs), hd, ih)
    case False{}:
      ih

def pchain_vs(+r: DR.Node, ls: List<&2, S.Q>, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: AllVS(ds, es, fs))
  -> BS.VS(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), DC.bases(es, fs)):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (hd, ht) = h
      pchain_vs.pick(DR.qnz(l), r, l, d, HS.pchain(r, lt, dt), es, fs, hd, pchain_vs(r, lt, dt, es, fs, ht))
    case Nil{} ds:
      BS.vs_vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), DC.bases(es, fs), vs_zdir(es, fs, r), vs_zdir(es, fs, r))
    case Con{l, lt} Nil{}:
      BS.vs_vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r), DC.bases(es, fs), vs_zdir(es, fs, r), vs_zdir(es, fs, r))

# New K facts
# -----------

# a new K fact, if any, is in the bases' span
def OptS(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, m: Maybe<&2, DR.Der>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{+d}:
      SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), DC.bases(es, fs))

def fbp_s(b: Bool, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hg: BS.VS(DR.Jd.x(DR.concl(es, fs, g)), DC.bases(es, fs)), +rest: Maybe<&2, DR.Der>, hr: OptS(es, fs, rest))
  -> OptS(es, fs, DC.mpick2(b, DR.DBack{g}, rest)):
  match b:
    case True{}:
      BS.vs.y(DR.Jd.x(DR.concl(es, fs, g)), DC.bases(es, fs), hg)
    case False{}:
      hr

def fback_s(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, h: AllVS(gs, es, fs)) -> OptS(es, fs, DC.fback(gs, es, fs, k)):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +tl}:
      (hg, ht) = h
      fbp_s(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), g, es, fs, hg, DC.fback(tl, es, fs, k), fback_s(tl, es, fs, k, ht))

def dline_s(re: Bool, +x: SK.VE, +B: List<&2, E.QExpr>, +h: BS.VS(x, B)) -> SN.InSpan(DR.dline.e(re, x), B):
  match re:
    case True{}:
      BS.vs.x(x, B, h)
    case False{}:
      BS.vs.y(x, B, h)

def clk_s(b: Bool, +px: DR.Der, +d2: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +h: BS.VS(DR.Jd.x(DR.concl(es, fs, px)), DC.bases(es, fs)))
  -> SN.InSpan(DR.Jd.e(DR.concl(es, fs, DC.cl.k(b, px, d2))), DC.bases(es, fs)):
  match b:
    case True{}:
      dline_s(False{}, DR.Jd.x(DR.concl(es, fs, px)), DC.bases(es, fs), h)
    case False{}:
      dline_s(True{}, DR.Jd.x(DR.concl(es, fs, px)), DC.bases(es, fs), h)

def clp_s(b: Bool, +found: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hf: SN.InSpan(DR.Jd.e(DR.concl(es, fs, found)), DC.bases(es, fs)), +rest: Maybe<&2, DR.Der>, hr: OptS(es, fs, rest))
  -> OptS(es, fs, DC.cl.pick(b, found, rest)):
  match b:
    case True{}:
      hf
    case False{}:
      hr

def clgo_s(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>,
  hd: AllVS(ds, es, fs), +hp: AllVS(prev, es, fs)) -> OptS(es, fs, DC.cl.go(ds, es, fs, t, r, h, k, rows2, bb, prev)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (+h0, ht) = hd
      +e = HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)
      +res = EL.resid(rows2, e)
      +lsI = PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)), DV.dropls(DV.rescb(res), DV.resbt(res), e, bb))
      +px = {DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)} : DR.Der}
      clp_s(EP.isnil(EP.resp(res)), DC.cl.found(es, fs, t, r, h, k, d, res, e, bb, prev), es, fs,
        clk_s(KS.ks.inb(k, SK.VE.x(DR.Jd.x(DR.concl(es, fs, px)))), px, HS.hs.der(es, fs, t, r, h, DR.imul(DR.Jd.x(DR.concl(es, fs, px)))), es, fs,
          BS.vs_vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev))), DC.bases(es, fs), h0, pchain_vs(r, lsI, prev, es, fs, hp))),
        DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d)),
        clgo_s(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d), ht, allvs_snoc(prev, d, es, fs, hp, h0)))

def clx_s(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  hk: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), DC.bases(es, fs))) -> OptS(es, fs, DC.clx(es, fs, t, s, r)):
  clgo_s(DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))), es, fs, t, r, DC.rhull(es, fs, t, s, r), DC.Sk.k(s),
    HS.hs.rows(DC.rhull(es, fs, t, s, r)), HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t), Nil{},
    allvs_ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)), es, fs, rhull_vs(es, fs, ctx, t, s, r, hm, hk)), Unit{})

def clxs.pick_s(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hm: OptS(es, fs, m), +rest: Maybe<&2, DR.Der>, hr: OptS(es, fs, rest)) -> OptS(es, fs, DC.clxs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+d}:
      hm

def clxs.if_s(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  +hk: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), DC.bases(es, fs)), +rest: Maybe<&2, DR.Der>, hr: OptS(es, fs, rest)) -> OptS(es, fs, DC.clxs.if(f, es, fs, t, s, r, rest)):
  match f:
    case True{}:
      clxs.pick_s(DC.clx(es, fs, t, s, r), es, fs, clx_s(es, fs, ctx, t, s, r, hm, hk), rest, hr)
    case False{}:
      hr

# a complex line's K fact is in the bases' span
def clxs_s(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  +hk: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), DC.bases(es, fs))) -> OptS(es, fs, DC.clxs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      clxs.if_s(SV.bnot(DC.node_eq(r, DR.NFrame{})), es, fs, ctx, t, s, r, hm, hk, DC.clxs(tl, es, fs, t, s), clxs_s(tl, es, fs, ctx, t, s, hm, hk))

# K's generators
# --------------

def KSpan(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS.KS) -> Data:
  KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), DC.bases(es, fs))

def ks_add_span.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +rr: EL.Res, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>,
  h: KL.AllIn(KS.kexprs(es, fs, ds), DC.bases(es, fs)), hd: SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), DC.bases(es, fs))) -> KSpan(es, fs, KS.ks.pick(b, rows, ds, rr, d)):
  match b:
    case True{}:
      h
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, KS.kexprs(es, fs, KS.dsnoc(ds, d)), EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), KP.kexprs_snoc(es, fs, ds, d)) : KL.AllIn(_, DC.bases(es, fs))
      KL.allin_snoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d)), DC.bases(es, fs), h, hd)

# adding a generator in the span keeps K's in it
def ks_add_span(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS.KS, +d: DR.Der, h: KSpan(es, fs, k), hd: SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), DC.bases(es, fs)))
  -> KSpan(es, fs, KS.ks.add(es, fs, k, d)):
  match k:
    case KS.KS{+rows, +ds}:
      ks_add_span.pick(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d, es, fs, h, hd)

# the facts' K is in the span
def kinit_span(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, h: KSpan(es, fs, k)) -> KSpan(es, fs, DC.kinit(es, fs, rest, i, k)):
  match rest:
    case Nil{}:
      h
    case Con{+f, +tl}:
      kinit_span(tl, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), ks_add_span(es, fs, k, DR.DPrem{i}, h, BS.fe_in(fs, i, bases_d(es))))
