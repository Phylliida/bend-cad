# bend-cad: the closure theorem at an open node's links into a collapsed
# one (PLAN-sk13b B3, "Turn and through"). A link (c, b) to b with root r
# (not F) gives c the generators w conj(w_b) g, g among r's; pushed through
# r's hull, c's set holds w conj(w_b) y for every y in r's set. So through at
# an open b into c, and turn from an open a into c, follow from the link
# checks. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./identpf.bend as ID
import ./listpf.bend as LP2
import ./labpf.bend as LP
import ./lab.bend as LB
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcopenpf.bend as OP
import ./dcinvpf.bend as IV
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG
import ./dcreppf.bend as RP
import ./dcroundpf.bend as RD
import ./dcsetpf.bend as ST
import ./dcnodepf.bend as ND
import ./labalgpf.bend as LA
import ./labnzpf.bend as NZ
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX
import ./dcreadpf.bend as RF
import ./dclinepf.bend as CL
import ./lspanpf.bend as LS
import ./dcreprpf.bend as RR

import ./dcbelowpf.bend as BL
import ./dcturnpf.bend as TU
import ./dcpushpf.bend as PU

import ./dcturncpf.bend as TC

def absurd(-A: Type, x: Empty) -> A:
  match x:

# A link's generators into c, pushed
# ----------------------------------

def cg_louts(+fs: List<&2, DR.Fact>, +s: DC.Sk, +c: Nat, +g: DR.Der, h: ST.InD(g, DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)))) -> ST.InD(g, DC.cgens(fs, s, c)):
  ST.ind_tl(g, DR.DSelf{DR.NSeg{c}}, DC.dcat(DC.pprems(DC.stats(fs, c, 0n)), DC.dcat(DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c))), ST.ind_cat_r(g, DC.pprems(DC.stats(fs, c, 0n)), DC.dcat(DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c)),
    ST.ind_cat_l(g, DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c), h)))

def lo.m(+fs: List<&2, DR.Fact>, +s: DC.Sk, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +g: DR.Der, embl: {DC.mem_of(DC.Sk.ms(s), bl) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, hrF: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool},
  hg: ST.InD(g, DC.lout.gens(DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), bl, wl, dl, rb, wb, db))) -> ST.InD(g, Con{dl, DC.lout.mem(DC.mem_of(DC.Sk.ms(s), bl), fs, DC.Sk.ms(s), DC.Sk.ls(s), bl, wl, dl)}):
  %Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), bl), Some{DC.Mem{b2, rb, wb, db}}, embl) : ST.InD(g, Con{dl, DC.lout.mem(_, fs, DC.Sk.ms(s), DC.Sk.ls(s), bl, wl, dl)})
  %Equal.sym(Bool, DC.node_eq(rb, DR.NFrame{}), False{}, hrF) : ST.InD(g, Con{dl, DC.lout.root(_, fs, DC.Sk.ms(s), DC.Sk.ls(s), bl, wl, dl, rb, wb, db)})
  ST.ind_tl(g, dl, DC.lout.gens(DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), bl, wl, dl, rb, wb, db), hg)

# a generator h of b's root, through b along the link, rotated into c's set
def lo.gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +embl: {DC.mem_of(DC.Sk.ms(s), bl) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +hrF: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool}, +h: DR.Der, hh: ST.InD(h, DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(LB.lmul(wl, DR.Lab.conj(wb)), DR.Jd.x(DR.concl(es, fs, h)))):
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(DR.Lab.conj(wl)), DR.gmul(DR.Lab.conj(wb), DR.Jd.x(DR.concl(es, fs, h)))), DR.gmul(LB.lmul(wl, DR.Lab.conj(wb)), DR.Jd.x(DR.concl(es, fs, h))), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    ND.gen_coll(es, fs, ctx, t, s, c, PU.lg.at(h, bl, wl, dl, rb, wb, db), cg_louts(fs, s, c, PU.lg.at(h, bl, wl, dl, rb, wb, db), PU.lo_in(DC.Sk.ls(s), n, c, fs, DC.Sk.ms(s), DC.Sk.ls(s), c2, bl, wl, dl, PU.lg.at(h, bl, wl, dl, rb, wb, db), en, ec,
      lo.m(fs, s, bl, wl, dl, b2, rb, wb, db, PU.lg.at(h, bl, wl, dl, rb, wb, db), embl, hrF, PU.lg_in(DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), h, bl, wl, dl, rb, wb, db, hh)))), RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)),
    MG.ccomp(wl, DR.Lab.conj(wb), DR.Jd.x(DR.concl(es, fs, h))))

def ind_ef(+h: DR.Der, +pre: List<&2, DR.Der>, +xt: List<&2, DR.Der>, +full: List<&2, DR.Der>, ef: {DC.dcat(pre, Con{h, xt}) == full : List<&2, DR.Der>}) -> ST.InD(h, full):
  %ef : ST.InD(h, _)
  ST.ind_cat_r(h, pre, Con{h, xt}, ST.ind_hd(h, xt))

def alld_rg(xs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +embl: {DC.mem_of(DC.Sk.ms(s), bl) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +hrF: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool}, +pre: List<&2, DR.Der>, +ef: {DC.dcat(pre, xs) == DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)) : List<&2, DR.Der>}) -> PU.AllD(xs, es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb))):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+h, +xt}:
      (lo.gen(es, fs, ctx, t, s, H, c, n, c2, bl, wl, dl, en, ec, b2, rb, wb, db, embl, hrF, h, ind_ef(h, pre, xt, DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), ef)),
       alld_rg(xt, es, fs, ctx, t, s, H, c, n, c2, bl, wl, dl, en, ec, b2, rb, wb, db, embl, hrF, KS.dsnoc(pre, h), Equal.trans(List<&2, DR.Der>, DC.dcat(KS.dsnoc(pre, h), xt), DC.dcat(pre, Con{h, xt}), DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), PU.dcat_snoc(pre, h, xt), ef)))

# c's set holds w_l conj(w_b) y for every y in b's root's set
def act_lo(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +embl: {DC.mem_of(DC.Sk.ms(s), bl) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +hrF: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool}, +y: SK.VE, hin: ST.HIn(es, fs, rb, DC.rhull(es, fs, t, s, rb), y)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(LB.lmul(wl, DR.Lab.conj(wb)), y)):
  PU.push(DC.rhull(es, fs, t, s, rb), rb, y, es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb)), t, ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), PU.hz0(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb)), DR.zdir(es, rb), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), hin,
    PU.hfold_alld(DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), DC.khull(es, fs, t, DC.Sk.k(s), rb), t, es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb)), alld_rg(DC.rgens(fs, rb, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, ctx, t, s, H, c, n, c2, bl, wl, dl, en, ec, b2, rb, wb, db, embl, hrF, Nil{}, {==}),
      PU.hfold_alld(DC.kgens(rb, KS.ks.ds(DC.Sk.k(s))), HS.hs0(), t, es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb)), PU.alld_kg(KS.ks.ds(DC.Sk.k(s)), es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LB.lmul(wl, DR.Lab.conj(wb)), rb, ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), OP.all_self(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))))), Unit{})))

# Label tools
# -----------

def vone.q(+X: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), X), S.Q.mul(DR.qz(), X)), X):
  QR.qring_eq([X], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QVar{0n}, {==})

def vone(+y: SK.VE) -> VD.SameVD(DR.vlin(DR.qo(), y, DR.qz(), y), y):
  (ID.qzero_ident(SK.VE.x(DR.vlin(DR.qo(), y, DR.qz(), y)), SK.VE.x(y), p => vone.q(E.qeval(p, SK.VE.x(y)))), ID.qzero_ident(SK.VE.y(DR.vlin(DR.qo(), y, DR.qz(), y)), SK.VE.y(y), p => vone.q(E.qeval(p, SK.VE.y(y)))))

# conj(1) acts as 1
def c1g(+y: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(DC.lone()), y), y):
  GN.samevd_tr(DR.gmul(DR.Lab.conj(DC.lone()), y), DR.vlin(DR.qo(), y, DR.qz(), y), y, LA.gmul_realq(DR.qo(), S.Q.neg(DR.qz()), y, Equal.trans(Bool, DR.qnz(S.Q.neg(DR.qz())), DR.qnz(DR.qz()), False{}, LA.qnz_neg(DR.qz()), {==})), vone(y))

# conj(w conj(g)) (w z) = |w|² (g z)
def tchain2(+wa: DR.Lab, +g: DR.Lab, +z: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(wa, z)), DR.vlin(DC.lnorm(wa), DR.gmul(g, z), DR.qz(), DR.gmul(g, z))):
  GN.samevd_tr(DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(wa, z)), DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wa, z))), DR.vlin(DC.lnorm(wa), DR.gmul(g, z), DR.qz(), DR.gmul(g, z)), LA.gconj_mul(wa, DR.Lab.conj(g), DR.gmul(wa, z)), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wa, z))), DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, z))), DR.vlin(DC.lnorm(wa), DR.gmul(g, z), DR.qz(), DR.gmul(g, z)), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wa, z)), DR.gmul(g, DR.gmul(wa, z)), MG.samevd_sym(DR.gmul(g, DR.gmul(wa, z)), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wa, z)), GN.cc(g, DR.gmul(wa, z)))), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, z))), DR.gmul(DR.Lab.conj(wa), DR.gmul(wa, DR.gmul(g, z))), DR.vlin(DC.lnorm(wa), DR.gmul(g, z), DR.qz(), DR.gmul(g, z)), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, z)), DR.gmul(wa, DR.gmul(g, z)), LA.gswap(g, wa, z)), LA.conj_w(wa, DR.gmul(g, z)))))

# The stored labels of (c, b) span every v with v z_b in c's set
# -------------------------------------------------------------

def lsp_cb.b(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +v: DR.Lab, +b: DR.Node, bin: RF.BIn(DC.lstored(DC.Sk.ls(s), c, b), LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b)))), +lb: LS.LSp(LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), v)) -> LS.LSp(LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), v):
  (+b0, +b1) = bin
  LS.lsp_trans(v, LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), lb, b0, b1)

def lsp_cb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +v: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(v, DR.zdir(es, b)))) -> LS.LSp(LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), v):
  lsp_cb.b(es, fs, ctx, t, s, H, c, v, b,
    RF.basis_in(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b), RF.lkc_none(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, b, es, fs, t, s, c, DC.crep(es, fs, t, s, c), PU.lkc.of(c, es, fs, ctx, t, s, H, PU.lkcr(es, fs, ctx, t, s, H, c, emc, hf)),
      RR.btr(q => SH.nmem(q, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}), b2, b, eab, RR.recn_at(DC.Sk.ms(s), nb, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, DC.Mem{b2, rb, wb, db}, enb, SH.sh.rn(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))))), PU.ne_rec(es, fs, ctx, t, s, H, b, c, DC.Mem{b2, rb, wb, db}, emb, emc)),
      SH.pairok_of(DC.Sk.ls(s), c, b, SH.shi.l(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))), SH.lnzs_of(DC.Sk.ls(s), c, b, RR.h.lsn(es, fs, ctx, t, s, H))),
    PU.bc_c(es, fs, ctx, t, s, H, c, DR.zdir(es, b), v, hf, BL.zdir_below(es, t, b, RR.h.z(es, fs, ctx, t, s, H)), hv))

# Through at an open node into collapsed c, b's root not F
# --------------------------------------------------------

def thr.act.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>},
  +ec: {SV.eq(c2, c) == True{} : Bool}, eb: {DC.node_eq(bl, b) == True{} : Bool}, ew: {wl == w : DR.Lab}) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  %ew : ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(_, x2))
  TU.descale(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DC.lnorm(wb), DR.gmul(wl, x2), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(LB.lmul(wl, DR.Lab.conj(wb)), DR.gmul(wb, x2)), DR.vlin(DC.lnorm(wb), DR.gmul(wl, x2), DR.qz(), DR.gmul(wl, x2)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
      act_lo(es, fs, ctx, t, s, H, c, n, c2, bl, wl, dl, en, ec, b2, DR.NSeg{c1}, wb, db, Equal.trans(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), bl), DC.mem_of(DC.Sk.ms(s), b), Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}}, Equal.cong(DR.Node, Maybe<&2, DC.Mem>, q => DC.mem_of(DC.Sk.ms(s), q), bl, b, GN.node_eq_ok(bl, b, eb)), emb), {==}, DR.gmul(wb, x2), hq), TU.unwb(wl, wb, x2)),
    RR.mnz_at(DC.Sk.ms(s), nb, DC.Mem{b2, DR.NSeg{c1}, wb, db}, enb, RR.h.msn(es, fs, ctx, t, s, H)))

def thr.act.k2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>},
  +ec: {SV.eq(c2, c) == True{} : Bool}, r1: SK.Both({DC.node_eq(bl, b) == True{} : Bool}, {wl == w : DR.Lab})) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  (eb, ew) = r1
  thr.act.go(es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, n, c2, bl, wl, dl, en, ec, eb, ew)

def thr.act.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, ok: SK.Both({SV.eq(c2, c) == True{} : Bool}, SK.Both({DC.node_eq(bl, b) == True{} : Bool}, {wl == w : DR.Lab}))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  (+ec, r1) = ok
  thr.act.k2(es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, n, c2, bl, wl, dl, en, ec, r1)

def thr.act.m(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), +n: Nat,
  em: {SH.lat(DC.Sk.ls(s), n) == m : Maybe<&2, DC.Link>}, ok: PU.lk.ok(m, c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  match m:
    case Some{DC.Link{+c2, +bl, +wl, +dl}}:
      thr.act.k(es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, n, c2, bl, wl, dl, em, ok)
    case None{}:
      absurd(ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)), LP.tf(ok))

def thr.act(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), hl: PU.LIn(DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  (+n, +ok) = hl
  thr.act.m(SH.lat(DC.Sk.ls(s), n), es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, n, {==}, ok)

def thr.act.lz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), h: PU.lzor.f(f, DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  match f:
    case True{}:
      %Equal.sym(DR.Lab, w, LS.lab0(), h) : ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(_, x2))
      TC.zinc(es, fs, ctx, t, s, H, c, DR.gmul(LS.lab0(), x2), TU.lzv(LS.lab0(), x2, ({==}, {==})))
    case False{}:
      thr.act(es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, h)

def thr.act.st(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +x2: SK.VE, +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)), hz: PU.LZor(DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, x2)):
  (+f, +h) = hz
  thr.act.lz(f, es, fs, ctx, t, s, H, c, b, w, b2, c1, wb, db, nb, enb, eab, emb, x2, hq, h)

# through at open b (root not F) into collapsed c not in K squared
def thr.co.n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +c1: Nat, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, DR.NSeg{c1}, wb, db}} : Maybe<&2, DC.Mem>}, +emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, +x2: SK.VE, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), +hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(wb, x2)))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), x2)):
  TC.lsp_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), DR.Lab.conj(g), x2, ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), lsp_cb(es, fs, ctx, t, s, H, c, DR.Lab.conj(g), b, b2, DR.NSeg{c1}, wb, db, nb, enb, eab, emb, emc, hf, hv),
    thr.act.st(es, fs, ctx, t, s, H, c, b, LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), b2, c1, wb, db, nb, enb, eab, emb, x2, hq, PU.lat0_of(DC.Sk.ls(s), c, b)), thr.act.st(es, fs, ctx, t, s, H, c, b, LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), b2, c1, wb, db, nb, enb, eab, emb, x2, hq, PU.lat1_of(DC.Sk.ls(s), c, b)))

# Turn from an open node (root not F) into collapsed c
# ----------------------------------------------------

def turn.act.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, eb: {DC.node_eq(bl, DR.NSeg{c1}) == True{} : Bool},
  ew: {wl == w : DR.Lab}) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  %ew : ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(_, DR.gmul(wa, DR.zdir(es, a))))
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(LB.lmul(wl, DR.Lab.conj(DC.lone())), DR.gmul(wa, DR.zdir(es, a))), DR.gmul(wl, DR.gmul(wa, DR.zdir(es, a))), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    act_lo(es, fs, ctx, t, s, H, c, n, c2, bl, wl, dl, en, ec, DR.NSeg{c1}, DR.NSeg{c1}, DC.lone(), DR.DSelf{DR.NSeg{c1}}, Equal.trans(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), bl), DC.mem_of(DC.Sk.ms(s), DR.NSeg{c1}), Some{DC.Mem{DR.NSeg{c1}, DR.NSeg{c1}, DC.lone(), DR.DSelf{DR.NSeg{c1}}}}, Equal.cong(DR.Node, Maybe<&2, DC.Mem>, q => DC.mem_of(DC.Sk.ms(s), q), bl, DR.NSeg{c1}, GN.node_eq_ok(bl, DR.NSeg{c1}, eb)), RR.rootrec(DC.Sk.ms(s), DR.NSeg{c1}, RR.rok_at(DC.Sk.ms(s), na, DC.Sk.ms(s), DC.Mem{a2, DR.NSeg{c1}, wa, da}, ena, SH.sh.ro(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H)))), SH.sh.rr(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))))), {==}, DR.gmul(wa, DR.zdir(es, a)), RR.self.go(es, fs, ctx, t, s, H, a, a2, DR.NSeg{c1}, wa, da, na, ena, eaa)),
    GN.samevd_tr(DR.gmul(LB.lmul(wl, DR.Lab.conj(DC.lone())), DR.gmul(wa, DR.zdir(es, a))), DR.gmul(wl, DR.gmul(DR.Lab.conj(DC.lone()), DR.gmul(wa, DR.zdir(es, a)))), DR.gmul(wl, DR.gmul(wa, DR.zdir(es, a))), MG.samevd_sym(DR.gmul(wl, DR.gmul(DR.Lab.conj(DC.lone()), DR.gmul(wa, DR.zdir(es, a)))), DR.gmul(LB.lmul(wl, DR.Lab.conj(DC.lone())), DR.gmul(wa, DR.zdir(es, a))), MG.compd(wl, DR.Lab.conj(DC.lone()), DR.gmul(wa, DR.zdir(es, a)))), MG.gmul_cong(wl, DR.gmul(DR.Lab.conj(DC.lone()), DR.gmul(wa, DR.zdir(es, a))), DR.gmul(wa, DR.zdir(es, a)), c1g(DR.gmul(wa, DR.zdir(es, a))))))

def turn.act.k2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, r1: SK.Both({DC.node_eq(bl, DR.NSeg{c1}) == True{} : Bool}, {wl == w : DR.Lab})) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  (eb, ew) = r1
  turn.act.go(es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, n, c2, bl, wl, dl, en, ec, eb, ew)

def turn.act.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, ok: SK.Both({SV.eq(c2, c) == True{} : Bool}, SK.Both({DC.node_eq(bl, DR.NSeg{c1}) == True{} : Bool}, {wl == w : DR.Lab}))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  (+ec, r1) = ok
  turn.act.k2(es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, n, c2, bl, wl, dl, en, ec, r1)

def turn.act.m(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +n: Nat, em: {SH.lat(DC.Sk.ls(s), n) == m : Maybe<&2, DC.Link>}, ok: PU.lk.ok(m, c, DR.NSeg{c1}, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  match m:
    case Some{DC.Link{+c2, +bl, +wl, +dl}}:
      turn.act.k(es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, n, c2, bl, wl, dl, em, ok)
    case None{}:
      absurd(ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))), LP.tf(ok))

def turn.act(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, hl: PU.LIn(DC.Sk.ls(s), c, DR.NSeg{c1}, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  (+n, +ok) = hl
  turn.act.m(SH.lat(DC.Sk.ls(s), n), es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, n, {==}, ok)

def turn.act.lz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, h: PU.lzor.f(f, DC.Sk.ls(s), c, DR.NSeg{c1}, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  match f:
    case True{}:
      %Equal.sym(DR.Lab, w, LS.lab0(), h) : ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(_, DR.gmul(wa, DR.zdir(es, a))))
      TC.zinc(es, fs, ctx, t, s, H, c, DR.gmul(LS.lab0(), DR.gmul(wa, DR.zdir(es, a))), TU.lzv(LS.lab0(), DR.gmul(wa, DR.zdir(es, a)), ({==}, {==})))
    case False{}:
      turn.act(es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, h)

def turn.act.st(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +a: DR.Node, +w: DR.Lab, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, hz: PU.LZor(DC.Sk.ls(s), c, DR.NSeg{c1}, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(w, DR.gmul(wa, DR.zdir(es, a)))):
  (+f, +h) = hz
  turn.act.lz(f, es, fs, ctx, t, s, H, c, a, w, a2, c1, wa, da, na, ena, eaa, h)

def turn.oc.l(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +a: DR.Node, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +lst: LS.LSp(LS.lat0(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), LS.lat1(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(g, DR.zdir(es, a))):
  TU.descale(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DC.lnorm(wa), DR.gmul(g, DR.zdir(es, a)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(wa, DR.zdir(es, a))), DR.vlin(DC.lnorm(wa), DR.gmul(g, DR.zdir(es, a)), DR.qz(), DR.gmul(g, DR.zdir(es, a))), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
      TC.lsp_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), LS.lat0(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), LS.lat1(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(wa, DR.zdir(es, a)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), lst,
        turn.act.st(es, fs, ctx, t, s, H, c, a, LS.lat0(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), a2, c1, wa, da, na, ena, eaa, PU.lat0_of(DC.Sk.ls(s), c, DR.NSeg{c1})), turn.act.st(es, fs, ctx, t, s, H, c, a, LS.lat1(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), a2, c1, wa, da, na, ena, eaa, PU.lat1_of(DC.Sk.ls(s), c, DR.NSeg{c1}))),
      tchain2(wa, g, DR.zdir(es, a))),
    RR.mnz_at(DC.Sk.ms(s), na, DC.Mem{a2, DR.NSeg{c1}, wa, da}, ena, RR.h.msn(es, fs, ctx, t, s, H)))

def turn.oc.b(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +a: DR.Node, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, bin: RF.BIn(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1}), DR.Lab.conj(LS.lat0(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})))), DR.Lab.conj(LS.lat1(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}))))), +lb: LS.LSp(LS.lat0(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}))), LS.lat1(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}))), LB.lmul(wa, DR.Lab.conj(g)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(g, DR.zdir(es, a))):
  (+b0, +b1) = bin
  turn.oc.l(es, fs, ctx, t, s, H, c, g, a, a2, c1, wa, da, na, ena, eaa, LS.lsp_trans(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.Lab.conj(LS.lat0(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})))), DR.Lab.conj(LS.lat1(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})))), LS.lat0(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), LS.lat1(DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1})), LS.lsp_conj(LB.lmul(wa, DR.Lab.conj(g)), LS.lat0(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}))), LS.lat1(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}))), lb), b0, b1))

# turn from open a (root not F) into collapsed c not in K squared
def turn.oc.n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +a: DR.Node, +a2: DR.Node, +c1: Nat, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, DR.NSeg{c1}, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, DR.NSeg{c1}), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(g, DR.zdir(es, a))):
  turn.oc.b(es, fs, ctx, t, s, H, c, g, a, a2, c1, wa, da, na, ena, eaa,
    RF.basis_inc(DC.basis.free(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), DC.lstored(DC.Sk.ls(s), c, DR.NSeg{c1}), RF.lkr_none(DC.roots(DC.Sk.ms(s)), DR.NSeg{c1}, es, fs, t, s, c, PU.lkr.of(c, es, fs, ctx, t, s, H, PU.lkcr(es, fs, ctx, t, s, H, c, emc, hf)), RR.root_nmem(es, fs, ctx, t, s, H, na, a2, DR.NSeg{c1}, wa, da, ena)),
      SH.pairok_of(DC.Sk.ls(s), c, DR.NSeg{c1}, SH.shi.l(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))), SH.lnzs_of(DC.Sk.ls(s), c, DR.NSeg{c1}, RR.h.lsn(es, fs, ctx, t, s, H))),
    LS.bfree_ok(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c})), es, fs, ctx, DR.NSeg{c1}, t, DC.Sk.k(s), DC.rhull(es, fs, t, s, DR.NSeg{c1}), DR.zdir(es, DR.NSeg{c}), {==}, GN.rhull_inv(es, fs, ctx, t, s, DR.NSeg{c1}, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)),
      BL.zdir_below(es, t, DR.NSeg{c1}, RR.h.z(es, fs, ctx, t, s, H)), BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H)), LB.lmul(wa, DR.Lab.conj(g)), hv))
