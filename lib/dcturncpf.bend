# bend-cad: the closure theorem's turn rule at collapsed nodes (PLAN-sk13b
# B3, "Turn and through"). From collapsed c to an open b: the link check
# puts conj(g) in the span of the stored labels of (c, b), and each stored
# link's turn is a generator at b, so w_b g z_c is in b's root's set. Between
# collapsed c and c1: the same with the turns into c1; at the same node,
# g z = 2 Re(g) z - conj(g) z. A node whose direction is in K squared
# makes it trivial. Proofs only.

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

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Tools
# -----

def cseg.g(g: SK.Geo, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +eg: {SK.find(c, es) == Some{g} : Maybe<&2, SK.Geo>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}:
  match g:
    case SK.GPoint{+x, +y}:
      absurd({SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}, PU.nf(es, DC.Sk.k(s), c, PU.fz.p(es, fs, ctx, t, s, H, c, x, y, eg), hf))
    case SK.GSeg{+p, +q}:
      RR.seg_in(es, c, p, q, eg)
    case SK.GCirc{+x, +y}:
      absurd({SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}, PU.nf(es, DC.Sk.k(s), c, PU.fz.c(es, fs, ctx, t, s, H, c, x, y, eg), hf))
    case SK.GArc{+x, +y, +z}:
      absurd({SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}, PU.nf(es, DC.Sk.k(s), c, PU.fz.a(es, fs, ctx, t, s, H, c, x, y, z, eg), hf))

def cseg.m(mg: Maybe<&2, SK.Geo>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, eg: {SK.find(c, es) == mg : Maybe<&2, SK.Geo>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}:
  match mg:
    case Some{+g}:
      cseg.g(g, es, fs, ctx, t, s, H, c, eg, hf)
    case None{}:
      absurd({SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}, PU.nf(es, DC.Sk.k(s), c, PU.fz.n(es, fs, ctx, t, s, H, c, eg), hf))

# a node not in K squared is a sketch segment
def cseg(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {SH.nmem(DR.NSeg{c}, DC.snodes(DC.segids(es))) == True{} : Bool}:
  cseg.m(SK.find(c, es), es, fs, ctx, t, s, H, c, {==}, hf)

def nb2(+bl: DR.Node, +b: DR.Node, +b2: DR.Node, eab: {b2 == b : DR.Node}, eb: {DC.node_eq(bl, b) == True{} : Bool}) -> {DC.node_eq(bl, b2) == True{} : Bool}:
  %Equal.sym(DR.Node, b2, b, eab) : {DC.node_eq(bl, _) == True{} : Bool}
  eb

# K squared, rotated twice, is in a root's set
def k2rr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, +l1: DR.Lab, +l2: DR.Lab, +y: SK.VE, +hx: {KS.ks.inb(DC.Sk.k(s), SK.VE.x(y)) == True{} : Bool}, +hy: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(y)) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(l1, DR.gmul(l2, y))):
  PU.k2r(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), l1, DR.gmul(l2, y), ND.sok_root(es, fs, ctx, t, s, r, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
    RR.k2b.x(es, fs, DC.Sk.k(s), DR.gmul(l2, y), RR.k2_gmul(l2, es, fs, DC.Sk.k(s), y, ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), hx, hy)), RR.k2b.y(es, fs, DC.Sk.k(s), DR.gmul(l2, y), RR.k2_gmul(l2, es, fs, DC.Sk.k(s), y, ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), hx, hy)))

# a form the same as 0 is in a collapsed set
def zinc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +y: SK.VE, +sv: VD.SameVD(y, DR.zerov())) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), y):
  ND.k2_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), y, ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.x(y), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), RR.svx(DR.zerov(), y, MG.samevd_sym(y, DR.zerov(), sv))),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.y(y), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), RR.svy(DR.zerov(), y, MG.samevd_sym(y, DR.zerov(), sv))))

# a label in the span of two whose rotations of y are in a set: so is its rotation
def lsp_in(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab, +y: SK.VE, +ok: ST.StOk(es, fs, t, k, st),
  +hs: LS.LSp(u0, u1, v), h0: ST.InSt(es, fs, k, st, DR.gmul(u0, y)), h1: ST.InSt(es, fs, k, st, DR.gmul(u1, y))) -> ST.InSt(es, fs, k, st, DR.gmul(v, y)):
  ST.st_tr(es, fs, t, k, st, DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, y), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, y)), DR.gmul(v, y), ok,
    ST.st_lin(es, fs, t, k, st, LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, y), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, y), ok, h0, h1),
    MG.samevd_sym(DR.gmul(v, y), DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, y), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, y)), LS.lsp_form(u0, u1, v, hs, y)))

# the same, behind a rotation w
def lsp_inw(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, +w: DR.Lab, +u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab, +z: SK.VE, +hs: LS.LSp(u0, u1, v),
  h0: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.gmul(u0, z))), h1: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.gmul(u1, z)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.gmul(v, z))):
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u0, z)), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u1, z))), DR.gmul(w, DR.gmul(v, z)), RR.rok(r, es, fs, ctx, t, s, H),
    ST.st_lin(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u0, z)), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u1, z)), RR.rok(r, es, fs, ctx, t, s, H), h0, h1),
    MG.samevd_sym(DR.gmul(w, DR.gmul(v, z)), DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u0, z)), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u1, z))), GN.samevd_tr(DR.gmul(w, DR.gmul(v, z)), DR.gmul(w, DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, z), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, z))), DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u0, z)), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(w, DR.gmul(u1, z))), MG.gmul_cong(w, DR.gmul(v, z), DR.vlin(LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, z), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, z)), LS.lsp_form(u0, u1, v, hs, z)), LA.gmul_vlin(w, LA.lab.c(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u0, z), LA.lab.s(LS.lsp.p(u0, u1, v, hs)), DR.gmul(u1, z)))))

# Turn from a collapsed node to an open one
# -----------------------------------------

def act_ll.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, ec: {SV.eq(c2, c) == True{} : Bool}, eb: {DC.node_eq(bl, b) == True{} : Bool}, ew: {wl == w : DR.Lab})
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  %ew : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(_), DR.zdir(es, DR.NSeg{c}))))
  %LP2.eq_ok(c2, c, ec) : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.NSeg{_}))))
  %PU.lok.a(es, fs, ctx, t, c2, bl, wl, dl, PU.lok_at(DC.Sk.ls(s), n, es, fs, ctx, t, DC.Link{c2, bl, wl, dl}, en, RR.h.ls(es, fs, ctx, t, s, H))) : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, _))))
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))))), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))))), RR.rok(rb, es, fs, ctx, t, s, H),
    RR.gen_rset(rb, es, fs, ctx, t, s, H, DC.thr(db, wb, b2, DR.DTurn{dl, DR.Lab.conj(wl), b2}), RR.mg_in(DC.Sk.ms(s), nb, fs, DC.Sk.ls(s), rb, DC.Mem{b2, rb, wb, db}, DC.thr(db, wb, b2, DR.DTurn{dl, DR.Lab.conj(wl), b2}), enb, SH.node_refl(rb),
      ST.ind_tl(DC.thr(db, wb, b2, DR.DTurn{dl, DR.Lab.conj(wl), b2}), db, DC.dcat(DC.lstats(DC.pprems(DC.nstats(fs, b2)), b2, wb, db), DC.llinks(DC.Sk.ls(s), b2, wb, db)), ST.ind_cat_r(DC.thr(db, wb, b2, DR.DTurn{dl, DR.Lab.conj(wl), b2}), DC.lstats(DC.pprems(DC.nstats(fs, b2)), b2, wb, db), DC.llinks(DC.Sk.ls(s), b2, wb, db), PU.ll_in(DC.Sk.ls(s), n, b2, wb, db, c2, bl, wl, dl, en, nb2(bl, b, b2, eab, eb)))))),
    MG.samevd_sym(DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))))), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))))), GN.cc(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl)))))))

def act_ll.k2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, ec: {SV.eq(c2, c) == True{} : Bool}, r1: SK.Both({DC.node_eq(bl, b) == True{} : Bool}, {wl == w : DR.Lab})) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  (eb, ew) = r1
  act_ll.go(es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, n, c2, bl, wl, dl, en, ec, eb, ew)

def act_ll.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, ok: SK.Both({SV.eq(c2, c) == True{} : Bool}, SK.Both({DC.node_eq(bl, b) == True{} : Bool}, {wl == w : DR.Lab}))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  (ec, r1) = ok
  act_ll.k2(es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, n, c2, bl, wl, dl, en, ec, r1)

def act_ll.m(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +n: Nat, em: {SH.lat(DC.Sk.ls(s), n) == m : Maybe<&2, DC.Link>}, ok: PU.lk.ok(m, c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  match m:
    case Some{DC.Link{+c2, +bl, +wl, +dl}}:
      act_ll.k(es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, n, c2, bl, wl, dl, em, ok)
    case None{}:
      absurd(ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))), LP.tf(ok))

# a stored label of (c, b): its link's turn gives w_b conj(w) z_c in b's root's set
def act_ll(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, hl: PU.LIn(DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  (+n, +ok) = hl
  act_ll.m(SH.lat(DC.Sk.ls(s), n), es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, n, {==}, ok)

def act_ll.z(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +rb: DR.Node, +wb: DR.Lab) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(LS.lab0()), DR.zdir(es, DR.NSeg{c})))):
  TU.zin(es, fs, ctx, t, s, H, rb, DR.gmul(wb, DR.gmul(DR.Lab.conj(LS.lab0()), DR.zdir(es, DR.NSeg{c}))), GN.samevd_tr(DR.gmul(wb, DR.gmul(DR.Lab.conj(LS.lab0()), DR.zdir(es, DR.NSeg{c}))), DR.gmul(wb, DR.zerov()), DR.zerov(), MG.gmul_cong(wb, DR.gmul(DR.Lab.conj(LS.lab0()), DR.zdir(es, DR.NSeg{c})), DR.zerov(), TU.lzv(DR.Lab.conj(LS.lab0()), DR.zdir(es, DR.NSeg{c}), TU.lz_conj(LS.lab0(), ({==}, {==})))), TU.gz0(wb)))

def act_ll.lz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, h: PU.lzor.f(f, DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  match f:
    case True{}:
      %Equal.sym(DR.Lab, w, LS.lab0(), h) : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(_), DR.zdir(es, DR.NSeg{c}))))
      act_ll.z(es, fs, ctx, t, s, H, c, rb, wb)
    case False{}:
      act_ll(es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, h)

def act_ll.st(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +b: DR.Node, +w: DR.Lab, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, hz: PU.LZor(DC.Sk.ls(s), c, b, w)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.NSeg{c})))):
  (+f, +h) = hz
  act_ll.lz(f, es, fs, ctx, t, s, H, c, b, w, b2, rb, wb, db, nb, enb, eab, h)

def turn.co.l(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +lst: LS.LSp(LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), DR.Lab.conj(g))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c})))):
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c}))), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))), RR.rok(rb, es, fs, ctx, t, s, H),
    lsp_inw(es, fs, ctx, t, s, H, rb, wb, DR.Lab.conj(LS.lat0(DC.lstored(DC.Sk.ls(s), c, b))), DR.Lab.conj(LS.lat1(DC.lstored(DC.Sk.ls(s), c, b))), DR.Lab.conj(DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c}), LS.lsp_conj(DR.Lab.conj(g), LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), lst),
      act_ll.st(es, fs, ctx, t, s, H, c, b, LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), b2, rb, wb, db, nb, enb, eab, PU.lat0_of(DC.Sk.ls(s), c, b)), act_ll.st(es, fs, ctx, t, s, H, c, b, LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), b2, rb, wb, db, nb, enb, eab, PU.lat1_of(DC.Sk.ls(s), c, b))),
    MG.gmul_cong(wb, DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})), DR.gmul(g, DR.zdir(es, DR.NSeg{c})), MG.samevd_sym(DR.gmul(g, DR.zdir(es, DR.NSeg{c})), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})), GN.cc(g, DR.zdir(es, DR.NSeg{c})))))

def turn.co.b(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, bin: RF.BIn(DC.lstored(DC.Sk.ls(s), c, b), LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b)))), +lb: LS.LSp(LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), DR.Lab.conj(g))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c})))):
  (+b0, +b1) = bin
  turn.co.l(es, fs, ctx, t, s, H, c, g, b, b2, rb, wb, db, nb, enb, eab, LS.lsp_trans(DR.Lab.conj(g), LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b))), LS.lat0(DC.lstored(DC.Sk.ls(s), c, b)), LS.lat1(DC.lstored(DC.Sk.ls(s), c, b)), lb, b0, b1))

def turn.co.t(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool},
  hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c})))):
  turn.co.b(es, fs, ctx, t, s, H, c, g, b, b2, rb, wb, db, nb, enb, eab,
    RF.basis_in(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b), RF.lkc_none(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, b, es, fs, t, s, c, DC.crep(es, fs, t, s, c), PU.lkc.of(c, es, fs, ctx, t, s, H, PU.lkcr(es, fs, ctx, t, s, H, c, emc, hf)),
      RR.btr(q => SH.nmem(q, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}), b2, b, eab, RR.recn_at(DC.Sk.ms(s), nb, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, DC.Mem{b2, rb, wb, db}, enb, SH.sh.rn(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))))), PU.ne_rec(es, fs, ctx, t, s, H, b, c, DC.Mem{b2, rb, wb, db}, emb, emc)),
      SH.pairok_of(DC.Sk.ls(s), c, b, SH.shi.l(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))), SH.lnzs_of(DC.Sk.ls(s), c, b, RR.h.lsn(es, fs, ctx, t, s, H))),
    PU.bc_c(es, fs, ctx, t, s, H, c, DR.zdir(es, b), DR.Lab.conj(g), hf, BL.zdir_below(es, t, b, RR.h.z(es, fs, ctx, t, s, H)), hv))

def turn.co.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +eq: {q == DC.fullc(es, DC.Sk.k(s), c) : Bool}, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>},
  emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c})))):
  match q:
    case True{}:
      k2rr(es, fs, ctx, t, s, H, rb, wb, g, DR.zdir(es, DR.NSeg{c}), LP2.band_l(KS.ks.inb(DC.Sk.k(s), SK.VE.x(DR.zdir(es, DR.NSeg{c}))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.zdir(es, DR.NSeg{c}))), Equal.sym(Bool, True{}, DC.fullc(es, DC.Sk.k(s), c), eq)),
        LP2.band_r(KS.ks.inb(DC.Sk.k(s), SK.VE.x(DR.zdir(es, DR.NSeg{c}))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.zdir(es, DR.NSeg{c}))), Equal.sym(Bool, True{}, DC.fullc(es, DC.Sk.k(s), c), eq)))
    case False{}:
      turn.co.t(es, fs, ctx, t, s, H, c, g, b, b2, rb, wb, db, nb, enb, eab, emb, emc, Equal.sym(Bool, False{}, DC.fullc(es, DC.Sk.k(s), c), eq), hv)

# turn from collapsed c to an open b: par(c, x), x the same as conj(g) z_b, gives w_b g z_c in b's root's set
def turn.co(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>},
  emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, DR.NSeg{c})))):
  turn.co.q(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, H, c, g, b, b2, rb, wb, db, nb, enb, eab, {==}, emb, emc, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), hp, sx))
