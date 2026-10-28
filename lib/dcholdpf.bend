# bend-cad: the closure's positive answers are right (PLAN-sk13b B3, the
# decision interface). When a state holds the target equation e (K) or its
# direction statement (par(b, y) in b's set), DC.hold.der is a valid
# derivation proving it: K's own, or b's set's (through b's record: its
# derivation turned to b and passed through the root, then scaled).
# Proofs only.

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
import ./seppf.bend as SP
import ./dcturnpf.bend as TU
import ./dcpushpf.bend as PU

import ./dcturncpf.bend as TC

import ./dclopf.bend as LO

import ./dcftiepf.bend as FT

import ./dclinkpf.bend as LK
import ./dcderpf.bend as DP
import ./hspacepf.bend as HP
import ./dcbelowpf.bend as BL
import ./seppf.bend as SP
import ../spec/_draft13b.bend as SD


def absurd(-A: Type, x: Empty) -> A:
  match x:

# a derivation of par(a, ·) the same as y, in reusable form
def POk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +a: DR.Node, +d: DR.Der, +y: SK.VE) -> Data:
  SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isp(DR.concl(es, fs, d)), SK.Both({DR.Jd.a(DR.concl(es, fs, d)) == a : DR.Node}, VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), y))))

def pok_der(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +d: DR.Der, +y: SK.VE, h: LK.DerOk(es, fs, ctx, t, a, d, y)) -> POk(es, fs, ctx, a, d, y):
  (h1, sv) = h
  (h2, bl) = h1
  (v, r1) = h2
  (p, ea) = r1
  (v, (p, (ea, sv)))

def kd.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +y: SK.VE, kk: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, DC.Sk.k(s), SK.VE.y(y))), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), SK.VE.y(y)))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), SK.VE.y(y)))), SK.VE.y(y)))))
  -> POk(es, fs, ctx, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, DC.Sk.k(s), SK.VE.y(y)), y}, y):
  (kk, ({==}, ({==}, MG.samevd_refl(y))))

def rset_pok(r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +y: SK.VE, h: {DC.rset.inb(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, y) == True{} : Bool}, +hy: HP.VBelow(y, t)) -> POk(es, fs, ctx, r, DC.rset.der(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, y), y):
  match r:
    case DR.NFrame{}:
      kd.go(es, fs, ctx, t, s, H, y, DP.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), SK.VE.y(y), RR.h.k(es, fs, ctx, t, s, H), h))
    case DR.NSeg{+c}:
      pok_der(es, fs, ctx, t, DR.NSeg{c}, HS.hs.der(es, fs, t, DR.NSeg{c}, DC.rhull(es, fs, t, s, DR.NSeg{c}), y), y,
        DP.hs_der_okd(es, fs, ctx, DR.NSeg{c}, t, DC.rhull(es, fs, t, s, DR.NSeg{c}), y, GN.rhull_inv(es, fs, ctx, t, s, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), h, hy,
          BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H))))

# Through a record
# ----------------

def svz(+es: List<&2, SK.Ent>, +x: SK.VE, +w: DR.Lab, +a2: DR.Node, +a: DR.Node, ea: {a2 == a : DR.Node}, h: VD.SameVD(x, DR.gmul(w, DR.zdir(es, a2)))) -> VD.SameVD(x, DR.gmul(w, DR.zdir(es, a))):
  %ea : VD.SameVD(x, DR.gmul(w, DR.zdir(es, _)))
  h

def mb.sv1(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +w: DR.Lab, +r: DR.Node, +d: DR.Der, ad: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node})
  -> VD.SameVD(DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d)))), DR.gmul(DR.Lab.conj(w), DR.zdir(es, r))):
  %ad : VD.SameVD(DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d)))), DR.gmul(DR.Lab.conj(w), DR.zdir(es, _)))
  MG.samevd_refl(DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d)))))

def mb.fin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +dx: DR.Der, +y: SK.VE, +thv: VD.VD(es, fs, ctx, DR.DThrough{DR.DTurn{d, DR.Lab.conj(w), a}, dx, w, r}), +svx: VD.SameVD(DR.Jd.x(DR.concl(es, fs, dx)), DR.gmul(w, y)), +hnz: NZ.Nz(w))
  -> POk(es, fs, ctx, a, DC.mem.back(d, w, a, r, dx), y):
  ((thv, (thv, ({==}, ({==}, {==})))), ({==}, ({==},
    GN.samevd_tr(DR.vlin(S.Q.inv(DC.lnorm(w)), DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx))), DR.qz(), DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx)))), DR.vlin(S.Q.inv(DC.lnorm(w)), DR.vlin(DC.lnorm(w), y, DR.qz(), y), DR.qz(), DR.vlin(DC.lnorm(w), y, DR.qz(), y)), y, ST.vcong(S.Q.inv(DC.lnorm(w)), DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx))), DR.vlin(DC.lnorm(w), y, DR.qz(), y), DR.qz(), DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx))), DR.vlin(DC.lnorm(w), y, DR.qz(), y), GN.samevd_tr(DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx))), DR.gmul(DR.Lab.conj(w), DR.gmul(w, y)), DR.vlin(DC.lnorm(w), y, DR.qz(), y), MG.gmul_cong(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx)), DR.gmul(w, y), svx), LA.conj_w(w, y)), GN.samevd_tr(DR.gmul(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx))), DR.gmul(DR.Lab.conj(w), DR.gmul(w, y)), DR.vlin(DC.lnorm(w), y, DR.qz(), y), MG.gmul_cong(DR.Lab.conj(w), DR.Jd.x(DR.concl(es, fs, dx)), DR.gmul(w, y), svx), LA.conj_w(w, y))), RR.ur(DC.lnorm(w), y, hnz)))))

def mb.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +ea: {a2 == a : DR.Node}, +y: SK.VE, +dx: DR.Der, +vd: VD.VD(es, fs, ctx, d), +pd: VD.Isp(DR.concl(es, fs, d)),
  +ad: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +svd: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a2))), +orr: VD.OpenD(es, ctx, r), +vx: VD.VD(es, fs, ctx, dx), +px: VD.Isp(DR.concl(es, fs, dx)),
  +ax: {DR.Jd.a(DR.concl(es, fs, dx)) == r : DR.Node}, +svx: VD.SameVD(DR.Jd.x(DR.concl(es, fs, dx)), DR.gmul(w, y)), +hnz: NZ.Nz(w)) -> POk(es, fs, ctx, a, DC.mem.back(d, w, a, r, dx), y):
  mb.fin(es, fs, ctx, t, s, H, a, r, w, d, dx, y,
    ((vd, (pd, GN.samevd_tr(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a)), DR.gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.zdir(es, a)), svz(es, DR.Jd.x(DR.concl(es, fs, d)), w, a2, a, ea, svd), GN.cc(w, DR.zdir(es, a))))), (vx, ({==}, (px, (mb.sv1(es, fs, w, r, d, ad), (ax, orr)))))),
    svx, hnz)

def mb.x(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +ea: {a2 == a : DR.Node}, +y: SK.VE, +dx: DR.Der, +vd: VD.VD(es, fs, ctx, d), +pd: VD.Isp(DR.concl(es, fs, d)),
  +ad: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +svd: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a2))), +orr: VD.OpenD(es, ctx, r), hdx: POk(es, fs, ctx, r, dx, DR.gmul(w, y)), +hnz: NZ.Nz(w)) -> POk(es, fs, ctx, a, DC.mem.back(d, w, a, r, dx), y):
  (vx, r1) = hdx
  (px, r2) = r1
  (ax, svx) = r2
  mb.go(es, fs, ctx, t, s, H, a, a2, r, w, d, ea, y, dx, vd, pd, ad, svd, orr, vx, px, ax, svx, hnz)

def mb.m(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +ea: {a2 == a : DR.Node}, +y: SK.VE, +dx: DR.Der, mok: GN.MOkD(es, fs, ctx, t, DC.Mem{a2, r, w, d}), hdx: POk(es, fs, ctx, r, dx, DR.gmul(w, y)), +hnz: NZ.Nz(w))
  -> POk(es, fs, ctx, a, DC.mem.back(d, w, a, r, dx), y):
  (vd, m1) = mok
  (pd, m2) = m1
  (ad, m3) = m2
  (svd, m4) = m3
  (oa, m5) = m4
  (orr, bel) = m5
  mb.x(es, fs, ctx, t, s, H, a, a2, r, w, d, ea, y, dx, vd, pd, ad, svd, orr, hdx, hnz)

# b's record (r, w, d) and a derivation of par(r, w y) give par(b, y)
def mb_pok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +n: Nat, +en: {SH.mat(DC.Sk.ms(s), n) == Some{DC.Mem{a2, r, w, d}} : Maybe<&2, DC.Mem>}, +ea: {a2 == a : DR.Node}, +y: SK.VE, +dx: DR.Der,
  hdx: POk(es, fs, ctx, r, dx, DR.gmul(w, y))) -> POk(es, fs, ctx, a, DC.mem.back(d, w, a, r, dx), y):
  mb.m(es, fs, ctx, t, s, H, a, a2, r, w, d, ea, y, dx, RR.mok_at(DC.Sk.ms(s), n, es, fs, ctx, t, DC.Mem{a2, r, w, d}, en, RR.h.ms(es, fs, ctx, t, s, H)), hdx, RR.mnz_at(DC.Sk.ms(s), n, DC.Mem{a2, r, w, d}, en, RR.h.msn(es, fs, ctx, t, s, H)))

def pdm.i(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +y: SK.VE, +hy: HP.VBelow(y, t), +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, hin: SH.Inm(DC.Mem{a2, r, w, d}, DC.Sk.ms(s)), hn: {DC.node_eq(a2, a) == True{} : Bool},
  h: {DC.rset.inb(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, y)) == True{} : Bool}) -> POk(es, fs, ctx, a, DC.par.dm(Some{DC.Mem{a2, r, w, d}}, es, fs, t, s, a, y), y):
  (+n, +en) = hin
  mb_pok(es, fs, ctx, t, s, H, a, a2, r, w, d, n, en, GN.node_eq_ok(a2, a, hn), y, DC.rset.der(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, y)), rset_pok(r, es, fs, ctx, t, s, H, DR.gmul(w, y), h, BL.vb_gmul(w, y, t, hy)))

def pdm.mi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +y: SK.VE, +hy: HP.VBelow(y, t), +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), a, DC.Mem{a2, r, w, d}),
  h: {DC.rset.inb(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, y)) == True{} : Bool}) -> POk(es, fs, ctx, a, DC.par.dm(Some{DC.Mem{a2, r, w, d}}, es, fs, t, s, a, y), y):
  (hin, hn) = mi
  pdm.i(es, fs, ctx, t, s, H, a, y, hy, a2, r, w, d, hin, hn, h)

def pdn(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +y: SK.VE, +hy: HP.VBelow(y, t), em: {DC.mem_of(DC.Sk.ms(s), a) == None{} : Maybe<&2, DC.Mem>}, h: {DC.par.n(a, es, fs, t, s, y) == True{} : Bool})
  -> POk(es, fs, ctx, a, DC.par.dn(a, es, fs, t, s, y), y):
  match a:
    case DR.NFrame{}:
      absurd(POk(es, fs, ctx, DR.NFrame{}, DC.par.dn(DR.NFrame{}, es, fs, t, s, y), y), RR.fnone(es, fs, ctx, t, s, H, em))
    case DR.NSeg{+c}:
      pok_der(es, fs, ctx, t, DR.NSeg{c}, DC.rep.der(DC.crep(es, fs, t, s, c), es, fs, t, DC.Sk.k(s), c, y), y,
        LK.rep_der_ok(DC.crep(es, fs, t, s, c), es, fs, ctx, t, DC.Sk.k(s), c, y, RP.crep_ok(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), RR.h.k(es, fs, ctx, t, s, H), h, hy, RR.h.z(es, fs, ctx, t, s, H)))

def pdm(mm: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +y: SK.VE, +hy: HP.VBelow(y, t), em: {DC.mem_of(DC.Sk.ms(s), a) == mm : Maybe<&2, DC.Mem>}, h: {DC.par.m(mm, es, fs, t, s, a, y) == True{} : Bool})
  -> POk(es, fs, ctx, a, DC.par.dm(mm, es, fs, t, s, a, y), y):
  match mm:
    case Some{DC.Mem{+a2, +r, +w, +d}}:
      pdm.mi(es, fs, ctx, t, s, H, a, y, hy, a2, r, w, d, SH.mem_of_in(DC.Sk.ms(s), a, DC.Mem{a2, r, w, d}, em), h)
    case None{}:
      pdn(a, es, fs, ctx, t, s, H, y, hy, em, h)

# what the state holds at a node has a derivation there
def par_pok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +y: SK.VE, +hy: HP.VBelow(y, t), h: {DC.par.inb(es, fs, t, s, a, y) == True{} : Bool}) -> POk(es, fs, ctx, a, DC.par.der(es, fs, t, s, a, y), y):
  pdm(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, y, hy, {==}, h)

# The positive answer
# -------------------

def isk_pr(j: DR.Jd, +es: List<&2, SK.Ent>, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, hk: VD.Isk(j), hs: VD.SameD(DR.Jd.e(j), e)) -> SD.Proves(es, m, e, j):
  match j:
    case DR.JK{+f}:
      ID.ident_ok(f, e, hs)
    case DR.JP{+a, +x}:
      absurd(SD.Proves(es, m, e, DR.JP{a, x}), LP.tf(Equal.sym(Bool, False{}, True{}, hk)))

def isp_pr(j: DR.Jd, +es: List<&2, SK.Ent>, +b: Nat, +y: SK.VE, +l: S.Q, +e: E.QExpr, hp: VD.Isp(j), ha: {DR.Jd.a(j) == DR.NSeg{b} : DR.Node}, hs: VD.SameVD(DR.Jd.x(j), y))
  -> SD.Proves(es, Some{DR.DStat{b, y, l}}, e, j):
  match j:
    case DR.JK{+f}:
      absurd(SD.Proves(es, Some{DR.DStat{b, y, l}}, e, DR.JK{f}), LP.tf(Equal.sym(Bool, False{}, True{}, hp)))
    case DR.JP{+a, +x}:
      (ha, VD.samev_of(x, y, hs))

def st.fin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b: Nat, +y: SK.VE, +l: S.Q, +e: E.QExpr, h: POk(es, fs, ctx, DR.NSeg{b}, DC.par.der(es, fs, t, s, DR.NSeg{b}, y), y))
  -> DR.Valid(es, fs, ctx, DC.par.der(es, fs, t, s, DR.NSeg{b}, y)) & SD.Proves(es, Some{DR.DStat{b, y, l}}, e, DR.concl(es, fs, DC.par.der(es, fs, t, s, DR.NSeg{b}, y))):
  (v, r1) = h
  (p, r2) = r1
  (ea, sv) = r2
  (VD.valid_of(es, fs, ctx, DC.par.der(es, fs, t, s, DR.NSeg{b}, y), v), isp_pr(DR.concl(es, fs, DC.par.der(es, fs, t, s, DR.NSeg{b}, y)), es, b, y, l, e, p, ea, sv))

def st.m(m: Maybe<&2, DR.DStat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, hs: {DC.stat.inb(m, es, fs, t, s) == True{} : Bool}, +hb: {DC.fb.ds(m, t) == True{} : Bool})
  -> DR.Valid(es, fs, ctx, DC.stat.der(m, es, fs, t, s)) & SD.Proves(es, m, e, DR.concl(es, fs, DC.stat.der(m, es, fs, t, s))):
  match m:
    case Some{DR.DStat{+b, +y, +l}}:
      st.fin(es, fs, ctx, t, s, H, b, y, l, e, par_pok(es, fs, ctx, t, s, H, DR.NSeg{b}, y, (LP2.band_l(SP.vbelow(SK.VE.x(y), t), SP.vbelow(SK.VE.y(y), t), hb), LP2.band_r(SP.vbelow(SK.VE.x(y), t), SP.vbelow(SK.VE.y(y), t), hb)), hs))
    case None{}:
      absurd(DR.Valid(es, fs, ctx, DR.DZero{}) & SD.Proves(es, None{}, e, DR.concl(es, fs, DR.DZero{})), LP.tf(Equal.sym(Bool, False{}, True{}, hs)))

def kh.fin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>, kk: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, DC.Sk.k(s), e)), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), e))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), e))), e))))
  -> DR.Valid(es, fs, ctx, KS.ks.der(es, fs, DC.Sk.k(s), e)) & SD.Proves(es, m, e, DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), e))):
  (v, r1) = kk
  (ik, sd) = r1
  (VD.valid_of(es, fs, ctx, KS.ks.der(es, fs, DC.Sk.k(s), e), v), isk_pr(DR.concl(es, fs, KS.ks.der(es, fs, DC.Sk.k(s), e)), es, m, e, ik, sd))

def hold.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>, eq: {q == KS.ks.inb(DC.Sk.k(s), e) : Bool}, hh: {SV.bor(q, DC.stat.inb(m, es, fs, t, s)) == True{} : Bool}, hb: {DC.fb.ds(m, t) == True{} : Bool})
  -> DR.Valid(es, fs, ctx, DC.hold.pick(q, es, fs, t, s, e, m)) & SD.Proves(es, m, e, DR.concl(es, fs, DC.hold.pick(q, es, fs, t, s, e, m))):
  match q:
    case True{}:
      kh.fin(es, fs, ctx, t, s, H, e, m, DP.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), e, RR.h.k(es, fs, ctx, t, s, H), Equal.sym(Bool, True{}, KS.ks.inb(DC.Sk.k(s), e), eq)))
    case False{}:
      st.m(m, es, fs, ctx, t, s, H, e, hh, hb)

# a state holding e, or its statement m (below t), has a valid derivation proving e
def hold_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>, hh: {DC.holds(es, fs, t, s, e, m) == True{} : Bool}, hb: {DC.fb.ds(m, t) == True{} : Bool})
  -> DR.Valid(es, fs, ctx, DC.hold.der(es, fs, t, s, e, m)) & SD.Proves(es, m, e, DR.concl(es, fs, DC.hold.der(es, fs, t, s, e, m))):
  hold.q(KS.ks.inb(DC.Sk.k(s), e), es, fs, ctx, t, s, H, e, m, {==}, hh, hb)
