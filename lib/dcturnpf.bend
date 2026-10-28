# bend-cad: the closure theorem's turn and through rules (PLAN-sk13b B3,
# "Turn and through"). This file: the label algebra they share, and the
# cases where both nodes are open. Different roots: the merge check makes
# w_a conj(g) zero. The same root r: Q_r holds y = w_b z_b and
# u y, u = w_a conj(g) conj(w_b), so a non-real u gives a complex line
# through y, z_b in K squared, and an open void node; a real u makes the
# conclusion a real multiple of w_a z_a (turn) or of w_b x (through).
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

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Zero forms and labels
# ---------------------

def gz0.q(+c: S.Q, +s0: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(c, DR.qz()), S.Q.mul(s0, DR.qz())), DR.qz()):
  QR.qring_eq([c, s0], E.QSub{E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}, E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}}, E.QCst{DR.qz()}, {==})

def gz0.r(+c: S.Q, +s0: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(s0, DR.qz()), S.Q.mul(c, DR.qz())), DR.qz()):
  QR.qring_eq([c, s0], E.QAdd{E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}, E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}}, E.QCst{DR.qz()}, {==})

# a rotation of 0 is 0
def gz0(w: DR.Lab) -> VD.SameVD(DR.gmul(w, DR.zerov()), DR.zerov()):
  match w:
    case DR.Lab{+c, +s0}:
      (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c, s0}, DR.zerov())), DR.zeroe(), p => gz0.q(c, s0)),
       ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c, s0}, DR.zerov())), DR.zeroe(), p => gz0.r(c, s0)))

def vz0.q(+m1: S.Q, +m2: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(m1, DR.qz()), S.Q.mul(m2, DR.qz())), DR.qz()):
  QR.qring_eq([m1, m2], E.QAdd{E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}, E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}}, E.QCst{DR.qz()}, {==})

# a combination of 0s is 0
def vz0(+m1: S.Q, +m2: S.Q) -> VD.SameVD(DR.vlin(m1, DR.zerov(), m2, DR.zerov()), DR.zerov()):
  (ID.qzero_ident(SK.VE.x(DR.vlin(m1, DR.zerov(), m2, DR.zerov())), DR.zeroe(), p => vz0.q(m1, m2)),
   ID.qzero_ident(SK.VE.y(DR.vlin(m1, DR.zerov(), m2, DR.zerov())), DR.zeroe(), p => vz0.q(m1, m2)))

def lz_conj(v: DR.Lab, h: LS.LZ(v)) -> LS.LZ(DR.Lab.conj(v)):
  match v:
    case DR.Lab{+c, +s0}:
      (hc, hs) = h
      (hc, Equal.trans(Bool, DR.qnz(S.Q.neg(s0)), DR.qnz(s0), False{}, LA.qnz_neg(s0), hs))

# a zero label acts as 0
def lzv(v: DR.Lab, +y: SK.VE, h: LS.LZ(v)) -> VD.SameVD(DR.gmul(v, y), DR.zerov()):
  match v:
    case DR.Lab{+c, +s0}:
      (hc, hs) = h
      LA.gmul_zero(c, s0, y, hc, hs)

def lzg.v(+wa: DR.Lab, +g: DR.Lab, +y: SK.VE, +hw: NZ.Nz(wa), +hV: VD.SameVD(DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.zerov())) -> VD.SameVD(DR.gmul(g, y), DR.zerov()):
  GN.samevd_tr(DR.gmul(g, y), DR.vlin(S.Q.inv(DC.lnorm(wa)), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.qz(), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y))), DR.zerov(), MG.samevd_sym(DR.vlin(S.Q.inv(DC.lnorm(wa)), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.qz(), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y))), DR.gmul(g, y), RR.ur(DC.lnorm(wa), DR.gmul(g, y), hw)), GN.samevd_tr(DR.vlin(S.Q.inv(DC.lnorm(wa)), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.qz(), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y))), DR.vlin(S.Q.inv(DC.lnorm(wa)), DR.zerov(), DR.qz(), DR.zerov()), DR.zerov(), ST.vcong(S.Q.inv(DC.lnorm(wa)), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.zerov(), DR.qz(), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.zerov(), hV, hV), vz0(S.Q.inv(DC.lnorm(wa)), DR.qz())))

def lzg.c(+wa: DR.Lab, +g: DR.Lab, +y: SK.VE, hz: LS.LZ(LB.lmul(wa, DR.Lab.conj(g)))) -> VD.SameVD(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y)), DR.zerov()):
  GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y)), DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), y), DR.zerov(), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y)), DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), y)), DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), y), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(g, y), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), y), GN.cc(g, y)), MG.samevd_sym(DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), y), DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), y)), LA.gconj_mul(wa, DR.Lab.conj(g), y))), lzv(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), y, lz_conj(LB.lmul(wa, DR.Lab.conj(g)), hz)))

# w conj(g) = 0 with w nonzero: g acts as 0
def lzg(+wa: DR.Lab, +g: DR.Lab, +y: SK.VE, +hw: NZ.Nz(wa), hz: LS.LZ(LB.lmul(wa, DR.Lab.conj(g)))) -> VD.SameVD(DR.gmul(g, y), DR.zerov()):
  lzg.v(wa, g, y, hw, GN.samevd_tr(DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), DR.gmul(wa, DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y))), DR.zerov(), MG.samevd_sym(DR.gmul(wa, DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y))), DR.vlin(DC.lnorm(wa), DR.gmul(g, y), DR.qz(), DR.gmul(g, y)), LA.w_conj(wa, DR.gmul(g, y))), GN.samevd_tr(DR.gmul(wa, DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y))), DR.gmul(wa, DR.zerov()), DR.zerov(), MG.gmul_cong(wa, DR.gmul(DR.Lab.conj(wa), DR.gmul(g, y)), DR.zerov(), lzg.c(wa, g, y, hz)), gz0(wa))))

# Scaling inside a set
# --------------------

def scale(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +c: S.Q, +y: SK.VE, +ok: ST.StOk(es, fs, t, k, st), +h: ST.InSt(es, fs, k, st, y))
  -> ST.InSt(es, fs, k, st, DR.vlin(c, y, DR.qz(), y)):
  ST.st_lin(es, fs, t, k, st, c, y, DR.qz(), y, ok, h, h)

# n y in a set, n nonzero: y is
def descale(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +n: S.Q, +y: SK.VE, +ok: ST.StOk(es, fs, t, k, st),
  +h: ST.InSt(es, fs, k, st, DR.vlin(n, y, DR.qz(), y)), +hn: {DR.qnz(n) == True{} : Bool}) -> ST.InSt(es, fs, k, st, y):
  ST.st_tr(es, fs, t, k, st, DR.vlin(S.Q.inv(n), DR.vlin(n, y, DR.qz(), y), DR.qz(), DR.vlin(n, y, DR.qz(), y)), y, ok,
    ST.st_lin(es, fs, t, k, st, S.Q.inv(n), DR.vlin(n, y, DR.qz(), y), DR.qz(), DR.vlin(n, y, DR.qz(), y), ok, h, h), RR.ur(n, y, hn))

# Real labels
# -----------

def realg(u: DR.Lab, +y: SK.VE, h: {DR.qnz(LA.lab.s(u)) == False{} : Bool}) -> VD.SameVD(DR.gmul(u, y), DR.vlin(LA.lab.c(u), y, DR.qz(), y)):
  match u:
    case DR.Lab{+c, +s0}:
      LA.gmul_realq(c, s0, y, h)

def real_conj(u: DR.Lab, h: {DR.qnz(LA.lab.s(u)) == False{} : Bool}) -> {DR.qnz(LA.lab.s(DR.Lab.conj(u))) == False{} : Bool}:
  match u:
    case DR.Lab{+c, +s0}:
      Equal.trans(Bool, DR.qnz(S.Q.neg(s0)), DR.qnz(s0), False{}, LA.qnz_neg(s0), h)

# (v conj(w)) (w y) = |w|² (v y)
def unwb(+v: DR.Lab, +wb: DR.Lab, +y: SK.VE) -> VD.SameVD(DR.gmul(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, y)), DR.vlin(DC.lnorm(wb), DR.gmul(v, y), DR.qz(), DR.gmul(v, y))):
  GN.samevd_tr(DR.gmul(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, y)), DR.gmul(v, DR.gmul(DR.Lab.conj(wb), DR.gmul(wb, y))), DR.vlin(DC.lnorm(wb), DR.gmul(v, y), DR.qz(), DR.gmul(v, y)), MG.samevd_sym(DR.gmul(v, DR.gmul(DR.Lab.conj(wb), DR.gmul(wb, y))), DR.gmul(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, y)), MG.compd(v, DR.Lab.conj(wb), DR.gmul(wb, y))), GN.samevd_tr(DR.gmul(v, DR.gmul(DR.Lab.conj(wb), DR.gmul(wb, y))), DR.gmul(v, DR.vlin(DC.lnorm(wb), y, DR.qz(), y)), DR.vlin(DC.lnorm(wb), DR.gmul(v, y), DR.qz(), DR.gmul(v, y)), MG.gmul_cong(v, DR.gmul(DR.Lab.conj(wb), DR.gmul(wb, y)), DR.vlin(DC.lnorm(wb), y, DR.qz(), y), LA.conj_w(wb, y)), LA.gmul_vlin(v, DC.lnorm(wb), y, DR.qz(), y)))

# conj(w_a conj(g) conj(w_b)) (w_a z) = |w_a|² (w_b (g z))
def tchain(+wa: DR.Lab, +g: DR.Lab, +wb: DR.Lab, +z: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb))), DR.gmul(wa, z)), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z)))):
  GN.samevd_tr(DR.gmul(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb))), DR.gmul(wa, z)), DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), LA.gconj_mul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb), DR.gmul(wa, z)), GN.samevd_tr(DR.gmul(DR.Lab.conj(LB.lmul(wa, DR.Lab.conj(g))), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z))), DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z)))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), LA.gconj_mul(wa, DR.Lab.conj(g), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z))), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z)))), DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z)))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z))), DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z))), GN.samevd_tr(DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z))), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wb, DR.gmul(wa, z))), DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z))), MG.gmul_cong(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z)), DR.gmul(wb, DR.gmul(wa, z)), MG.samevd_sym(DR.gmul(wb, DR.gmul(wa, z)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(wa, z)), GN.cc(wb, DR.gmul(wa, z)))), MG.samevd_sym(DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z))), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(wb, DR.gmul(wa, z))), GN.cc(g, DR.gmul(wb, DR.gmul(wa, z)))))), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z)))), DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, DR.gmul(wb, z)))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wb, DR.gmul(wa, z))), DR.gmul(g, DR.gmul(wa, DR.gmul(wb, z))), MG.gmul_cong(g, DR.gmul(wb, DR.gmul(wa, z)), DR.gmul(wa, DR.gmul(wb, z)), LA.gswap(wb, wa, z))), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, DR.gmul(wb, z)))), DR.gmul(DR.Lab.conj(wa), DR.gmul(wa, DR.gmul(g, DR.gmul(wb, z)))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), MG.gmul_cong(DR.Lab.conj(wa), DR.gmul(g, DR.gmul(wa, DR.gmul(wb, z))), DR.gmul(wa, DR.gmul(g, DR.gmul(wb, z))), LA.gswap(g, wa, DR.gmul(wb, z))), GN.samevd_tr(DR.gmul(DR.Lab.conj(wa), DR.gmul(wa, DR.gmul(g, DR.gmul(wb, z)))), DR.vlin(DC.lnorm(wa), DR.gmul(g, DR.gmul(wb, z)), DR.qz(), DR.gmul(g, DR.gmul(wb, z))), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), LA.conj_w(wa, DR.gmul(g, DR.gmul(wb, z))), ST.vcong(DC.lnorm(wa), DR.gmul(g, DR.gmul(wb, z)), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(g, DR.gmul(wb, z)), DR.gmul(wb, DR.gmul(g, z)), LA.gswap(g, wb, z), LA.gswap(g, wb, z))))))))

# Checks read at a root
# ---------------------

def fx.mgs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, h: FX.Fx(es, fs, t, cs, ids, s))
  -> {DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, r4) = r3
  (e, f) = r4
  e

def h.mgs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s)) -> {DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  fx.mgs(es, fs, t, OP.cspan(ctx), DC.segids(es), s, RR.h.fx(es, fs, ctx, t, s, H))

def inn_of.g(g: Bool, +x: DR.Node, +h0: DR.Node, +tl: List<&2, DR.Node>, eg: {g == DC.node_eq(x, h0) : Bool}, hn: {SV.bor(g, SH.nmem(x, tl)) == True{} : Bool},
  ih: {SH.nmem(x, tl) == True{} : Bool} -> SH.Inn(x, tl)) -> SH.Inn(x, Con{h0, tl}):
  match g:
    case True{}:
      (0n, Equal.cong(DR.Node, Maybe<&2, DR.Node>, q => Some{q}, h0, x, Equal.sym(DR.Node, x, h0, GN.node_eq_ok(x, h0, Equal.sym(Bool, True{}, DC.node_eq(x, h0), eg)))))
    case False{}:
      SH.inn_tl(x, h0, tl, ih(hn))

# a member of a node list has a position in it
def inn_of(xs: List<&2, DR.Node>, +x: DR.Node, h: {SH.nmem(x, xs) == True{} : Bool}) -> SH.Inn(x, xs):
  match xs:
    case Nil{}:
      absurd(SH.Inn(x, Nil{}), LP.tf(Equal.sym(Bool, False{}, True{}, h)))
    case Con{+h0, +tl}:
      inn_of.g(DC.node_eq(x, h0), x, h0, tl, {==}, h, y => inn_of(tl, x, y))

def mgs_at.n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, hi: SH.Inn(r, DC.roots(DC.Sk.ms(s)))) -> {DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r) == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  (+n, +en) = hi
  RF.mgs_none(DC.roots(DC.Sk.ms(s)), es, fs, t, s, h.mgs(es, fs, ctx, t, s, H), r, n, en)

# the merge search at a record's root found nothing
def mgs_at(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +n: Nat, +en: {SH.mat(DC.Sk.ms(s), n) == Some{DC.Mem{a2, r, w, d}} : Maybe<&2, DC.Mem>})
  -> {DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r) == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  mgs_at.n(es, fs, ctx, t, s, H, r, inn_of(DC.roots(DC.Sk.ms(s)), r, RR.root_nmem(es, fs, ctx, t, s, H, n, a2, r, w, d, en)))

# Both open, different roots
# --------------------------

# a record outside the root's component: no nonzero rotation of its node is in the root's set
def mz(ra: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +hne: {DC.node_eq(rb, ra) == False{} : Bool}, +v: DR.Lab,
  em: {DC.mgs.root(DC.node_eq(ra, DR.NFrame{}), es, fs, t, s, ra) == None{} : Maybe<&2, List<&2, DC.Mem>>}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(v, DR.zdir(es, b2)))) -> LS.LZ(v):
  match ra:
    case DR.NFrame{}:
      LS.zero_k(v, es, fs, ctx, t, DC.Sk.k(s), DR.zdir(es, b2), RR.h.k(es, fs, ctx, t, s, H), RF.mgF_none(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s), em, DC.Mem{b2, rb, wb, db}, nb, enb, hne), hv)
    case DR.NSeg{+c}:
      LS.zero_h(v, es, fs, ctx, DR.NSeg{c}, t, DC.rhull(es, fs, t, s, DR.NSeg{c}), DR.zdir(es, b2), GN.rhull_inv(es, fs, ctx, t, s, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)),
        RF.mgR_none(DC.Sk.ms(s), es, fs, t, DC.rhull(es, fs, t, s, DR.NSeg{c}), DR.NSeg{c}, DC.Sk.ms(s), em, DC.Mem{b2, rb, wb, db}, nb, enb, hne), hv)

def zb2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +v: DR.Lab, +b: DR.Node, +b2: DR.Node, eab: {b2 == b : DR.Node},
  h: ST.InSt(es, fs, k, st, DR.gmul(v, DR.zdir(es, b)))) -> ST.InSt(es, fs, k, st, DR.gmul(v, DR.zdir(es, b2))):
  %Equal.sym(DR.Node, b2, b, eab) : ST.InSt(es, fs, k, st, DR.gmul(v, DR.zdir(es, _)))
  h

# a form the same as 0 is in a root's set
def zin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, +y: SK.VE, +sv: VD.SameVD(y, DR.zerov())) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), y):
  ND.k2_in(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), y, ND.sok_root(es, fs, ctx, t, s, r, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.x(y), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), RR.svx(DR.zerov(), y, MG.samevd_sym(y, DR.zerov(), sv))),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.y(y), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), RR.svy(DR.zerov(), y, MG.samevd_sym(y, DR.zerov(), sv))))

# The same root
# -------------

def trr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +ra: DR.Node, +rb: DR.Node, +y: SK.VE, e: {ra == rb : DR.Node}, h: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), y)) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), y):
  %e : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, _), y)
  h

def explode.v(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b: DR.Node, +b2: DR.Node, +r: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, r, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +k2z: CL.K2(es, fs, DC.Sk.k(s), DR.zdir(es, b))) -> Empty:
  RR.void.go(es, fs, ctx, t, s, H, b, b2, r, wb, db, nb, enb, eab, RR.k2b.x(es, fs, DC.Sk.k(s), DR.zdir(es, b), k2z), RR.k2b.y(es, fs, DC.Sk.k(s), DR.zdir(es, b), k2z))

# Q_r holds y = w_b z_b and u y with u not real: i y too, a complex line, and an open void node
def explode(u: DR.Lab, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b: DR.Node, +b2: DR.Node, +r: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, r, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +hB: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(wb, DR.zdir(es, b))), hU: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(u, DR.gmul(wb, DR.zdir(es, b)))),
  hs: {DR.qnz(LA.lab.s(u)) == True{} : Bool}) -> Empty:
  match u:
    case DR.Lab{+c, +s0}:
      explode.v(es, fs, ctx, t, s, H, b, b2, r, wb, db, nb, enb, eab, RR.unrot(es, fs, DC.Sk.k(s), wb, DR.zdir(es, b), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), RR.mnz_at(DC.Sk.ms(s), nb, DC.Mem{b2, r, wb, db}, enb, RR.h.msn(es, fs, ctx, t, s, H)),
        RR.line.root(r, es, fs, ctx, t, s, H, DR.gmul(wb, DR.zdir(es, b)), hB, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.vlin(S.Q.inv(s0), DR.gmul(DR.Lab{c, s0}, DR.gmul(wb, DR.zdir(es, b))), S.Q.neg(S.Q.mul(c, S.Q.inv(s0))), DR.gmul(wb, DR.zdir(es, b))), DR.imul(DR.gmul(wb, DR.zdir(es, b))), RR.rok(r, es, fs, ctx, t, s, H),
          ST.st_lin(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), S.Q.inv(s0), DR.gmul(DR.Lab{c, s0}, DR.gmul(wb, DR.zdir(es, b))), S.Q.neg(S.Q.mul(c, S.Q.inv(s0))), DR.gmul(wb, DR.zdir(es, b)), RR.rok(r, es, fs, ctx, t, s, H), hU, hB),
          MG.samevd_sym(DR.imul(DR.gmul(wb, DR.zdir(es, b))), DR.vlin(S.Q.inv(s0), DR.gmul(DR.Lab{c, s0}, DR.gmul(wb, DR.zdir(es, b))), S.Q.neg(S.Q.mul(c, S.Q.inv(s0))), DR.gmul(wb, DR.zdir(es, b))), LA.gmul_i(c, s0, DR.gmul(wb, DR.zdir(es, b)), hs))), RR.root_nmem(es, fs, ctx, t, s, H, nb, b2, r, wb, db, enb))))

def real.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +u: DR.Lab, +b: DR.Node, +b2: DR.Node, +r: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, r, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, eq: {q == DR.qnz(LA.lab.s(u)) : Bool},
  +hB: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(wb, DR.zdir(es, b))), +hU: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(u, DR.gmul(wb, DR.zdir(es, b))))) -> {DR.qnz(LA.lab.s(u)) == False{} : Bool}:
  match q:
    case True{}:
      absurd({DR.qnz(LA.lab.s(u)) == False{} : Bool}, explode(u, es, fs, ctx, t, s, H, b, b2, r, wb, db, nb, enb, eab, hB, hU, Equal.sym(Bool, True{}, DR.qnz(LA.lab.s(u)), eq)))
    case False{}:
      Equal.sym(Bool, False{}, DR.qnz(LA.lab.s(u)), eq)

# through, the same root: a real u makes w_a conj(g) x a real multiple of w_b x
def thr.same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, +v: DR.Lab, +wb: DR.Lab, +x: SK.VE, +hx: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(wb, x)), hr: {DR.qnz(LA.lab.s(LB.lmul(v, DR.Lab.conj(wb)))) == False{} : Bool}, +hw: NZ.Nz(wb))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(v, x)):
  descale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DC.lnorm(wb), DR.gmul(v, x), RR.rok(r, es, fs, ctx, t, s, H),
    ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.vlin(LA.lab.c(LB.lmul(v, DR.Lab.conj(wb))), DR.gmul(wb, x), DR.qz(), DR.gmul(wb, x)), DR.vlin(DC.lnorm(wb), DR.gmul(v, x), DR.qz(), DR.gmul(v, x)), RR.rok(r, es, fs, ctx, t, s, H),
      scale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), LA.lab.c(LB.lmul(v, DR.Lab.conj(wb))), DR.gmul(wb, x), RR.rok(r, es, fs, ctx, t, s, H), hx),
      GN.samevd_tr(DR.vlin(LA.lab.c(LB.lmul(v, DR.Lab.conj(wb))), DR.gmul(wb, x), DR.qz(), DR.gmul(wb, x)), DR.gmul(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, x)), DR.vlin(DC.lnorm(wb), DR.gmul(v, x), DR.qz(), DR.gmul(v, x)), MG.samevd_sym(DR.gmul(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, x)), DR.vlin(LA.lab.c(LB.lmul(v, DR.Lab.conj(wb))), DR.gmul(wb, x), DR.qz(), DR.gmul(wb, x)), realg(LB.lmul(v, DR.Lab.conj(wb)), DR.gmul(wb, x), hr)), unwb(v, wb, x))), hw)

# turn, the same root: a real u makes w_b g z_a a real multiple of w_a z_a
def turn.same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +r: DR.Node, +wa: DR.Lab, +g: DR.Lab, +wb: DR.Lab, +z: SK.VE, +hA: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(wa, z)), hr: {DR.qnz(LA.lab.s(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))) == False{} : Bool}, +hw: NZ.Nz(wa))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(wb, DR.gmul(g, z))):
  descale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), RR.rok(r, es, fs, ctx, t, s, H),
    ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.vlin(LA.lab.c(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), DR.gmul(wa, z), DR.qz(), DR.gmul(wa, z)), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), RR.rok(r, es, fs, ctx, t, s, H),
      scale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), LA.lab.c(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), DR.gmul(wa, z), RR.rok(r, es, fs, ctx, t, s, H), hA),
      GN.samevd_tr(DR.vlin(LA.lab.c(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), DR.gmul(wa, z), DR.qz(), DR.gmul(wa, z)), DR.gmul(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb))), DR.gmul(wa, z)), DR.vlin(DC.lnorm(wa), DR.gmul(wb, DR.gmul(g, z)), DR.qz(), DR.gmul(wb, DR.gmul(g, z))), MG.samevd_sym(DR.gmul(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb))), DR.gmul(wa, z)), DR.vlin(LA.lab.c(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), DR.gmul(wa, z), DR.qz(), DR.gmul(wa, z)), realg(DR.Lab.conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb))), DR.gmul(wa, z), real_conj(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), hr))), tchain(wa, g, wb, z))), hw)

# Both open
# ---------

def turn.oo.t(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +e: {ra == rb : DR.Node}, +hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, a)))):
  turn.same(es, fs, ctx, t, s, H, rb, wa, g, wb, DR.zdir(es, a), trr(es, fs, ctx, t, s, H, ra, rb, DR.gmul(wa, DR.zdir(es, a)), e, RR.self.go(es, fs, ctx, t, s, H, a, a2, ra, wa, da, na, ena, eaa)), real.q(DR.qnz(LA.lab.s(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), es, fs, ctx, t, s, H, LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), b, b2, rb, wb, db, nb, enb, eab, {==}, RR.self.go(es, fs, ctx, t, s, H, b, b2, rb, wb, db, nb, enb, eab), ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.vlin(DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), DR.qz(), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), DR.gmul(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), DR.gmul(wb, DR.zdir(es, b))), RR.rok(rb, es, fs, ctx, t, s, H), scale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), RR.rok(rb, es, fs, ctx, t, s, H), trr(es, fs, ctx, t, s, H, ra, rb, DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), e, hv)), MG.samevd_sym(DR.gmul(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), DR.gmul(wb, DR.zdir(es, b))), DR.vlin(DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), DR.qz(), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), unwb(LB.lmul(wa, DR.Lab.conj(g)), wb, DR.zdir(es, b))))), RR.mnz_at(DC.Sk.ms(s), na, DC.Mem{a2, ra, wa, da}, ena, RR.h.msn(es, fs, ctx, t, s, H)))

def turn.oo.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, eq: {q == DC.node_eq(ra, rb) : Bool}, +hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, a)))):
  match q:
    case True{}:
      turn.oo.t(es, fs, ctx, t, s, H, a, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, eab, GN.node_eq_ok(ra, rb, Equal.sym(Bool, True{}, DC.node_eq(ra, rb), eq)), hv)
    case False{}:
      zin(es, fs, ctx, t, s, H, rb, DR.gmul(wb, DR.gmul(g, DR.zdir(es, a))), GN.samevd_tr(DR.gmul(wb, DR.gmul(g, DR.zdir(es, a))), DR.gmul(wb, DR.zerov()), DR.zerov(), MG.gmul_cong(wb, DR.gmul(g, DR.zdir(es, a)), DR.zerov(), lzg(wa, g, DR.zdir(es, a), RR.mnz_at(DC.Sk.ms(s), na, DC.Mem{a2, ra, wa, da}, ena, RR.h.msn(es, fs, ctx, t, s, H)), mz(ra, es, fs, ctx, t, s, H, b2, rb, wb, db, nb, enb, SH.node_sym(ra, rb, Equal.sym(Bool, False{}, DC.node_eq(ra, rb), eq)), LB.lmul(wa, DR.Lab.conj(g)), mgs_at(es, fs, ctx, t, s, H, a2, ra, wa, da, na, ena), zb2(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), LB.lmul(wa, DR.Lab.conj(g)), b, b2, eab, hv)))), gz0(wb)))

# turn with both nodes open: par(a, x), x the same as conj(g) z_b, gives par(b, g z_a)
def turn.oo(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, DR.gmul(g, DR.zdir(es, a)))):
  turn.oo.q(DC.node_eq(ra, rb), es, fs, ctx, t, s, H, a, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, eab, {==}, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), RR.rok(ra, es, fs, ctx, t, s, H), hp, GN.samevd_tr(DR.gmul(wa, x), DR.gmul(wa, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), MG.gmul_cong(wa, x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), sx), MG.compd(wa, DR.Lab.conj(g), DR.zdir(es, b)))))

def thr.oo.t(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +e: {ra == rb : DR.Node}, +hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2)):
  trr(es, fs, ctx, t, s, H, rb, ra, DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2), Equal.sym(DR.Node, ra, rb, e), thr.same(es, fs, ctx, t, s, H, rb, LB.lmul(wa, DR.Lab.conj(g)), wb, x2, hq, real.q(DR.qnz(LA.lab.s(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)))), es, fs, ctx, t, s, H, LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), b, b2, rb, wb, db, nb, enb, eab, {==}, RR.self.go(es, fs, ctx, t, s, H, b, b2, rb, wb, db, nb, enb, eab), ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.vlin(DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), DR.qz(), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), DR.gmul(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), DR.gmul(wb, DR.zdir(es, b))), RR.rok(rb, es, fs, ctx, t, s, H), scale(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), RR.rok(rb, es, fs, ctx, t, s, H), trr(es, fs, ctx, t, s, H, ra, rb, DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), e, hv)), MG.samevd_sym(DR.gmul(LB.lmul(LB.lmul(wa, DR.Lab.conj(g)), DR.Lab.conj(wb)), DR.gmul(wb, DR.zdir(es, b))), DR.vlin(DC.lnorm(wb), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), DR.qz(), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), unwb(LB.lmul(wa, DR.Lab.conj(g)), wb, DR.zdir(es, b))))), RR.mnz_at(DC.Sk.ms(s), nb, DC.Mem{b2, rb, wb, db}, enb, RR.h.msn(es, fs, ctx, t, s, H))))

def thr.oo.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, eq: {q == DC.node_eq(ra, rb) : Bool}, +hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2)):
  match q:
    case True{}:
      thr.oo.t(es, fs, ctx, t, s, H, a, g, b, x2, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, eab, GN.node_eq_ok(ra, rb, Equal.sym(Bool, True{}, DC.node_eq(ra, rb), eq)), hv, hq)
    case False{}:
      zin(es, fs, ctx, t, s, H, ra, DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2), lzv(LB.lmul(wa, DR.Lab.conj(g)), x2, mz(ra, es, fs, ctx, t, s, H, b2, rb, wb, db, nb, enb, SH.node_sym(ra, rb, Equal.sym(Bool, False{}, DC.node_eq(ra, rb), eq)), LB.lmul(wa, DR.Lab.conj(g)), mgs_at(es, fs, ctx, t, s, H, a2, ra, wa, da, na, ena), zb2(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), LB.lmul(wa, DR.Lab.conj(g)), b, b2, eab, hv))))

# through with both nodes open: par(a, x), x the same as conj(g) z_b, and par(b, x2) give par(a, conj(g) x2)
def thr.oo(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2)))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, DR.gmul(DR.Lab.conj(g), x2))):
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2), DR.gmul(wa, DR.gmul(DR.Lab.conj(g), x2)), RR.rok(ra, es, fs, ctx, t, s, H), thr.oo.q(DC.node_eq(ra, rb), es, fs, ctx, t, s, H, a, g, b, x2, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, eab, {==}, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), RR.rok(ra, es, fs, ctx, t, s, H), hp, GN.samevd_tr(DR.gmul(wa, x), DR.gmul(wa, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, b)), MG.gmul_cong(wa, x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), sx), MG.compd(wa, DR.Lab.conj(g), DR.zdir(es, b)))), hq),
    MG.samevd_sym(DR.gmul(wa, DR.gmul(DR.Lab.conj(g), x2)), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), x2), MG.compd(wa, DR.Lab.conj(g), x2)))
