# bend-cad: the closure's explosions derive everything (PLAN-sk13b B3,
# "Explosion"). With 1 in K, void at F gives par(F, (0, e)); with an open
# segment's direction in K squared, turn and through at it do; frame-back
# then gives K(e), which proves any equation e. Proofs only.

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

def zz.q(+p: List<&2, S.Q>) -> S.Q.eq(E.qeval(p, DR.zeroe()), E.qeval(p, DR.cst(DR.qz()))):
  LQ.q_refl(DR.qz())

def ey.q(+E0: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.neg(DR.qz()), DR.qz()), S.Q.mul(DR.qo(), E0)), E0):
  QR.qring_eq([E0], E.QAdd{E.QMul{E.QCst{S.Q.neg(DR.qz())}, E.QCst{DR.qz()}}, E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}}, E.QVar{0n}, {==})

def ey.at(+p: List<&2, S.Q>, +e: E.QExpr) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab.conj(DC.lone()), SK.VE{DR.zeroe(), e}))), E.qeval(p, e)):
  ey.q(E.qeval(p, e))

def e1.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, +d: DR.Der, vd: VD.VD(es, fs, ctx, d), r1: SK.Both(VD.Isk(DR.concl(es, fs, d)), VD.SameD(DR.Jd.e(DR.concl(es, fs, d)), DR.cst(DR.qo()))))
  -> DR.Valid(es, fs, ctx, DR.DBack{DR.DVoid{d, DR.DZero{}, DR.NFrame{}, SK.VE{DR.zeroe(), e}}}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DBack{DR.DVoid{d, DR.DZero{}, DR.NFrame{}, SK.VE{DR.zeroe(), e}}})):
  (ik, sd) = r1
  (VD.valid_of(es, fs, ctx, DR.DBack{DR.DVoid{d, DR.DZero{}, DR.NFrame{}, SK.VE{DR.zeroe(), e}}}, ((vd, (Unit{}, (ik, ({==}, (sd, ID.qzero_ident(DR.zeroe(), DR.cst(DR.qz()), p => zz.q(p))))))), ({==}, {==}))),
   p => LQ.q_refl(E.qeval(p, e)))

def ev.v2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +g: Nat, +dr: DR.Der, +di: DR.Der, +x: SK.VE, +vr: VD.VD(es, fs, ctx, dr), +ir: VD.Isk(DR.concl(es, fs, dr)),
  +sr: VD.SameD(DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zseg(es, g))), +vi: VD.VD(es, fs, ctx, di), +ii: VD.Isk(DR.concl(es, fs, di)), +si: VD.SameD(DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zseg(es, g))))
  -> VD.VD(es, fs, ctx, DR.DVoid{dr, di, DR.NSeg{g}, x}):
  (vr, (vi, (ir, (ii, (sr, si)))))

def ev.v(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +g: Nat, +dr: DR.Der, +di: DR.Der, +x: SK.VE, kr: RD.KD(es, fs, ctx, dr, SK.VE.x(DR.zseg(es, g))), ki: RD.KD(es, fs, ctx, di, SK.VE.y(DR.zseg(es, g))))
  -> VD.VD(es, fs, ctx, DR.DVoid{dr, di, DR.NSeg{g}, x}):
  (vr, r1) = kr
  (ir, sr) = r1
  (vi, r2) = ki
  (ii, si) = r2
  ev.v2(es, fs, ctx, g, dr, di, x, vr, ir, sr, vi, ii, si)

def ev.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, +g: Nat, +dr: DR.Der, +di: DR.Der, +og: VD.OpenD(es, ctx, DR.NSeg{g}),
  +kr: RD.KD(es, fs, ctx, dr, SK.VE.x(DR.zseg(es, g))), +ki: RD.KD(es, fs, ctx, di, SK.VE.y(DR.zseg(es, g)))) -> DR.Valid(es, fs, ctx, DR.DBack{DR.DThrough{DR.DTurn{DR.DVoid{dr, di, DR.NSeg{g}, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))}, DC.lone(), DR.NFrame{}}, DR.DVoid{dr, di, DR.NSeg{g}, SK.VE{DR.zeroe(), e}}, DC.lone(), DR.NSeg{g}}}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DBack{DR.DThrough{DR.DTurn{DR.DVoid{dr, di, DR.NSeg{g}, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))}, DC.lone(), DR.NFrame{}}, DR.DVoid{dr, di, DR.NSeg{g}, SK.VE{DR.zeroe(), e}}, DC.lone(), DR.NSeg{g}}})):
  (VD.valid_of(es, fs, ctx, DR.DBack{DR.DThrough{DR.DTurn{DR.DVoid{dr, di, DR.NSeg{g}, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))}, DC.lone(), DR.NFrame{}}, DR.DVoid{dr, di, DR.NSeg{g}, SK.VE{DR.zeroe(), e}}, DC.lone(), DR.NSeg{g}}},
    ((((ev.v(es, fs, ctx, g, dr, di, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{})), kr, ki), ({==}, MG.samevd_refl(DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))))), (ev.v(es, fs, ctx, g, dr, di, SK.VE{DR.zeroe(), e}, kr, ki), ({==}, ({==},
      (GN.samevd_tr(DR.gmul(DC.lone(), DR.zdir(es, DR.NSeg{g})), DR.zdir(es, DR.NSeg{g}), DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NSeg{g})), MG.samevd_sym(DR.zdir(es, DR.NSeg{g}), DR.gmul(DC.lone(), DR.zdir(es, DR.NSeg{g})), GN.one(DR.zdir(es, DR.NSeg{g}))), MG.samevd_sym(DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NSeg{g})), DR.zdir(es, DR.NSeg{g}), LO.c1g(DR.zdir(es, DR.NSeg{g})))), ({==}, og))))))), ({==}, {==}))),
   p => ey.at(p, e))

def ev.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, +g: Nat, +dr: DR.Der, +di: DR.Der,
  h: SK.Both(VD.OpenD(es, ctx, DR.NSeg{g}), SK.Both(RD.KD(es, fs, ctx, dr, SK.VE.x(DR.zseg(es, g))), RD.KD(es, fs, ctx, di, SK.VE.y(DR.zseg(es, g)))))) -> DR.Valid(es, fs, ctx, DR.DBack{DR.DThrough{DR.DTurn{DR.DVoid{dr, di, DR.NSeg{g}, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))}, DC.lone(), DR.NFrame{}}, DR.DVoid{dr, di, DR.NSeg{g}, SK.VE{DR.zeroe(), e}}, DC.lone(), DR.NSeg{g}}}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DBack{DR.DThrough{DR.DTurn{DR.DVoid{dr, di, DR.NSeg{g}, DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NFrame{}))}, DC.lone(), DR.NFrame{}}, DR.DVoid{dr, di, DR.NSeg{g}, SK.VE{DR.zeroe(), e}}, DC.lone(), DR.NSeg{g}}})):
  (og, r1) = h
  (kr, ki) = r1
  ev.go(es, fs, ctx, m, e, g, dr, di, og, kr, ki)

def e1.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, +d: DR.Der, h: RD.KD(es, fs, ctx, d, DR.cst(DR.qo())))
  -> DR.Valid(es, fs, ctx, DR.DBack{DR.DVoid{d, DR.DZero{}, DR.NFrame{}, SK.VE{DR.zeroe(), e}}}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DBack{DR.DVoid{d, DR.DZero{}, DR.NFrame{}, SK.VE{DR.zeroe(), e}}})):
  (vd, r1) = h
  e1.go(es, fs, ctx, m, e, d, vd, r1)

# an explosion's derivation of K(e) is valid and proves e
def expl_ok(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, ho: RD.OutInv(es, fs, ctx, t, o),
  hx: {DC.is_expl(o) == True{} : Bool}) -> DR.Valid(es, fs, ctx, DC.expl.der(o, es, e)) & SD.Proves(es, m, e, DR.concl(es, fs, DC.expl.der(o, es, e))):
  match o:
    case DC.OStep{+s}:
      absurd(DR.Valid(es, fs, ctx, DR.DZero{}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DZero{})), LP.tf(Equal.sym(Bool, False{}, True{}, hx)))
    case DC.OFix{+s}:
      absurd(DR.Valid(es, fs, ctx, DR.DZero{}) & SD.Proves(es, m, e, DR.concl(es, fs, DR.DZero{})), LP.tf(Equal.sym(Bool, False{}, True{}, hx)))
    case DC.OOne{+d}:
      e1.k(es, fs, ctx, m, e, d, ho)
    case DC.OVoid{+g, +dr, +di}:
      ev.k(es, fs, ctx, m, e, g, dr, di, ho)
