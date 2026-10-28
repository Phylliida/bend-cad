# bend-cad: the closure theorem (PLAN-sk13b B3, "Closure of a fixpoint").
# At a fixpoint of the closure, every valid derivation's conclusion is
# represented: K(e) has e in K, and par(a, x) has x in a's set. Turn and
# through by the two nodes' records; then the induction on derivations.
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
import ./dcturnpf.bend as TU
import ./dcpushpf.bend as PU

import ./dcturncpf.bend as TC

import ./dclopf.bend as LO

import ./dcftiepf.bend as FT

def absurd(-A: Type, x: Empty) -> A:
  match x:

# a collapsed set holding every form
def full_triv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +y: SK.VE, eq: {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), y):
  %Equal.sym(Bool, DC.fullc(es, DC.Sk.k(s), c), True{}, eq) : ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.f(_, es, fs, t, s, c), c), y)
  Unit{}

# Turn
# ----

def tr.oc.r(ra: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +a: DR.Node, +a2: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node},
  emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(g, DR.zdir(es, a))):
  match ra:
    case DR.NFrame{}:
      FT.turn.oc.F(es, fs, ctx, t, s, H, c, g, a, a2, wa, da, na, ena, eaa, emc, hf, hv)
    case DR.NSeg{+c1}:
      LO.turn.oc.n(es, fs, ctx, t, s, H, c, g, a, a2, c1, wa, da, na, ena, eaa, emc, hf, hv)

def tr.oc.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +a: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +eq: {q == DC.fullc(es, DC.Sk.k(s), c) : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(g, DR.zdir(es, a))):
  match q:
    case True{}:
      full_triv(es, fs, ctx, t, s, H, c, DR.gmul(g, DR.zdir(es, a)), Equal.sym(Bool, True{}, DC.fullc(es, DC.Sk.k(s), c), eq))
    case False{}:
      tr.oc.r(ra, es, fs, ctx, t, s, H, c, g, a, a2, wa, da, na, ena, eaa, emc, Equal.sym(Bool, False{}, DC.fullc(es, DC.Sk.k(s), c), eq), hv)

def tr.ab.n(b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, emb: {DC.mem_of(DC.Sk.ms(s), b) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))))
  -> RR.rp.m(None{}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  match b:
    case DR.NFrame{}:
      absurd(RR.rp.m(None{}, es, fs, t, s, DR.NFrame{}, DR.gmul(g, DR.zdir(es, a))), RR.fnone(es, fs, ctx, t, s, H, emb))
    case DR.NSeg{+c}:
      tr.oc.q(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, H, c, g, a, a2, ra, wa, da, na, ena, eaa, emb, {==}, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})), RR.rok(ra, es, fs, ctx, t, s, H), hp, GN.samevd_tr(DR.gmul(wa, x), DR.gmul(wa, DR.gmul(DR.Lab.conj(g), DR.zdir(es, DR.NSeg{c}))), DR.gmul(LB.lmul(wa, DR.Lab.conj(g)), DR.zdir(es, DR.NSeg{c})), MG.gmul_cong(wa, x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, DR.NSeg{c})), sx), MG.compd(wa, DR.Lab.conj(g), DR.zdir(es, DR.NSeg{c})))))

def tr.ab.n2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(Some{DC.Mem{b2, rb, wb, db}}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  TU.turn.oo(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, eab, hp, sx)

def tr.ab.i(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, hin: SH.Inm(DC.Mem{b2, rb, wb, db}, DC.Sk.ms(s)), hn: {DC.node_eq(b2, b) == True{} : Bool},
  hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(Some{DC.Mem{b2, rb, wb, db}}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  (+nb, +enb) = hin
  tr.ab.n2(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, nb, enb, GN.node_eq_ok(b2, b, hn), hp, sx)

def tr.ab.mi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}),
  hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(Some{DC.Mem{b2, rb, wb, db}}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  (hin, hn) = mi
  tr.ab.i(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, hin, hn, hp, sx)

def tr.ab(mb: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, +na: Nat, +ena: {SH.mat(DC.Sk.ms(s), na) == Some{DC.Mem{a2, ra, wa, da}} : Maybe<&2, DC.Mem>}, +eaa: {a2 == a : DR.Node}, emb: {DC.mem_of(DC.Sk.ms(s), b) == mb : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))))
  -> RR.rp.m(mb, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  match mb:
    case Some{DC.Mem{+b2, +rb, +wb, +db}}:
      tr.ab.mi(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, na, ena, eaa, b2, rb, wb, db, SH.mem_of_in(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}, emb), hp, sx)
    case None{}:
      tr.ab.n(b, es, fs, ctx, t, s, H, a, x, g, a2, ra, wa, da, na, ena, eaa, emb, hp, sx)

def tr.a.i(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, hin: SH.Inm(DC.Mem{a2, ra, wa, da}, DC.Sk.ms(s)), hn: {DC.node_eq(a2, a) == True{} : Bool},
  hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(DC.mem_of(DC.Sk.ms(s), b), es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  (+na, +ena) = hin
  tr.ab(DC.mem_of(DC.Sk.ms(s), b), es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, na, ena, GN.node_eq_ok(a2, a, hn), {==}, hp, sx)

def tr.a.mi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), a, DC.Mem{a2, ra, wa, da}),
  hp: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x)), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(DC.mem_of(DC.Sk.ms(s), b), es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  (hin, hn) = mi
  tr.a.i(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, hin, hn, hp, sx)

def tr.cc(b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: SK.VE, +g: DR.Lab, emb: {DC.mem_of(DC.Sk.ms(s), b) == None{} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(None{}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))):
  match b:
    case DR.NFrame{}:
      absurd(RR.rp.m(None{}, es, fs, t, s, DR.NFrame{}, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))), RR.fnone(es, fs, ctx, t, s, H, emb))
    case DR.NSeg{+c1}:
      TC.turn.cc(es, fs, ctx, t, s, H, c, x, g, c1, emc, hp, sx)

def tr.cb.i(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, hin: SH.Inm(DC.Mem{b2, rb, wb, db}, DC.Sk.ms(s)), hn: {DC.node_eq(b2, b) == True{} : Bool},
  emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(Some{DC.Mem{b2, rb, wb, db}}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))):
  (+nb, +enb) = hin
  TC.turn.co(es, fs, ctx, t, s, H, c, x, g, b, b2, rb, wb, db, nb, enb, GN.node_eq_ok(b2, b, hn), emb, emc, hp, sx)

def tr.cb.mi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}),
  emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(Some{DC.Mem{b2, rb, wb, db}}, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))):
  (hin, hn) = mi
  tr.cb.i(es, fs, ctx, t, s, H, c, x, g, b, b2, rb, wb, db, hin, hn, emb, emc, hp, sx)

def tr.cb(mb: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: SK.VE, +g: DR.Lab, +b: DR.Node, +emb: {DC.mem_of(DC.Sk.ms(s), b) == mb : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hp: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)))) -> RR.rp.m(mb, es, fs, t, s, b, DR.gmul(g, DR.zdir(es, DR.NSeg{c}))):
  match mb:
    case Some{DC.Mem{+b2, +rb, +wb, +db}}:
      tr.cb.mi(es, fs, ctx, t, s, H, c, x, g, b, b2, rb, wb, db, SH.mem_of_in(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}, emb), emb, emc, hp, sx)
    case None{}:
      tr.cc(b, es, fs, ctx, t, s, H, c, x, g, emb, emc, hp, sx)

def tr.a.n(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +x: SK.VE, +g: DR.Lab, +b: DR.Node, ema: {DC.mem_of(DC.Sk.ms(s), a) == None{} : Maybe<&2, DC.Mem>}, hp: RR.rp.m(None{}, es, fs, t, s, a, x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))))
  -> RR.rp.m(DC.mem_of(DC.Sk.ms(s), b), es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  match a:
    case DR.NFrame{}:
      absurd(RR.rp.m(DC.mem_of(DC.Sk.ms(s), b), es, fs, t, s, b, DR.gmul(g, DR.zdir(es, DR.NFrame{}))), RR.fnone(es, fs, ctx, t, s, H, ema))
    case DR.NSeg{+c}:
      tr.cb(DC.mem_of(DC.Sk.ms(s), b), es, fs, ctx, t, s, H, c, x, g, b, {==}, ema, hp, sx)

def tr.a(ma: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +g: DR.Lab, +b: DR.Node, ema: {DC.mem_of(DC.Sk.ms(s), a) == ma : Maybe<&2, DC.Mem>}, hp: RR.rp.m(ma, es, fs, t, s, a, x), sx: VD.SameVD(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))))
  -> RR.rp.m(DC.mem_of(DC.Sk.ms(s), b), es, fs, t, s, b, DR.gmul(g, DR.zdir(es, a))):
  match ma:
    case Some{DC.Mem{+a2, +ra, +wa, +da}}:
      tr.a.mi(es, fs, ctx, t, s, H, a, x, g, b, a2, ra, wa, da, SH.mem_of_in(DC.Sk.ms(s), a, DC.Mem{a2, ra, wa, da}, ema), hp, sx)
    case None{}:
      tr.a.n(a, es, fs, ctx, t, s, H, x, g, b, ema, hp, sx)

# turn: par(a, x), x the same as conj(g) z_b, gives par(b, g z_a)
def rule_turn(j: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +g: DR.Lab, +b: DR.Node, h: RR.Repr(es, fs, t, s, j), p: DR.IsP(j), sv: DR.SameV(DR.Jd.x(j), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))))
  -> RR.Repr(es, fs, t, s, DR.JP{b, DR.gmul(g, DR.zdir(es, DR.Jd.a(j)))}):
  match j:
    case DR.JP{+a, +x}:
      tr.a(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, x, g, b, {==}, h, VD.samevd_of(x, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), sv))
    case DR.JK{+e}:
      absurd(RR.Repr(es, fs, t, s, DR.JP{b, DR.gmul(g, DR.zdir(es, DR.NFrame{}))}), p)

# Through
# -------

def th.c.r(rb: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node},
  +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), x2)):
  match rb:
    case DR.NFrame{}:
      FT.thr.co.F(es, fs, ctx, t, s, H, c, g, b, b2, wb, db, nb, enb, eab, emb, emc, hf, x2, hv, hq)
    case DR.NSeg{+c1}:
      LO.thr.co.n(es, fs, ctx, t, s, H, c, g, b, b2, c1, wb, db, nb, enb, eab, emb, emc, hf, x2, hv, hq)

def th.c.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +eq: {q == DC.fullc(es, DC.Sk.k(s), c) : Bool}, hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2)))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(DR.Lab.conj(g), x2)):
  match q:
    case True{}:
      full_triv(es, fs, ctx, t, s, H, c, DR.gmul(DR.Lab.conj(g), x2), Equal.sym(Bool, True{}, DC.fullc(es, DC.Sk.k(s), c), eq))
    case False{}:
      th.c.r(rb, es, fs, ctx, t, s, H, c, g, b, x2, b2, wb, db, nb, enb, eab, emb, emc, Equal.sym(Bool, False{}, DC.fullc(es, DC.Sk.k(s), c), eq), hv, hq)

def th.an(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, ema: {DC.mem_of(DC.Sk.ms(s), a) == None{} : Maybe<&2, DC.Mem>}, h1: RR.rp.m(None{}, es, fs, t, s, a, x1), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2)))
  -> RR.rp.m(None{}, es, fs, t, s, a, DR.gmul(DR.Lab.conj(g), x2)):
  match a:
    case DR.NFrame{}:
      absurd(RR.rp.m(None{}, es, fs, t, s, DR.NFrame{}, DR.gmul(DR.Lab.conj(g), x2)), RR.fnone(es, fs, ctx, t, s, H, ema))
    case DR.NSeg{+c}:
      th.c.q(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, H, c, g, b, x2, b2, rb, wb, db, nb, enb, eab, emb, ema, {==}, ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), ND.sok_coll(es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), h1, sx), hq)

def th.ai(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, hin: SH.Inm(DC.Mem{a2, ra, wa, da}, DC.Sk.ms(s)),
  hn: {DC.node_eq(a2, a) == True{} : Bool}, h1: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x1)), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> RR.rp.m(Some{DC.Mem{a2, ra, wa, da}}, es, fs, t, s, a, DR.gmul(DR.Lab.conj(g), x2)):
  (+na, +ena) = hin
  TU.thr.oo(es, fs, ctx, t, s, H, a, x1, g, b, x2, a2, ra, wa, da, na, ena, GN.node_eq_ok(a2, a, hn), b2, rb, wb, db, nb, enb, eab, h1, sx, hq)

def th.ami(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +a2: DR.Node, +ra: DR.Node, +wa: DR.Lab, +da: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), a, DC.Mem{a2, ra, wa, da}),
  h1: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, ra), DR.gmul(wa, x1)), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> RR.rp.m(Some{DC.Mem{a2, ra, wa, da}}, es, fs, t, s, a, DR.gmul(DR.Lab.conj(g), x2)):
  (hin, hn) = mi
  th.ai(es, fs, ctx, t, s, H, a, x1, g, b, x2, b2, rb, wb, db, nb, enb, eab, a2, ra, wa, da, hin, hn, h1, sx, hq)

def th.a(ma: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, ema: {DC.mem_of(DC.Sk.ms(s), a) == ma : Maybe<&2, DC.Mem>}, h1: RR.rp.m(ma, es, fs, t, s, a, x1), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2)))
  -> RR.rp.m(ma, es, fs, t, s, a, DR.gmul(DR.Lab.conj(g), x2)):
  match ma:
    case Some{DC.Mem{+a2, +ra, +wa, +da}}:
      th.ami(es, fs, ctx, t, s, H, a, x1, g, b, x2, b2, rb, wb, db, nb, enb, eab, a2, ra, wa, da, SH.mem_of_in(DC.Sk.ms(s), a, DC.Mem{a2, ra, wa, da}, ema), h1, sx, hq)
    case None{}:
      th.an(a, es, fs, ctx, t, s, H, x1, g, b, x2, b2, rb, wb, db, nb, enb, eab, emb, ema, h1, sx, hq)

def th.bi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, hin: SH.Inm(DC.Mem{b2, rb, wb, db}, DC.Sk.ms(s)),
  hn: {DC.node_eq(b2, b) == True{} : Bool}, +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, h1: RR.Repr(es, fs, t, s, DR.JP{a, x1}), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> RR.Repr(es, fs, t, s, DR.JP{a, DR.gmul(DR.Lab.conj(g), x2)}):
  (+nb, +enb) = hin
  th.a(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, x1, g, b, x2, b2, rb, wb, db, nb, enb, GN.node_eq_ok(b2, b, hn), emb, {==}, h1, sx, hq)

def th.bmi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +b2: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}),
  +emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{DC.Mem{b2, rb, wb, db}} : Maybe<&2, DC.Mem>}, h1: RR.Repr(es, fs, t, s, DR.JP{a, x1}), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), hq: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, rb), DR.gmul(wb, x2))) -> RR.Repr(es, fs, t, s, DR.JP{a, DR.gmul(DR.Lab.conj(g), x2)}):
  (hin, hn) = mi
  th.bi(es, fs, ctx, t, s, H, a, x1, g, b, x2, b2, rb, wb, db, hin, hn, emb, h1, sx, hq)

def th.b(mb: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +g: DR.Lab, +b: DR.Node, +x2: SK.VE, +emb: {DC.mem_of(DC.Sk.ms(s), b) == mb : Maybe<&2, DC.Mem>}, h1: RR.Repr(es, fs, t, s, DR.JP{a, x1}),
  h2: RR.rp.m(mb, es, fs, t, s, b, x2), sx: VD.SameVD(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), ho: DR.Open(es, ctx, b)) -> RR.Repr(es, fs, t, s, DR.JP{a, DR.gmul(DR.Lab.conj(g), x2)}):
  match mb:
    case Some{DC.Mem{+b2, +rb, +wb, +db}}:
      th.bmi(es, fs, ctx, t, s, H, a, x1, g, b, x2, b2, rb, wb, db, SH.mem_of_in(DC.Sk.ms(s), b, DC.Mem{b2, rb, wb, db}, emb), emb, h1, sx, h2)
    case None{}:
      absurd(RR.Repr(es, fs, t, s, DR.JP{a, DR.gmul(DR.Lab.conj(g), x2)}), RR.open_rec(b, es, fs, ctx, t, s, H, ho, emb))

# through: par(a, x1), x1 the same as conj(g) z_b, and par(b, x2), b open, give par(a, conj(g) x2)
def rule_through(j1: DR.Jd, j2: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +g: DR.Lab, +b: DR.Node, h1: RR.Repr(es, fs, t, s, j1), h2: RR.Repr(es, fs, t, s, j2), p1: DR.IsP(j1), p2: DR.IsP(j2),
  sv: DR.SameV(DR.Jd.x(j1), DR.gmul(DR.Lab.conj(g), DR.zdir(es, b))), eb: {DR.Jd.a(j2) == b : DR.Node}, ho: DR.Open(es, ctx, b)) -> RR.Repr(es, fs, t, s, DR.JP{DR.Jd.a(j1), DR.gmul(DR.Lab.conj(g), DR.Jd.x(j2))}):
  match j1 j2:
    case DR.JP{+a, +x1} DR.JP{+b0, +x2}:
      th.b(DC.mem_of(DC.Sk.ms(s), b), es, fs, ctx, t, s, H, a, x1, g, b, x2, {==}, h1, RR.rp_node(b0, b, es, fs, t, s, x2, eb, h2), VD.samevd_of(x1, DR.gmul(DR.Lab.conj(g), DR.zdir(es, b)), sv), ho)
    case DR.JP{+a, +x1} DR.JK{+e2}:
      absurd(RR.Repr(es, fs, t, s, DR.JP{a, DR.gmul(DR.Lab.conj(g), DR.zerov())}), p2)
    case DR.JK{+e1} j2:
      absurd(RR.Repr(es, fs, t, s, DR.JP{DR.NFrame{}, DR.gmul(DR.Lab.conj(g), DR.Jd.x(j2))}), p1)

# The closure theorem
# -------------------

# at a fixpoint, every valid derivation's conclusion is represented
def closed(d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), hv: DR.Valid(es, fs, ctx, d)) -> RR.Repr(es, fs, t, s, DR.concl(es, fs, d)):
  match d:
    case DR.DZero{}:
      RR.rule_zero(es, fs, ctx, t, s, H)
    case DR.DPrem{+i}:
      RR.rule_prem(es, fs, ctx, t, s, H, i, hv)
    case DR.DKAdd{+l, +d1, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (k1, k2) = r2
      RR.rule_kadd(DR.concl(es, fs, d1), DR.concl(es, fs, d2), es, fs, ctx, t, s, H, l, closed(d1, es, fs, ctx, t, s, H, v1), closed(d2, es, fs, ctx, t, s, H, v2), k1, k2)
    case DR.DBack{+d0}:
      (v, r1) = hv
      (p, ea) = r1
      RR.rule_back(DR.concl(es, fs, d0), es, fs, ctx, t, s, H, closed(d0, es, fs, ctx, t, s, H, v), p, ea)
    case DR.DLine{+d1, +d2, +re}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (ea, r5) = r4
      (ho, sv) = r5
      RR.rule_line(DR.concl(es, fs, d1), DR.concl(es, fs, d2), es, fs, ctx, t, s, H, re, closed(d1, es, fs, ctx, t, s, H, v1), closed(d2, es, fs, ctx, t, s, H, v2), p1, p2, ea, ho, sv)
    case DR.DPPrem{+i}:
      RR.rule_pprem(es, fs, ctx, t, s, H, i, hv)
    case DR.DSelf{+a}:
      RR.rule_self(es, fs, ctx, t, s, H, a)
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, ea) = r3
      RR.rule_plin(DR.concl(es, fs, d1), DR.concl(es, fs, d2), es, fs, ctx, t, s, H, m1, m2, closed(d1, es, fs, ctx, t, s, H, v1), closed(d2, es, fs, ctx, t, s, H, v2), p1, p2, ea)
    case DR.DKnown{+d0, +dr, +di}:
      (v, r1) = hv
      (vr, r2) = r1
      (vi, r3) = r2
      (p, r4) = r3
      (kr, ki) = r4
      RR.rule_known(DR.concl(es, fs, d0), DR.concl(es, fs, dr), DR.concl(es, fs, di), es, fs, ctx, t, s, H, closed(d0, es, fs, ctx, t, s, H, v), closed(dr, es, fs, ctx, t, s, H, vr), closed(di, es, fs, ctx, t, s, H, vi), p, kr, ki)
    case DR.DTurn{+d0, +g, +b}:
      (v, r1) = hv
      (p, sv) = r1
      rule_turn(DR.concl(es, fs, d0), es, fs, ctx, t, s, H, g, b, closed(d0, es, fs, ctx, t, s, H, v), p, sv)
    case DR.DThrough{+d1, +d2, +g, +b}:
      (v1, r1) = hv
      (v2, r2) = r1
      (p1, r3) = r2
      (p2, r4) = r3
      (sv, r5) = r4
      (eb, ho) = r5
      rule_through(DR.concl(es, fs, d1), DR.concl(es, fs, d2), es, fs, ctx, t, s, H, g, b, closed(d1, es, fs, ctx, t, s, H, v1), closed(d2, es, fs, ctx, t, s, H, v2), p1, p2, sv, eb, ho)
    case DR.DFrame{+d0, +x}:
      (v, r1) = hv
      (k, sm) = r1
      RR.rule_frame(DR.concl(es, fs, d0), es, fs, ctx, t, s, H, x, closed(d0, es, fs, ctx, t, s, H, v), k, sm)
    case DR.DVoid{+dr, +di, +a, +x}:
      (vr, r1) = hv
      (vi, r2) = r1
      (kr, r3) = r2
      (ki, r4) = r3
      (sr, si) = r4
      RR.rule_void(DR.concl(es, fs, dr), DR.concl(es, fs, di), es, fs, ctx, t, s, H, a, x, closed(dr, es, fs, ctx, t, s, H, vr), closed(di, es, fs, ctx, t, s, H, vi), kr, ki, sr, si)

# the closure's fixpoint holds every valid derivation's conclusion
def dclose_closed(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, d: DR.Der, hv: DR.Valid(es, fs, ctx, d)) -> RR.Repr(es, fs, t, s, DR.concl(es, fs, d)):
  closed(d, es, fs, ctx, t, s, (FX.fix_at(es, fs, ctx, t, fuel, s, eo, hz, hb), (hz, hb)), hv)
