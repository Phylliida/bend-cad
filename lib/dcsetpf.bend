# bend-cad: the closure theorem's sets (PLAN-sk13b B3, "Closure of a
# fixpoint"): membership moved along SameV and closed under
# m1 x1 + m2 x2.
# - RI: rows deciding the span of B; membership by the residual, moved
#   along identities, closed under combinations, 0 in it.
# - K, F's set {y : Im y in K} and tied sets are residual tests on
#   polynomials (no encoding), exact for every form.
# - A hull's set is HIn: real combinations of its kept generators, a
#   Sigma (Data). Forms mentioning the tag t are fine there. It agrees
#   with the hull's Bool test for forms below t (hin_bool, hin_of).
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
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./identpf.bend as ID
import ./spanpf.bend as SN
import ./pairpf.bend as PP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG
import ./dcreppf.bend as RP
import ./dctiedpf.bend as TP
import ./kspacepf.bend as KP
import ./cwpf.bend as CW

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Spans decided by rows
# ---------------------

# the rows decide the span of B
def RI(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>) -> Data:
  SK.Both({EP.rinv(B, rows, 0n) == True{} : Bool}, {EL.rlen(rows) == SV.neqs(B) : Nat})

# e passes the rows' test
def Inb(+rows: List<&2, EL.Row>, +e: E.QExpr) -> Data:
  {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}

def ri.in(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: RI(B, rows), hz: Inb(rows, e)) -> SN.InSpan(e, B):
  (+hr, +hl) = h
  SN.in_of_zero(B, rows, e, hr, hz)

def ri.zero(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: RI(B, rows), +hi: SN.InSpan(e, B)) -> Inb(rows, e):
  (+hr, +hl) = h
  SN.zero_of_in(B, rows, e, hr, hl, hi)

# membership moves along SameD
def ri.tr(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e1: E.QExpr, +e2: E.QExpr, +h: RI(B, rows), hz: Inb(rows, e1), +hs: VD.SameD(e1, e2)) -> Inb(rows, e2):
  ri.zero(B, rows, e2, h, PP.in_tr(e1, e2, B, ri.in(B, rows, e1, h, hz), p => MG.samed_sym.at(p, e1, e2, hs)))

# m1 e1 + m2 e2
def lin2(+m1: S.Q, +e1: E.QExpr, +m2: S.Q, +e2: E.QExpr) -> E.QExpr:
  E.QAdd{E.QMul{E.QCst{m1}, e1}, E.QMul{E.QCst{m2}, e2}}

def az(+x: S.Q) -> S.Q.eq(S.Q.add(x, DR.qz()), x):
  QR.qring_eq([x], E.QAdd{E.QVar{0n}, E.QCst{DR.qz()}}, E.QVar{0n}, {==})

def lin2.at(+p: List<&2, S.Q>, +m1: S.Q, +e1: E.QExpr, +m2: S.Q, +e2: E.QExpr)
  -> S.Q.eq(E.qeval(p, lin2(m1, e1, m2, e2)), E.qeval(p, E.QAdd{E.QMul{E.QCst{m1}, e1}, E.QAdd{E.QMul{E.QCst{m2}, e2}, E.QCst{DR.qz()}}})):
  LQ.q_add_cong_r(S.Q.mul(m1, E.qeval(p, e1)), S.Q.mul(m2, E.qeval(p, e2)), S.Q.add(S.Q.mul(m2, E.qeval(p, e2)), DR.qz()), LQ.q_sym(S.Q.add(S.Q.mul(m2, E.qeval(p, e2)), DR.qz()), S.Q.mul(m2, E.qeval(p, e2)), az(S.Q.mul(m2, E.qeval(p, e2)))))

# closed under combinations
def ri.lin(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +m1: S.Q, +e1: E.QExpr, +m2: S.Q, +e2: E.QExpr, +h: RI(B, rows), h1: Inb(rows, e1), h2: Inb(rows, e2)) -> Inb(rows, lin2(m1, e1, m2, e2)):
  ri.zero(B, rows, lin2(m1, e1, m2, e2), h,
    PP.in_tr(E.QAdd{E.QMul{E.QCst{m1}, e1}, E.QAdd{E.QMul{E.QCst{m2}, e2}, E.QCst{DR.qz()}}}, lin2(m1, e1, m2, e2), B,
      SN.in_comb(m1, e1, E.QAdd{E.QMul{E.QCst{m2}, e2}, E.QCst{DR.qz()}}, B, ri.in(B, rows, e1, h, h1), SN.in_comb(m2, e2, E.QCst{DR.qz()}, B, ri.in(B, rows, e2, h, h2), SN.in_zero(B))),
      p => lin2.at(p, m1, e1, m2, e2)))

# 0 passes
def ri.z0(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +h: RI(B, rows)) -> Inb(rows, E.QCst{DR.qz()}):
  ri.zero(B, rows, E.QCst{DR.qz()}, h, SN.in_zero(B))

# The invariants' rows
# --------------------

def kri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, h: IV.KInvD(es, fs, ctx, t, k)) -> RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = h
      (hl, ha) = r1
      (hr, hl)

def hri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, hi: IV.HInvD(es, fs, ctx, r, t, h)) -> RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)):
  match h:
    case HS.HS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      (hr, hl)

def hbelow(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, hi: IV.HInvD(es, fs, ctx, r, t, h)) -> HP.AllBelow(HS.hxs(es, fs, HS.hs.ds(h)), t):
  match h:
    case HS.HS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      HP.allp_below(es, fs, ctx, r, t, ds, IV.allp_of(es, fs, ctx, r, t, ds, ha))

def tri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, s: DC.TS, hi: RP.TInvD(es, fs, ctx, r, t, u, s)) -> RI(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s)):
  match s:
    case DC.TS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      (hr, hl)

# F's set and tied sets
# ---------------------

def fin_tr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +y1: SK.VE, +y2: SK.VE, +hr: RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  hz: {KS.ks.inb(k, SK.VE.y(y1)) == True{} : Bool}, e: VD.SameVD(y1, y2)) -> {KS.ks.inb(k, SK.VE.y(y2)) == True{} : Bool}:
  (+e1, +e2) = e
  ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), SK.VE.y(y1), SK.VE.y(y2), hr, hz, e2)

def fin_lin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +m1: S.Q, +y1: SK.VE, +m2: S.Q, +y2: SK.VE, +hr: RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  h1: {KS.ks.inb(k, SK.VE.y(y1)) == True{} : Bool}, h2: {KS.ks.inb(k, SK.VE.y(y2)) == True{} : Bool}) -> {KS.ks.inb(k, SK.VE.y(DR.vlin(m1, y1, m2, y2))) == True{} : Bool}:
  ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), m1, SK.VE.y(y1), m2, SK.VE.y(y2), hr, h1, h2)

def cross_cong.at(+p: List<&2, S.Q>, +uu: SK.VE, +y1: SK.VE, +y2: SK.VE, +e1: VD.SameD(SK.VE.x(y1), SK.VE.x(y2)), +e2: VD.SameD(SK.VE.y(y1), SK.VE.y(y2)))
  -> S.Q.eq(E.qeval(p, SK.VE.cross(uu, y1)), E.qeval(p, SK.VE.cross(uu, y2))):
  QA.sub_cong(S.Q.mul(E.qeval(p, SK.VE.x(uu)), E.qeval(p, SK.VE.y(y1))), S.Q.mul(E.qeval(p, SK.VE.x(uu)), E.qeval(p, SK.VE.y(y2))), S.Q.mul(E.qeval(p, SK.VE.y(uu)), E.qeval(p, SK.VE.x(y1))), S.Q.mul(E.qeval(p, SK.VE.y(uu)), E.qeval(p, SK.VE.x(y2))),
    LQ.q_mul_cong_r(E.qeval(p, SK.VE.x(uu)), E.qeval(p, SK.VE.y(y1)), E.qeval(p, SK.VE.y(y2)), ID.ident_ok(SK.VE.y(y1), SK.VE.y(y2), e2)(p)),
    LQ.q_mul_cong_r(E.qeval(p, SK.VE.y(uu)), E.qeval(p, SK.VE.x(y1)), E.qeval(p, SK.VE.x(y2)), ID.ident_ok(SK.VE.x(y1), SK.VE.x(y2), e1)(p)))

def cross_cong(+uu: SK.VE, +y1: SK.VE, +y2: SK.VE, e: VD.SameVD(y1, y2)) -> VD.SameD(SK.VE.cross(uu, y1), SK.VE.cross(uu, y2)):
  (+e1, +e2) = e
  ID.qzero_ident(SK.VE.cross(uu, y1), SK.VE.cross(uu, y2), p => cross_cong.at(p, uu, y1, y2, e1, e2))

def tin_tr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +s: DC.TS, +y1: SK.VE, +y2: SK.VE, +hr: RI(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s)),
  hz: {DC.ts.inb(s, u, y1) == True{} : Bool}, e: VD.SameVD(y1, y2)) -> {DC.ts.inb(s, u, y2) == True{} : Bool}:
  ri.tr(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s), SK.VE.cross(DC.lform(u), y1), SK.VE.cross(DC.lform(u), y2), hr, hz, cross_cong(DC.lform(u), y1, y2, e))

def tin_lin.at(+p: List<&2, S.Q>, +uu: SK.VE, +m1: S.Q, +y1: SK.VE, +m2: S.Q, +y2: SK.VE)
  -> S.Q.eq(E.qeval(p, lin2(m1, SK.VE.cross(uu, y1), m2, SK.VE.cross(uu, y2))), E.qeval(p, SK.VE.cross(uu, DR.vlin(m1, y1, m2, y2)))):
  LQ.q_sym(E.qeval(p, SK.VE.cross(uu, DR.vlin(m1, y1, m2, y2))), E.qeval(p, lin2(m1, SK.VE.cross(uu, y1), m2, SK.VE.cross(uu, y2))), TP.cross_vlin.at(p, uu, m1, y1, m2, y2))

def tin_lin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +s: DC.TS, +m1: S.Q, +y1: SK.VE, +m2: S.Q, +y2: SK.VE, +hr: RI(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s)),
  h1: {DC.ts.inb(s, u, y1) == True{} : Bool}, h2: {DC.ts.inb(s, u, y2) == True{} : Bool}) -> {DC.ts.inb(s, u, DR.vlin(m1, y1, m2, y2)) == True{} : Bool}:
  ri.tr(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s), lin2(m1, SK.VE.cross(DC.lform(u), y1), m2, SK.VE.cross(DC.lform(u), y2)), SK.VE.cross(DC.lform(u), DR.vlin(m1, y1, m2, y2)), hr,
    ri.lin(DC.crosses(es, fs, u, DC.ts.ds(s)), DC.ts.rows(s), m1, SK.VE.cross(DC.lform(u), y1), m2, SK.VE.cross(DC.lform(u), y2), hr, h1, h2),
    ID.qzero_ident(lin2(m1, SK.VE.cross(DC.lform(u), y1), m2, SK.VE.cross(DC.lform(u), y2)), SK.VE.cross(DC.lform(u), DR.vlin(m1, y1, m2, y2)),
      p => tin_lin.at(p, DC.lform(u), m1, y1, m2, y2)))

# Combinations of forms
# ---------------------

def vcong.ax(+p: List<&2, S.Q>, +m1: S.Q, +x1: SK.VE, +y1: SK.VE, +m2: S.Q, +x2: SK.VE, +y2: SK.VE, +a1: VD.SameD(SK.VE.x(x1), SK.VE.x(y1)), +a2: VD.SameD(SK.VE.x(x2), SK.VE.x(y2)))
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(m1, x1, m2, x2))), E.qeval(p, SK.VE.x(DR.vlin(m1, y1, m2, y2)))):
  QA.add_cong(S.Q.mul(m1, E.qeval(p, SK.VE.x(x1))), S.Q.mul(m1, E.qeval(p, SK.VE.x(y1))), S.Q.mul(m2, E.qeval(p, SK.VE.x(x2))), S.Q.mul(m2, E.qeval(p, SK.VE.x(y2))),
    LQ.q_mul_cong_r(m1, E.qeval(p, SK.VE.x(x1)), E.qeval(p, SK.VE.x(y1)), ID.ident_ok(SK.VE.x(x1), SK.VE.x(y1), a1)(p)),
    LQ.q_mul_cong_r(m2, E.qeval(p, SK.VE.x(x2)), E.qeval(p, SK.VE.x(y2)), ID.ident_ok(SK.VE.x(x2), SK.VE.x(y2), a2)(p)))

def vcong.ay(+p: List<&2, S.Q>, +m1: S.Q, +x1: SK.VE, +y1: SK.VE, +m2: S.Q, +x2: SK.VE, +y2: SK.VE, +b1: VD.SameD(SK.VE.y(x1), SK.VE.y(y1)), +b2: VD.SameD(SK.VE.y(x2), SK.VE.y(y2)))
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(m1, x1, m2, x2))), E.qeval(p, SK.VE.y(DR.vlin(m1, y1, m2, y2)))):
  QA.add_cong(S.Q.mul(m1, E.qeval(p, SK.VE.y(x1))), S.Q.mul(m1, E.qeval(p, SK.VE.y(y1))), S.Q.mul(m2, E.qeval(p, SK.VE.y(x2))), S.Q.mul(m2, E.qeval(p, SK.VE.y(y2))),
    LQ.q_mul_cong_r(m1, E.qeval(p, SK.VE.y(x1)), E.qeval(p, SK.VE.y(y1)), ID.ident_ok(SK.VE.y(x1), SK.VE.y(y1), b1)(p)),
    LQ.q_mul_cong_r(m2, E.qeval(p, SK.VE.y(x2)), E.qeval(p, SK.VE.y(y2)), ID.ident_ok(SK.VE.y(x2), SK.VE.y(y2), b2)(p)))

def vcong.go(+m1: S.Q, +x1: SK.VE, +y1: SK.VE, +m2: S.Q, +x2: SK.VE, +y2: SK.VE, +a1: VD.SameD(SK.VE.x(x1), SK.VE.x(y1)), +b1: VD.SameD(SK.VE.y(x1), SK.VE.y(y1)), h2: VD.SameVD(x2, y2))
  -> VD.SameVD(DR.vlin(m1, x1, m2, x2), DR.vlin(m1, y1, m2, y2)):
  (+a2, +b2) = h2
  (ID.qzero_ident(SK.VE.x(DR.vlin(m1, x1, m2, x2)), SK.VE.x(DR.vlin(m1, y1, m2, y2)), p => vcong.ax(p, m1, x1, y1, m2, x2, y2, a1, a2)),
   ID.qzero_ident(SK.VE.y(DR.vlin(m1, x1, m2, x2)), SK.VE.y(DR.vlin(m1, y1, m2, y2)), p => vcong.ay(p, m1, x1, y1, m2, x2, y2, b1, b2)))

# x1 = y1 and x2 = y2 give m1 x1 + m2 x2 = m1 y1 + m2 y2
def vcong(+m1: S.Q, +x1: SK.VE, +y1: SK.VE, +m2: S.Q, +x2: SK.VE, +y2: SK.VE, h1: VD.SameVD(x1, y1), h2: VD.SameVD(x2, y2)) -> VD.SameVD(DR.vlin(m1, x1, m2, x2), DR.vlin(m1, y1, m2, y2)):
  (+a1, +b1) = h1
  vcong.go(m1, x1, y1, m2, x2, y2, a1, b1, h2)

def vv.q(+m1: S.Q, +a1: S.Q, +m2: S.Q, +a2: S.Q, +X: S.Q, +R1: S.Q, +R2: S.Q)
  -> S.Q.eq(S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.mul(a1, X), S.Q.mul(DR.qo(), R1))), S.Q.mul(m2, S.Q.add(S.Q.mul(a2, X), S.Q.mul(DR.qo(), R2)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(m1, R1), S.Q.mul(m2, R2))))):
  QA.ch4(S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.mul(a1, X), S.Q.mul(DR.qo(), R1))), S.Q.mul(m2, S.Q.add(S.Q.mul(a2, X), S.Q.mul(DR.qo(), R2)))),
    S.Q.add(S.Q.add(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(m1, S.Q.mul(DR.qo(), R1))), S.Q.add(S.Q.mul(m2, S.Q.mul(a2, X)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2)))),
    S.Q.add(S.Q.add(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(m2, S.Q.mul(a2, X))), S.Q.add(S.Q.mul(m1, S.Q.mul(DR.qo(), R1)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2)))),
    S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(m1, a1), X), S.Q.mul(S.Q.mul(m2, a2), X)), S.Q.add(S.Q.mul(DR.qo(), S.Q.mul(m1, R1)), S.Q.mul(DR.qo(), S.Q.mul(m2, R2)))),
    S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(m1, R1), S.Q.mul(m2, R2)))),
    QA.add_cong(S.Q.mul(m1, S.Q.add(S.Q.mul(a1, X), S.Q.mul(DR.qo(), R1))), S.Q.add(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(m1, S.Q.mul(DR.qo(), R1))), S.Q.mul(m2, S.Q.add(S.Q.mul(a2, X), S.Q.mul(DR.qo(), R2))), S.Q.add(S.Q.mul(m2, S.Q.mul(a2, X)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2))),
      QA.ldist(m1, S.Q.mul(a1, X), S.Q.mul(DR.qo(), R1)), QA.ldist(m2, S.Q.mul(a2, X), S.Q.mul(DR.qo(), R2))),
    QA.m4(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(m1, S.Q.mul(DR.qo(), R1)), S.Q.mul(m2, S.Q.mul(a2, X)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2))),
    QA.add_cong(S.Q.add(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(m2, S.Q.mul(a2, X))), S.Q.add(S.Q.mul(S.Q.mul(m1, a1), X), S.Q.mul(S.Q.mul(m2, a2), X)), S.Q.add(S.Q.mul(m1, S.Q.mul(DR.qo(), R1)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2))), S.Q.add(S.Q.mul(DR.qo(), S.Q.mul(m1, R1)), S.Q.mul(DR.qo(), S.Q.mul(m2, R2))),
      QA.add_cong(S.Q.mul(m1, S.Q.mul(a1, X)), S.Q.mul(S.Q.mul(m1, a1), X), S.Q.mul(m2, S.Q.mul(a2, X)), S.Q.mul(S.Q.mul(m2, a2), X), QA.ma(m1, a1, X), QA.ma(m2, a2, X)),
      QA.add_cong(S.Q.mul(m1, S.Q.mul(DR.qo(), R1)), S.Q.mul(DR.qo(), S.Q.mul(m1, R1)), S.Q.mul(m2, S.Q.mul(DR.qo(), R2)), S.Q.mul(DR.qo(), S.Q.mul(m2, R2)), QA.mswap(m1, DR.qo(), R1), QA.mswap(m2, DR.qo(), R2))),
    QA.add_cong(S.Q.add(S.Q.mul(S.Q.mul(m1, a1), X), S.Q.mul(S.Q.mul(m2, a2), X)), S.Q.mul(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), X), S.Q.add(S.Q.mul(DR.qo(), S.Q.mul(m1, R1)), S.Q.mul(DR.qo(), S.Q.mul(m2, R2))), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(m1, R1), S.Q.mul(m2, R2))),
      LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), X), S.Q.add(S.Q.mul(S.Q.mul(m1, a1), X), S.Q.mul(S.Q.mul(m2, a2), X)), QA.rdist(S.Q.mul(m1, a1), S.Q.mul(m2, a2), X)),
      LQ.q_sym(S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(m1, R1), S.Q.mul(m2, R2))), S.Q.add(S.Q.mul(DR.qo(), S.Q.mul(m1, R1)), S.Q.mul(DR.qo(), S.Q.mul(m2, R2))), QA.ldist(DR.qo(), S.Q.mul(m1, R1), S.Q.mul(m2, R2)))))

def vv.ax(+p: List<&2, S.Q>, +m1: S.Q, +a1: S.Q, +x: SK.VE, +r1: SK.VE, +m2: S.Q, +a2: S.Q, +r2: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(m1, DR.vlin(a1, x, DR.qo(), r1), m2, DR.vlin(a2, x, DR.qo(), r2)))), E.qeval(p, SK.VE.x(DR.vlin(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), x, DR.qo(), DR.vlin(m1, r1, m2, r2))))):
  vv.q(m1, a1, m2, a2, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(r1)), E.qeval(p, SK.VE.x(r2)))

def vv.ay(+p: List<&2, S.Q>, +m1: S.Q, +a1: S.Q, +x: SK.VE, +r1: SK.VE, +m2: S.Q, +a2: S.Q, +r2: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(m1, DR.vlin(a1, x, DR.qo(), r1), m2, DR.vlin(a2, x, DR.qo(), r2)))), E.qeval(p, SK.VE.y(DR.vlin(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), x, DR.qo(), DR.vlin(m1, r1, m2, r2))))):
  vv.q(m1, a1, m2, a2, E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(r1)), E.qeval(p, SK.VE.y(r2)))

# m1 (a1 x + r1) + m2 (a2 x + r2) = (m1 a1 + m2 a2) x + (m1 r1 + m2 r2)
def vv4(+m1: S.Q, +a1: S.Q, +x: SK.VE, +r1: SK.VE, +m2: S.Q, +a2: S.Q, +r2: SK.VE)
  -> VD.SameVD(DR.vlin(m1, DR.vlin(a1, x, DR.qo(), r1), m2, DR.vlin(a2, x, DR.qo(), r2)), DR.vlin(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), x, DR.qo(), DR.vlin(m1, r1, m2, r2))):
  (ID.qzero_ident(SK.VE.x(DR.vlin(m1, DR.vlin(a1, x, DR.qo(), r1), m2, DR.vlin(a2, x, DR.qo(), r2))), SK.VE.x(DR.vlin(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), x, DR.qo(), DR.vlin(m1, r1, m2, r2))), p => vv.ax(p, m1, a1, x, r1, m2, a2, r2)),
   ID.qzero_ident(SK.VE.y(DR.vlin(m1, DR.vlin(a1, x, DR.qo(), r1), m2, DR.vlin(a2, x, DR.qo(), r2))), SK.VE.y(DR.vlin(S.Q.add(S.Q.mul(m1, a1), S.Q.mul(m2, a2)), x, DR.qo(), DR.vlin(m1, r1, m2, r2))), p => vv.ay(p, m1, a1, x, r1, m2, a2, r2)))

def cb.q(+m1: S.Q, +m2: S.Q, +Z: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))), S.Q.mul(m2, S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)))), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))):
  QR.qring_eq([m1, m2, Z], E.QAdd{E.QMul{E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}}, E.QMul{E.QVar{1n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}}}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}, {==})

def cbase(+es: List<&2, SK.Ent>, +r: DR.Node, +m1: S.Q, +m2: S.Q) -> VD.SameVD(DR.vlin(m1, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), m2, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))):
  (ID.qzero_ident(SK.VE.x(DR.vlin(m1, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), m2, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => cb.q(m1, m2, E.qeval(p, SK.VE.x(DR.zdir(es, r))))),
   ID.qzero_ident(SK.VE.y(DR.vlin(m1, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), m2, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => cb.q(m1, m2, E.qeval(p, SK.VE.y(DR.zdir(es, r))))))

def ch.q(+Z: S.Q, +X: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)), S.Q.add(S.Q.mul(DR.qz(), X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))))):
  QR.qring_eq([Z, X], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}}}, {==})

def ch.ax(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +x: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), E.qeval(p, SK.VE.x(DR.vlin(DR.qz(), x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))))):
  ch.q(E.qeval(p, SK.VE.x(DR.zdir(es, r))), E.qeval(p, SK.VE.x(x)))

def ch.ay(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +x: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), E.qeval(p, SK.VE.y(DR.vlin(DR.qz(), x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))))):
  ch.q(E.qeval(p, SK.VE.y(DR.zdir(es, r))), E.qeval(p, SK.VE.y(x)))

# a combination's first step, for any coefficient list
def clin_ht(ls: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +x: SK.VE, +xt: List<&2, SK.VE>)
  -> VD.SameVD(HS.clin(es, r, ls, Con{x, xt}), DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), xt))):
  match ls:
    case Con{+l, +lt}:
      MG.samevd_refl(DR.vlin(l, x, DR.qo(), HS.clin(es, r, lt, xt)))
    case Nil{}:
      (ID.qzero_ident(SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), SK.VE.x(DR.vlin(DR.qz(), x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), p => ch.ax(p, es, r, x)),
       ID.qzero_ident(SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), SK.VE.y(DR.vlin(DR.qz(), x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), p => ch.ay(p, es, r, x)))

def clin_nil(ls: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node) -> VD.SameVD(HS.clin(es, r, ls, Nil{}), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))):
  match ls:
    case Con{+l, +lt}:
      MG.samevd_refl(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))
    case Nil{}:
      MG.samevd_refl(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))

# m1 ls1 + m2 ls2, cut to xs's length
def vlc(xs: List<&2, SK.VE>, +m1: S.Q, +ls1: List<&2, S.Q>, +m2: S.Q, +ls2: List<&2, S.Q>) -> List<&2, S.Q>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, xt}:
      Con{S.Q.add(S.Q.mul(m1, SN.qhd(ls1)), S.Q.mul(m2, SN.qhd(ls2))), vlc(xt, m1, SN.qtl(ls1), m2, SN.qtl(ls2))}

# m1 clin(ls1) + m2 clin(ls2) = clin(m1 ls1 + m2 ls2)
def clin_comb(xs: List<&2, SK.VE>, +es: List<&2, SK.Ent>, +r: DR.Node, +m1: S.Q, +ls1: List<&2, S.Q>, +m2: S.Q, +ls2: List<&2, S.Q>)
  -> VD.SameVD(DR.vlin(m1, HS.clin(es, r, ls1, xs), m2, HS.clin(es, r, ls2, xs)), HS.clin(es, r, vlc(xs, m1, ls1, m2, ls2), xs)):
  match xs:
    case Nil{}:
      GN.samevd_tr(DR.vlin(m1, HS.clin(es, r, ls1, Nil{}), m2, HS.clin(es, r, ls2, Nil{})), DR.vlin(m1, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), m2, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)),
        vcong(m1, HS.clin(es, r, ls1, Nil{}), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), m2, HS.clin(es, r, ls2, Nil{}), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), clin_nil(ls1, es, r), clin_nil(ls2, es, r)),
        cbase(es, r, m1, m2))
    case Con{+x, +xt}:
      GN.samevd_tr(DR.vlin(m1, HS.clin(es, r, ls1, Con{x, xt}), m2, HS.clin(es, r, ls2, Con{x, xt})),
        DR.vlin(m1, DR.vlin(SN.qhd(ls1), x, DR.qo(), HS.clin(es, r, SN.qtl(ls1), xt)), m2, DR.vlin(SN.qhd(ls2), x, DR.qo(), HS.clin(es, r, SN.qtl(ls2), xt))),
        HS.clin(es, r, vlc(Con{x, xt}, m1, ls1, m2, ls2), Con{x, xt}),
        vcong(m1, HS.clin(es, r, ls1, Con{x, xt}), DR.vlin(SN.qhd(ls1), x, DR.qo(), HS.clin(es, r, SN.qtl(ls1), xt)), m2, HS.clin(es, r, ls2, Con{x, xt}), DR.vlin(SN.qhd(ls2), x, DR.qo(), HS.clin(es, r, SN.qtl(ls2), xt)),
          clin_ht(ls1, es, r, x, xt), clin_ht(ls2, es, r, x, xt)),
        GN.samevd_tr(DR.vlin(m1, DR.vlin(SN.qhd(ls1), x, DR.qo(), HS.clin(es, r, SN.qtl(ls1), xt)), m2, DR.vlin(SN.qhd(ls2), x, DR.qo(), HS.clin(es, r, SN.qtl(ls2), xt))),
          DR.vlin(S.Q.add(S.Q.mul(m1, SN.qhd(ls1)), S.Q.mul(m2, SN.qhd(ls2))), x, DR.qo(), DR.vlin(m1, HS.clin(es, r, SN.qtl(ls1), xt), m2, HS.clin(es, r, SN.qtl(ls2), xt))),
          HS.clin(es, r, vlc(Con{x, xt}, m1, ls1, m2, ls2), Con{x, xt}),
          vv4(m1, SN.qhd(ls1), x, HS.clin(es, r, SN.qtl(ls1), xt), m2, SN.qhd(ls2), HS.clin(es, r, SN.qtl(ls2), xt)),
          vcong(S.Q.add(S.Q.mul(m1, SN.qhd(ls1)), S.Q.mul(m2, SN.qhd(ls2))), x, x, DR.qo(), DR.vlin(m1, HS.clin(es, r, SN.qtl(ls1), xt), m2, HS.clin(es, r, SN.qtl(ls2), xt)), HS.clin(es, r, vlc(xt, m1, SN.qtl(ls1), m2, SN.qtl(ls2)), xt),
            MG.samevd_refl(x), clin_comb(xt, es, r, m1, SN.qtl(ls1), m2, SN.qtl(ls2)))))

# Hull sets
# ---------

# y is a real combination of the hull's kept generators
def HIn(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +h: HS.HS, +y: SK.VE) -> Data:
  Sigma<&2, &2, List<&2, S.Q>, ls => VD.SameVD(y, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))))>

def enc_cong.at(+p: List<&2, S.Q>, +y1: SK.VE, +y2: SK.VE, +t: Nat, +h1: VD.SameD(SK.VE.x(y1), SK.VE.x(y2)), +h2: VD.SameD(SK.VE.y(y1), SK.VE.y(y2)))
  -> S.Q.eq(E.qeval(p, HS.enc(y1, t)), E.qeval(p, HS.enc(y2, t))):
  QA.add_cong(E.qeval(p, SK.VE.x(y1)), E.qeval(p, SK.VE.x(y2)), S.Q.mul(E.qeval(p, E.QVar{t}), E.qeval(p, SK.VE.y(y1))), S.Q.mul(E.qeval(p, E.QVar{t}), E.qeval(p, SK.VE.y(y2))),
    ID.ident_ok(SK.VE.x(y1), SK.VE.x(y2), h1)(p), LQ.q_mul_cong_r(E.qeval(p, E.QVar{t}), E.qeval(p, SK.VE.y(y1)), E.qeval(p, SK.VE.y(y2)), ID.ident_ok(SK.VE.y(y1), SK.VE.y(y2), h2)(p)))

def enc_cong(+y1: SK.VE, +y2: SK.VE, +t: Nat, h: VD.SameVD(y1, y2)) -> SV.Ident(HS.enc(y1, t), HS.enc(y2, t)):
  (+h1, +h2) = h
  p => enc_cong.at(p, y1, y2, t, h1, h2)

def enc_lin_sym.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +ls: List<&2, S.Q>, +xs: List<&2, SK.VE>)
  -> S.Q.eq(E.qeval(p, HS.enc(HS.clin(es, r, ls, xs), t)), E.qeval(p, SV.lin(ls, HS.encs(xs, t)))):
  LQ.q_sym(E.qeval(p, SV.lin(ls, HS.encs(xs, t))), E.qeval(p, HS.enc(HS.clin(es, r, ls, xs), t)), HP.enc_lin(es, r, t, ls, xs)(p))

def hin_bool.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)), +ls: List<&2, S.Q>, +sv: VD.SameVD(y, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h)))))
  -> {HS.hs.inb(h, y, t) == True{} : Bool}:
  ri.zero(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h), HS.enc(y, t), hr,
    SN.in_of_ident(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), ls, HP.ident_trans(HS.enc(y, t), HS.enc(HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))), t), SV.lin(ls, HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)),
      enc_cong(y, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))), t, sv), p => enc_lin_sym.at(p, es, r, t, ls, HS.hxs(es, fs, HS.hs.ds(h))))))

# a combination of the kept generators passes the hull's test
def hin_bool(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)), hi: HIn(es, fs, r, h, y))
  -> {HS.hs.inb(h, y, t) == True{} : Bool}:
  (+ls, +sv) = hi
  hin_bool.go(es, fs, r, t, h, y, hr, ls, sv)

def hin_of.go(+es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +xs: List<&2, SK.VE>, +y: SK.VE, +ls: List<&2, S.Q>, hid: SV.Ident(HS.enc(y, t), SV.lin(ls, HS.encs(xs, t))),
  hy: HP.VBelow(y, t), hc: HP.VBelow(HS.clin(es, r, ls, xs), t)) -> VD.SameVD(y, HS.clin(es, r, ls, xs)):
  MG.samevd_sym(HS.clin(es, r, ls, xs), y, VD.samevd_of(HS.clin(es, r, ls, xs), y,
    HP.hs_der.sep0(es, r, t, y, HS.clin(es, r, ls, xs), hy, hc, HP.ident_trans(HS.enc(y, t), SV.lin(ls, HS.encs(xs, t)), HS.enc(HS.clin(es, r, ls, xs), t), hid, HP.enc_lin(es, r, t, ls, xs)))))

def hin_of.sp(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE, +sp: SN.InSpan(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)),
  +hb: HP.AllBelow(HS.hxs(es, fs, HS.hs.ds(h)), t), +hzr: HP.VBelow(DR.zdir(es, r), t), +hy: HP.VBelow(y, t)) -> HIn(es, fs, r, h, y):
  (SN.in_ls(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), sp),
   hin_of.go(es, r, t, HS.hxs(es, fs, HS.hs.ds(h)), y, SN.in_ls(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), sp), SN.in_ident(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), sp), hy,
     HP.clin_below(es, r, t, SN.in_ls(HS.enc(y, t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), sp), HS.hxs(es, fs, HS.hs.ds(h)), hb, hzr)))

# a form below t passing the hull's test is a combination of its kept
# generators
def hin_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)),
  +hb: HP.AllBelow(HS.hxs(es, fs, HS.hs.ds(h)), t), +hzr: HP.VBelow(DR.zdir(es, r), t), +hy: HP.VBelow(y, t), hz: {HS.hs.inb(h, y, t) == True{} : Bool}) -> HIn(es, fs, r, h, y):
  hin_of.sp(es, fs, r, t, h, y, ri.in(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h), HS.enc(y, t), hr, hz), hb, hzr, hy)

def hin_tr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +h: HS.HS, +y1: SK.VE, +y2: SK.VE, hi: HIn(es, fs, r, h, y1), +e: VD.SameVD(y1, y2)) -> HIn(es, fs, r, h, y2):
  (+ls, +sv) = hi
  (ls, GN.samevd_tr(y2, y1, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))), MG.samevd_sym(y1, y2, e), sv))

def hin_lin.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +h: HS.HS, +m1: S.Q, +y1: SK.VE, +m2: S.Q, +y2: SK.VE, +ls1: List<&2, S.Q>, +sv1: VD.SameVD(y1, HS.clin(es, r, ls1, HS.hxs(es, fs, HS.hs.ds(h)))), h2: HIn(es, fs, r, h, y2))
  -> HIn(es, fs, r, h, DR.vlin(m1, y1, m2, y2)):
  (+ls2, +sv2) = h2
  (vlc(HS.hxs(es, fs, HS.hs.ds(h)), m1, ls1, m2, ls2), GN.samevd_tr(DR.vlin(m1, y1, m2, y2), DR.vlin(m1, HS.clin(es, r, ls1, HS.hxs(es, fs, HS.hs.ds(h))), m2, HS.clin(es, r, ls2, HS.hxs(es, fs, HS.hs.ds(h)))), HS.clin(es, r, vlc(HS.hxs(es, fs, HS.hs.ds(h)), m1, ls1, m2, ls2), HS.hxs(es, fs, HS.hs.ds(h))),
    vcong(m1, y1, HS.clin(es, r, ls1, HS.hxs(es, fs, HS.hs.ds(h))), m2, y2, HS.clin(es, r, ls2, HS.hxs(es, fs, HS.hs.ds(h))), sv1, sv2), clin_comb(HS.hxs(es, fs, HS.hs.ds(h)), es, r, m1, ls1, m2, ls2)))

def hin_lin(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +h: HS.HS, +m1: S.Q, +y1: SK.VE, +m2: S.Q, +y2: SK.VE, h1: HIn(es, fs, r, h, y1), h2: HIn(es, fs, r, h, y2))
  -> HIn(es, fs, r, h, DR.vlin(m1, y1, m2, y2)):
  (+ls1, +sv1) = h1
  hin_lin.go(es, fs, r, h, m1, y1, m2, y2, ls1, sv1, h2)

# Lists of derivations by position
# --------------------------------

def dat(ds: List<&2, DR.Der>, n: Nat) -> Maybe<&2, DR.Der>:
  match ds n:
    case Nil{} n:
      None{}
    case Con{d, tl} 0n:
      Some{d}
    case Con{d, tl} 1n+m:
      dat(tl, m)

# d is in ds
def InD(+d: DR.Der, +ds: List<&2, DR.Der>) -> Data:
  Sigma<&2, &2, Nat, n => {dat(ds, n) == Some{d} : Maybe<&2, DR.Der>}>

def dis_some(m: Maybe<&2, DR.Der>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def dsome_or(m: Maybe<&2, DR.Der>, +d: DR.Der) -> DR.Der:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def dsome_inj(+x: DR.Der, +y: DR.Der, h: {Some{x} == Some{y} : Maybe<&2, DR.Der>}) -> {x == y : DR.Der}:
  Equal.cong(Maybe<&2, DR.Der>, DR.Der, m => dsome_or(m, x), Some{x}, Some{y}, h)

def dnone_some(+y: DR.Der, h: {None{} == Some{y} : Maybe<&2, DR.Der>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DR.Der>, Bool, m => dis_some(m), None{}, Some{y}, h)) : PP.none_some.p(_)
  Unit{}

def ind_hd(+d: DR.Der, +tl: List<&2, DR.Der>) -> InD(d, Con{d, tl}):
  (0n, {==})

def ind_tl.go(+d: DR.Der, +h0: DR.Der, +tl: List<&2, DR.Der>, +n: Nat, +e: {dat(tl, n) == Some{d} : Maybe<&2, DR.Der>}) -> InD(d, Con{h0, tl}):
  (1n+n, e)

def ind_tl(+d: DR.Der, +h0: DR.Der, +tl: List<&2, DR.Der>, h: InD(d, tl)) -> InD(d, Con{h0, tl}):
  (+n, +e) = h
  ind_tl.go(d, h0, tl, n, e)

def dat_cat_l(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, n: Nat, +d: DR.Der, e: {dat(xs, n) == Some{d} : Maybe<&2, DR.Der>}) -> {dat(DC.dcat(xs, ys), n) == Some{d} : Maybe<&2, DR.Der>}:
  match xs n:
    case Nil{} n:
      absurd({dat(DC.dcat(Nil{}, ys), n) == Some{d} : Maybe<&2, DR.Der>}, dnone_some(d, e))
    case Con{+x, +xt} 0n:
      e
    case Con{+x, +xt} 1n+m:
      dat_cat_l(xt, ys, m, d, e)

def dlen_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +n: Nat, +d: DR.Der, e: {dat(ys, n) == Some{d} : Maybe<&2, DR.Der>}) -> {dat(DC.dcat(xs, ys), Nat.add(DC.dlen(xs), n)) == Some{d} : Maybe<&2, DR.Der>}:
  match xs:
    case Nil{}:
      e
    case Con{+x, +xt}:
      dlen_cat(xt, ys, n, d, e)

def ind_cat_l.go(+d: DR.Der, +xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +n: Nat, +e: {dat(xs, n) == Some{d} : Maybe<&2, DR.Der>}) -> InD(d, DC.dcat(xs, ys)):
  (n, dat_cat_l(xs, ys, n, d, e))

def ind_cat_l(+d: DR.Der, +xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, h: InD(d, xs)) -> InD(d, DC.dcat(xs, ys)):
  (+n, +e) = h
  ind_cat_l.go(d, xs, ys, n, e)

def ind_cat_r.go(+d: DR.Der, +xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +n: Nat, +e: {dat(ys, n) == Some{d} : Maybe<&2, DR.Der>}) -> InD(d, DC.dcat(xs, ys)):
  (Nat.add(DC.dlen(xs), n), dlen_cat(xs, ys, n, d, e))

def ind_cat_r(+d: DR.Der, +xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, h: InD(d, ys)) -> InD(d, DC.dcat(xs, ys)):
  (+n, +e) = h
  ind_cat_r.go(d, xs, ys, n, e)

# Adding a row
# ------------

def ri.len(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +x: EL.Row, hl: {EL.rlen(rows) == SV.neqs(B) : Nat}) -> {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(EP.qsnoc(B, e)) : Nat}:
  %Equal.sym(Nat, SV.neqs(EP.qsnoc(B, e)), 1n+SV.neqs(B), CW.neqs_qsnoc(B, e)) : {EL.rlen(EL.rsnoc(rows, x)) == _ : Nat}
  %Equal.sym(Nat, EL.rlen(EL.rsnoc(rows, x)), 1n+EL.rlen(rows), CW.rlen_rsnoc(rows, x)) : {_ == 1n+SV.neqs(B) : Nat}
  %Equal.sym(Nat, EL.rlen(rows), SV.neqs(B), hl) : {1n+_ == 1n+SV.neqs(B) : Nat}
  {==}

# a new row: the rows decide the span of B and e
def ri.snoc(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: RI(B, rows), +hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool})
  -> RI(EP.qsnoc(B, e), EL.rsnoc(rows, EL.row_of(EL.resid(rows, e)))):
  (+hr, +hl) = h
  (EP.new_rinv(B, rows, e, hr, hl, hne), ri.len(B, rows, e, EL.row_of(EL.resid(rows, e)), hl))

# hs: adding d keeps the rows deciding the span, d passes, and so does
# everything that passed

def hs_add.ri(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) : Bool}, +hr: RI(HS.encs(HS.hxs(es, fs, ds), t), rows))
  -> RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d))), t), HS.hs.rows(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d))):
  match b:
    case True{}:
      hr
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, d)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), HP.encs_snoc(es, fs, t, ds, d)) : RI(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))))
      ri.snoc(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb))

def hs_add.new(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) : Bool}, +hr: RI(HS.encs(HS.hxs(es, fs, ds), t), rows))
  -> Inb(HS.hs.rows(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)):
  match b:
    case True{}:
      Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb)
    case False{}:
      ri.zero(EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), ri.snoc(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb)), SN.in_last(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))

def hs_add.mono(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) : Bool}, +hr: RI(HS.encs(HS.hxs(es, fs, ds), t), rows), hz: Inb(rows, e))
  -> Inb(HS.hs.rows(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d)), e):
  match b:
    case True{}:
      hz
    case False{}:
      ri.zero(EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), e, ri.snoc(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb)),
        SN.in_snoc(e, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), ri.in(HS.encs(HS.hxs(es, fs, ds), t), rows, e, hr, hz)))

def hs_add_ri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +d: DR.Der, hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h))) -> RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(HS.hs.add(es, fs, t, h, d))), t), HS.hs.rows(HS.hs.add(es, fs, t, h, d))):
  match h:
    case HS.HS{+rows, +ds}:
      hs_add.ri(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), es, fs, t, rows, ds, d, {==}, hr)

def hs_add_new(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +d: DR.Der, hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h))) -> Inb(HS.hs.rows(HS.hs.add(es, fs, t, h, d)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)):
  match h:
    case HS.HS{+rows, +ds}:
      hs_add.new(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), es, fs, t, rows, ds, d, {==}, hr)

def hs_add_mono(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +d: DR.Der, +e: E.QExpr, hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)), hz: Inb(HS.hs.rows(h), e)) -> Inb(HS.hs.rows(HS.hs.add(es, fs, t, h, d)), e):
  match h:
    case HS.HS{+rows, +ds}:
      hs_add.mono(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), es, fs, t, rows, ds, d, e, {==}, hr, hz)

def hs_fold_ri(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h))) -> RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(ds, es, fs, t, h))), t), HS.hs.rows(DC.hfold(ds, es, fs, t, h))):
  match ds:
    case Nil{}:
      hr
    case Con{+d0, tl}:
      hs_fold_ri(tl, es, fs, t, HS.hs.add(es, fs, t, h, d0), hs_add_ri(es, fs, t, h, d0, hr))

def hs_fold_mono(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +e: E.QExpr, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)), hz: Inb(HS.hs.rows(h), e)) -> Inb(HS.hs.rows(DC.hfold(ds, es, fs, t, h)), e):
  match ds:
    case Nil{}:
      hz
    case Con{+d0, tl}:
      hs_fold_mono(tl, es, fs, t, HS.hs.add(es, fs, t, h, d0), e, hs_add_ri(es, fs, t, h, d0, hr), hs_add_mono(es, fs, t, h, d0, e, hr, hz))

# every derivation folded in passes
def hs_fold_in(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +d: DR.Der, n: Nat, en: {dat(ds, n) == Some{d} : Maybe<&2, DR.Der>}, +hr: RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h))) -> Inb(HS.hs.rows(DC.hfold(ds, es, fs, t, h)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)):
  match ds n:
    case Nil{} n:
      absurd(Inb(HS.hs.rows(DC.hfold(Nil{}, es, fs, t, h)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), dnone_some(d, en))
    case Con{+d0, +tl} 0n:
      %dsome_inj(d0, d, en) : Inb(HS.hs.rows(DC.hfold(Con{d0, tl}, es, fs, t, h)), HS.enc(DR.Jd.x(DR.concl(es, fs, _)), t))
      hs_fold_mono(tl, es, fs, t, HS.hs.add(es, fs, t, h, d0), HS.enc(DR.Jd.x(DR.concl(es, fs, d0)), t), hs_add_ri(es, fs, t, h, d0, hr), hs_add_new(es, fs, t, h, d0, hr))
    case Con{+d0, +tl} 1n+m:
      hs_fold_in(tl, es, fs, t, HS.hs.add(es, fs, t, h, d0), d, m, en, hs_add_ri(es, fs, t, h, d0, hr))

# ks: adding d keeps the rows deciding the span, d passes, and so does
# everything that passed

def ks_add.ri(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) : Bool}, +hr: RI(KS.kexprs(es, fs, ds), rows))
  -> RI(KS.kexprs(es, fs, KS.ks.ds(KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d))), KS.ks.rows(KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d))):
  match b:
    case True{}:
      hr
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, KS.kexprs(es, fs, KS.dsnoc(ds, d)), EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), KP.kexprs_snoc(es, fs, ds, d)) : RI(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))))
      ri.snoc(KS.kexprs(es, fs, ds), rows, DR.Jd.e(DR.concl(es, fs, d)), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb))

def ks_add.new(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) : Bool}, +hr: RI(KS.kexprs(es, fs, ds), rows))
  -> Inb(KS.ks.rows(KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d)), DR.Jd.e(DR.concl(es, fs, d))):
  match b:
    case True{}:
      Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb)
    case False{}:
      ri.zero(EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), DR.Jd.e(DR.concl(es, fs, d)), ri.snoc(KS.kexprs(es, fs, ds), rows, DR.Jd.e(DR.concl(es, fs, d)), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb)), SN.in_last(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))))

def ks_add.mono(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) : Bool}, +hr: RI(KS.kexprs(es, fs, ds), rows), hz: Inb(rows, e))
  -> Inb(KS.ks.rows(KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d)), e):
  match b:
    case True{}:
      hz
    case False{}:
      ri.zero(EP.qsnoc(KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), e, ri.snoc(KS.kexprs(es, fs, ds), rows, DR.Jd.e(DR.concl(es, fs, d)), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb)),
        SN.in_snoc(e, KS.kexprs(es, fs, ds), DR.Jd.e(DR.concl(es, fs, d)), ri.in(KS.kexprs(es, fs, ds), rows, e, hr, hz)))

def ks_add_ri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: KS.KS, +d: DR.Der, hr: RI(KS.kexprs(es, fs, KS.ks.ds(h)), KS.ks.rows(h))) -> RI(KS.kexprs(es, fs, KS.ks.ds(KS.ks.add(es, fs, h, d))), KS.ks.rows(KS.ks.add(es, fs, h, d))):
  match h:
    case KS.KS{+rows, +ds}:
      ks_add.ri(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), es, fs, rows, ds, d, {==}, hr)

def ks_add_new(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: KS.KS, +d: DR.Der, hr: RI(KS.kexprs(es, fs, KS.ks.ds(h)), KS.ks.rows(h))) -> Inb(KS.ks.rows(KS.ks.add(es, fs, h, d)), DR.Jd.e(DR.concl(es, fs, d))):
  match h:
    case KS.KS{+rows, +ds}:
      ks_add.new(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), es, fs, rows, ds, d, {==}, hr)

def ks_add_mono(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, h: KS.KS, +d: DR.Der, +e: E.QExpr, hr: RI(KS.kexprs(es, fs, KS.ks.ds(h)), KS.ks.rows(h)), hz: Inb(KS.ks.rows(h), e)) -> Inb(KS.ks.rows(KS.ks.add(es, fs, h, d)), e):
  match h:
    case KS.KS{+rows, +ds}:
      ks_add.mono(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), es, fs, rows, ds, d, e, {==}, hr, hz)

# ts: adding d keeps the rows deciding the span, d passes, and so does
# everything that passed

def ts_add.ri(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))) : Bool}, +hr: RI(DC.crosses(es, fs, u, ds), rows))
  -> RI(DC.crosses(es, fs, u, DC.ts.ds(DC.ts.pick(b, rows, ds, EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), d))), DC.ts.rows(DC.ts.pick(b, rows, ds, EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), d))):
  match b:
    case True{}:
      hr
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, KS.dsnoc(ds, d)), EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), RP.crosses_snoc(es, fs, u, ds, d)) : RI(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))))
      ri.snoc(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), eb))

def ts_add.new(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, eb: {b == EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))) : Bool}, +hr: RI(DC.crosses(es, fs, u, ds), rows))
  -> Inb(DC.ts.rows(DC.ts.pick(b, rows, ds, EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), d)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))):
  match b:
    case True{}:
      Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), eb)
    case False{}:
      ri.zero(EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), ri.snoc(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), eb)), SN.in_last(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))

def ts_add.mono(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))) : Bool}, +hr: RI(DC.crosses(es, fs, u, ds), rows), hz: Inb(rows, e))
  -> Inb(DC.ts.rows(DC.ts.pick(b, rows, ds, EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), d)), e):
  match b:
    case True{}:
      hz
    case False{}:
      ri.zero(EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), e, ri.snoc(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), hr, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), eb)),
        SN.in_snoc(e, DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), ri.in(DC.crosses(es, fs, u, ds), rows, e, hr, hz)))

def ts_add_ri(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, h: DC.TS, +d: DR.Der, hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h))) -> RI(DC.crosses(es, fs, u, DC.ts.ds(DC.ts.add(es, fs, u, h, d))), DC.ts.rows(DC.ts.add(es, fs, u, h, d))):
  match h:
    case DC.TS{+rows, +ds}:
      ts_add.ri(EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), es, fs, u, rows, ds, d, {==}, hr)

def ts_add_new(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, h: DC.TS, +d: DR.Der, hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h))) -> Inb(DC.ts.rows(DC.ts.add(es, fs, u, h, d)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))):
  match h:
    case DC.TS{+rows, +ds}:
      ts_add.new(EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), es, fs, u, rows, ds, d, {==}, hr)

def ts_add_mono(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, h: DC.TS, +d: DR.Der, +e: E.QExpr, hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h)), hz: Inb(DC.ts.rows(h), e)) -> Inb(DC.ts.rows(DC.ts.add(es, fs, u, h, d)), e):
  match h:
    case DC.TS{+rows, +ds}:
      ts_add.mono(EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), es, fs, u, rows, ds, d, e, {==}, hr, hz)

def ts_fold_ri(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +h: DC.TS, +hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h))) -> RI(DC.crosses(es, fs, u, DC.ts.ds(DC.tfold(ds, es, fs, u, h))), DC.ts.rows(DC.tfold(ds, es, fs, u, h))):
  match ds:
    case Nil{}:
      hr
    case Con{+d0, tl}:
      ts_fold_ri(tl, es, fs, u, DC.ts.add(es, fs, u, h, d0), ts_add_ri(es, fs, u, h, d0, hr))

def ts_fold_mono(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +h: DC.TS, +e: E.QExpr, +hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h)), hz: Inb(DC.ts.rows(h), e)) -> Inb(DC.ts.rows(DC.tfold(ds, es, fs, u, h)), e):
  match ds:
    case Nil{}:
      hz
    case Con{+d0, tl}:
      ts_fold_mono(tl, es, fs, u, DC.ts.add(es, fs, u, h, d0), e, ts_add_ri(es, fs, u, h, d0, hr), ts_add_mono(es, fs, u, h, d0, e, hr, hz))

# every derivation folded in passes
def ts_fold_in(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +h: DC.TS, +d: DR.Der, n: Nat, en: {dat(ds, n) == Some{d} : Maybe<&2, DR.Der>}, +hr: RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h))) -> Inb(DC.ts.rows(DC.tfold(ds, es, fs, u, h)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))):
  match ds n:
    case Nil{} n:
      absurd(Inb(DC.ts.rows(DC.tfold(Nil{}, es, fs, u, h)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), dnone_some(d, en))
    case Con{+d0, +tl} 0n:
      %dsome_inj(d0, d, en) : Inb(DC.ts.rows(DC.tfold(Con{d0, tl}, es, fs, u, h)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, _))))
      ts_fold_mono(tl, es, fs, u, DC.ts.add(es, fs, u, h, d0), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d0))), ts_add_ri(es, fs, u, h, d0, hr), ts_add_new(es, fs, u, h, d0, hr))
    case Con{+d0, +tl} 1n+m:
      ts_fold_in(tl, es, fs, u, DC.ts.add(es, fs, u, h, d0), d, m, en, ts_add_ri(es, fs, u, h, d0, hr))
