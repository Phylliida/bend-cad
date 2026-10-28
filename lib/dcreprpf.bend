# bend-cad: the closure theorem's represented sets (PLAN-sk13b B3,
# "Closure of a fixpoint"). Repr says what a fixpoint's state holds about a
# judgment: K(e) is e in K; par(a, x) is, for a node with a record (root r,
# label w), w x in r's set, and for one without, x in its collapsed set
# (F always has a record). Here: the hypotheses at a fixpoint, and Repr
# moved along SameV, closed under combinations, and holding K squared.
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
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The hypotheses at a fixpoint
# ----------------------------

def Hyp(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk) -> Data:
  SK.Both(FX.FixOut(es, fs, ctx, t, DC.segids(es), DC.OFix{s}), SK.Both({DC.zb(es, t) == True{} : Bool}, {DC.fb(fs, t) == True{} : Bool}))

def h.sk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, H: Hyp(es, fs, ctx, t, s)) -> RD.SkInv(es, fs, ctx, t, s):
  (a, r1) = H
  (b, r2) = a
  b

def h.sh(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, H: Hyp(es, fs, ctx, t, s)) -> SH.ShInv(es, fs, OP.cspan(ctx), DC.segids(es), s):
  (a, r1) = H
  (b, r2) = a
  (c, d) = r2
  c

def h.fx(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, H: Hyp(es, fs, ctx, t, s)) -> FX.Fx(es, fs, t, OP.cspan(ctx), DC.segids(es), s):
  (a, r1) = H
  (b, r2) = a
  (c, d) = r2
  d

def h.z(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, H: Hyp(es, fs, ctx, t, s)) -> {DC.zb(es, t) == True{} : Bool}:
  (a, r1) = H
  (b, c) = r1
  b

def h.b(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, H: Hyp(es, fs, ctx, t, s)) -> {DC.fb(fs, t) == True{} : Bool}:
  (a, r1) = H
  (b, c) = r1
  c

def sk.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)):
  (a, r1) = h
  a

def sk.ms(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)):
  (a, r1) = h
  (b, r2) = r1
  b

def sk.ls(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  c

def sk.msn(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> RP.MsNz(DC.Sk.ms(s)):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, e) = r3
  d

def sk.lsn(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> RP.LsNz(DC.Sk.ls(s)):
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, e) = r3
  e

def h.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)):
  sk.k(es, fs, ctx, t, s, h.sk(es, fs, ctx, t, s, H))

def h.ms(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)):
  sk.ms(es, fs, ctx, t, s, h.sk(es, fs, ctx, t, s, H))

def h.ls(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)):
  sk.ls(es, fs, ctx, t, s, h.sk(es, fs, ctx, t, s, H))

def h.msn(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> RP.MsNz(DC.Sk.ms(s)):
  sk.msn(es, fs, ctx, t, s, h.sk(es, fs, ctx, t, s, H))

def h.lsn(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> RP.LsNz(DC.Sk.ls(s)):
  sk.lsn(es, fs, ctx, t, s, h.sk(es, fs, ctx, t, s, H))

# Represented sets
# ----------------

def rp.n(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk) -> ST.St:
  match a:
    case DR.NFrame{}:
      ST.SF{}
    case DR.NSeg{+c}:
      ND.cset(DC.crep(es, fs, t, s, c), c)

def rp.m(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +a: DR.Node, +x: SK.VE) -> Data:
  match m:
    case Some{DC.Mem{a2, +r, +w, d}}:
      ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, x))
    case None{}:
      ST.InSt(es, fs, DC.Sk.k(s), rp.n(a, es, fs, t, s), x)

# what the state holds about a judgment
def Repr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, j: DR.Jd) -> Data:
  match j:
    case DR.JK{+e}:
      {KS.ks.inb(DC.Sk.k(s), e) == True{} : Bool}
    case DR.JP{+a, +x}:
      rp.m(DC.mem_of(DC.Sk.ms(s), a), es, fs, t, s, a, x)

# the sets of nodes without a record hold K squared
def sok_n(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> ND.SOk(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s)):
  match a:
    case DR.NFrame{}:
      ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H))
    case DR.NSeg{+c}:
      ND.sok_coll(es, fs, ctx, t, s, c, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))

# Moving, combining, K squared
# ----------------------------

def rp_tr(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +x1: SK.VE, +x2: SK.VE, h: rp.m(m, es, fs, t, s, a, x1), +e: VD.SameVD(x1, x2)) -> rp.m(m, es, fs, t, s, a, x2):
  match m:
    case Some{DC.Mem{a2, +r, +w, d}}:
      ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, x1), DR.gmul(w, x2), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), ND.sok_root(es, fs, ctx, t, s, r, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))), h,
        MG.gmul_cong(w, x1, x2, e))
    case None{}:
      ST.st_tr(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s), x1, x2, ND.sok_ok(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s), sok_n(a, es, fs, ctx, t, s, H)), h, e)

def rp_lin(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, h1: rp.m(m, es, fs, t, s, a, x1), h2: rp.m(m, es, fs, t, s, a, x2))
  -> rp.m(m, es, fs, t, s, a, DR.vlin(m1, x1, m2, x2)):
  match m:
    case Some{DC.Mem{a2, +r, +w, d}}:
      ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.vlin(m1, DR.gmul(w, x1), m2, DR.gmul(w, x2)), DR.gmul(w, DR.vlin(m1, x1, m2, x2)),
        ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), ND.sok_root(es, fs, ctx, t, s, r, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))),
        ST.st_lin(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), m1, DR.gmul(w, x1), m2, DR.gmul(w, x2), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), ND.sok_root(es, fs, ctx, t, s, r, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))), h1, h2),
        MG.samevd_sym(DR.gmul(w, DR.vlin(m1, x1, m2, x2)), DR.vlin(m1, DR.gmul(w, x1), m2, DR.gmul(w, x2)), LA.gmul_vlin(w, m1, x1, m2, x2)))
    case None{}:
      ST.st_lin(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s), m1, x1, m2, x2, ND.sok_ok(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s), sok_n(a, es, fs, ctx, t, s, H)), h1, h2)

def rk.q(+c: S.Q, +X: S.Q, +s0: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(c, X), S.Q.mul(S.Q.neg(s0), Y)), S.Q.sub(S.Q.mul(c, X), S.Q.mul(s0, Y))):
  QR.qring_eq([c, X, s0, Y], E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QNeg{E.QVar{2n}}, E.QVar{3n}}}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{2n}, E.QVar{3n}}}, {==})

def rk.at(+p: List<&2, S.Q>, +c: S.Q, +s0: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, ST.lin2(c, SK.VE.x(x), S.Q.neg(s0), SK.VE.y(x))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s0}, x)))):
  rk.q(c, E.qeval(p, SK.VE.x(x)), s0, E.qeval(p, SK.VE.y(x)))

def k2g.go(+c: S.Q, +s0: S.Q, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  +hx: {KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}, +hy: {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}) -> SK.Both({KS.ks.inb(k, SK.VE.x(DR.gmul(DR.Lab{c, s0}, x))) == True{} : Bool}, {KS.ks.inb(k, SK.VE.y(DR.gmul(DR.Lab{c, s0}, x))) == True{} : Bool}):
  (ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), ST.lin2(c, SK.VE.x(x), S.Q.neg(s0), SK.VE.y(x)), SK.VE.x(DR.gmul(DR.Lab{c, s0}, x)), hr,
     ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), c, SK.VE.x(x), S.Q.neg(s0), SK.VE.y(x), hr, hx, hy),
     ID.qzero_ident(ST.lin2(c, SK.VE.x(x), S.Q.neg(s0), SK.VE.y(x)), SK.VE.x(DR.gmul(DR.Lab{c, s0}, x)), p => rk.at(p, c, s0, x))),
   ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), s0, SK.VE.x(x), c, SK.VE.y(x), hr, hx, hy))

# a rotation of K squared is in K squared
def k2_gmul(w: DR.Lab, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  +hx: {KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}, +hy: {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}) -> SK.Both({KS.ks.inb(k, SK.VE.x(DR.gmul(w, x))) == True{} : Bool}, {KS.ks.inb(k, SK.VE.y(DR.gmul(w, x))) == True{} : Bool}):
  match w:
    case DR.Lab{+c, +s0}:
      k2g.go(c, s0, es, fs, k, x, hr, hx, hy)

def k2b.x(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, h: SK.Both({KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}, {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}))
  -> {KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}:
  (a, b) = h
  a

def k2b.y(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, h: SK.Both({KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}, {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}))
  -> {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}:
  (a, b) = h
  b

# a form with both parts in K is represented at every node
def rp_k2(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, +hx: {KS.ks.inb(DC.Sk.k(s), SK.VE.x(x)) == True{} : Bool}, +hy: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(x)) == True{} : Bool})
  -> rp.m(m, es, fs, t, s, a, x):
  match m:
    case Some{DC.Mem{a2, +r, +w, d}}:
      ND.k2_in(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, x), ND.sok_root(es, fs, ctx, t, s, r, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)),
        k2b.x(es, fs, DC.Sk.k(s), DR.gmul(w, x), k2_gmul(w, es, fs, DC.Sk.k(s), x, ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), hx, hy)), k2b.y(es, fs, DC.Sk.k(s), DR.gmul(w, x), k2_gmul(w, es, fs, DC.Sk.k(s), x, ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), hx, hy)))
    case None{}:
      ND.k2_in(es, fs, t, DC.Sk.k(s), rp.n(a, es, fs, t, s), x, sok_n(a, es, fs, ctx, t, s, H), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), hx, hy)
