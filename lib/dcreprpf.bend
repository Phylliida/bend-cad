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
import ./labnzpf.bend as NZ
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX
import ./dcreadpf.bend as RF

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

# Records at a position
# ---------------------

def mok_at(ms: List<&2, DC.Mem>, n: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +m: DC.Mem,
  en: {SH.mat(ms, n) == Some{m} : Maybe<&2, DC.Mem>}, h: GN.MsOk(es, fs, ctx, t, ms)) -> GN.MOkD(es, fs, ctx, t, m):
  match ms n:
    case Nil{} n:
      absurd(GN.MOkD(es, fs, ctx, t, m), SH.mnone_some(m, en))
    case Con{+m0, tl} 0n:
      (a, rt) = h
      %SH.msome_inj(m0, m, en) : GN.MOkD(es, fs, ctx, t, _)
      a
    case Con{+m0, tl} 1n+j:
      (a, rt) = h
      mok_at(tl, j, es, fs, ctx, t, m, en, rt)

def mnz.of(m: DC.Mem) -> Data:
  match m:
    case DC.Mem{a, r, +w, d}:
      NZ.Nz(w)

def mnz.hd(m0: DC.Mem, +tl: List<&2, DC.Mem>, h: RP.MsNz(Con{m0, tl})) -> mnz.of(m0):
  match m0:
    case DC.Mem{a, r, +w, d}:
      (b, c) = h
      b

def mnz.tl(m0: DC.Mem, +tl: List<&2, DC.Mem>, h: RP.MsNz(Con{m0, tl})) -> RP.MsNz(tl):
  match m0:
    case DC.Mem{a, r, +w, d}:
      (b, c) = h
      c

def mnz_at(ms: List<&2, DC.Mem>, n: Nat, +m: DC.Mem, en: {SH.mat(ms, n) == Some{m} : Maybe<&2, DC.Mem>}, h: RP.MsNz(ms)) -> mnz.of(m):
  match ms n:
    case Nil{} n:
      absurd(mnz.of(m), SH.mnone_some(m, en))
    case Con{+m0, +tl} 0n:
      %SH.msome_inj(m0, m, en) : mnz.of(_)
      mnz.hd(m0, tl, h)
    case Con{+m0, +tl} 1n+j:
      mnz_at(tl, j, m, en, mnz.tl(m0, tl, h))

def rr_at(ms: List<&2, DC.Mem>, n: Nat, +m: DC.Mem, en: {SH.mat(ms, n) == Some{m} : Maybe<&2, DC.Mem>}, h: SH.AllRR(ms)) -> SH.rrok(m):
  match ms n:
    case Nil{} n:
      absurd(SH.rrok(m), SH.mnone_some(m, en))
    case Con{+m0, tl} 0n:
      (a, rt) = h
      %SH.msome_inj(m0, m, en) : SH.rrok(_)
      a
    case Con{+m0, tl} 1n+j:
      (a, rt) = h
      rr_at(tl, j, m, en, rt)

def rok_at(sc: List<&2, DC.Mem>, n: Nat, +ms: List<&2, DC.Mem>, +m: DC.Mem, en: {SH.mat(sc, n) == Some{m} : Maybe<&2, DC.Mem>}, h: SH.RootsOk(sc, ms)) -> {SH.isroot(ms, DC.Mem.r(m)) == True{} : Bool}:
  match sc n:
    case Nil{} n:
      absurd({SH.isroot(ms, DC.Mem.r(m)) == True{} : Bool}, SH.mnone_some(m, en))
    case Con{+m0, tl} 0n:
      (a, rt) = h
      %SH.msome_inj(m0, m, en) : {SH.isroot(ms, DC.Mem.r(_)) == True{} : Bool}
      a
    case Con{+m0, tl} 1n+j:
      (a, rt) = h
      rok_at(tl, j, ms, m, en, rt)

# Root records
# ------------

def ne_tt(+a: DR.Node, +r2: DR.Node, +r: DR.Node, ea: {a == r : DR.Node}, er: {r2 == r : DR.Node}) -> {DC.node_eq(a, r2) == True{} : Bool}:
  %Equal.sym(DR.Node, a, r, ea) : {DC.node_eq(_, r2) == True{} : Bool}
  %Equal.sym(DR.Node, r2, r, er) : {DC.node_eq(r, _) == True{} : Bool}
  SH.node_refl(r)

def rootrec.go(+a: DR.Node, +r2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, ea: {a == r : DR.Node}, +er: {r2 == r : DR.Node},
  rr: SH.rrok.go(DC.node_eq(a, r2), a, r2, w, d)) -> {DC.Mem{a, r2, w, d} == DC.Mem{r, r, DC.lone(), DR.DSelf{r}} : DC.Mem}:
  %er : {DC.Mem{a, r2, w, d} == DC.Mem{_, _, DC.lone(), DR.DSelf{_}} : DC.Mem}
  %ne_tt(a, r2, r, ea, er) : SH.rrok.go(_, a, r2, w, d)
  rr

def rootrec.s(+ms: List<&2, DC.Mem>, +r: DR.Node, +a: DR.Node, +r2: DR.Node, +w: DR.Lab, +d: DR.Der, em: {DC.mem_of(ms, r) == Some{DC.Mem{a, r2, w, d}} : Maybe<&2, DC.Mem>},
  hr: {DC.node_eq(r2, r) == True{} : Bool}, hrr: SH.AllRR(ms), +n: Nat, +en: {SH.mat(ms, n) == Some{DC.Mem{a, r2, w, d}} : Maybe<&2, DC.Mem>}, hn: {DC.node_eq(a, r) == True{} : Bool})
  -> {DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}:
  Equal.trans(Maybe<&2, DC.Mem>, DC.mem_of(ms, r), Some{DC.Mem{a, r2, w, d}}, Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}}, em,
    Equal.cong(DC.Mem, Maybe<&2, DC.Mem>, x => Some{x}, DC.Mem{a, r2, w, d}, DC.Mem{r, r, DC.lone(), DR.DSelf{r}},
      rootrec.go(a, r2, r, w, d, GN.node_eq_ok(a, r, hn), GN.node_eq_ok(r2, r, hr), rr_at(ms, n, DC.Mem{a, r2, w, d}, en, hrr))))

def rootrec.n(+ms: List<&2, DC.Mem>, +r: DR.Node, +a: DR.Node, +r2: DR.Node, +w: DR.Lab, +d: DR.Der, em: {DC.mem_of(ms, r) == Some{DC.Mem{a, r2, w, d}} : Maybe<&2, DC.Mem>},
  hr: {DC.node_eq(r2, r) == True{} : Bool}, hrr: SH.AllRR(ms), hin: SH.Inm(DC.Mem{a, r2, w, d}, ms), hn: {DC.node_eq(a, r) == True{} : Bool})
  -> {DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}:
  (+n, +en) = hin
  rootrec.s(ms, r, a, r2, w, d, em, hr, hrr, n, en, hn)

def rootrec.mi(+ms: List<&2, DC.Mem>, +r: DR.Node, +a: DR.Node, +r2: DR.Node, +w: DR.Lab, +d: DR.Der, +em: {DC.mem_of(ms, r) == Some{DC.Mem{a, r2, w, d}} : Maybe<&2, DC.Mem>},
  hr: {DC.node_eq(r2, r) == True{} : Bool}, hrr: SH.AllRR(ms), mi: SH.MemIn(ms, r, DC.Mem{a, r2, w, d})) -> {DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}:
  (hin, hn) = mi
  rootrec.n(ms, r, a, r2, w, d, em, hr, hrr, hin, hn)

def rootrec.m(mm: Maybe<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +r: DR.Node, +em: {DC.mem_of(ms, r) == mm : Maybe<&2, DC.Mem>}, hr: {SH.isroot.m(mm, r) == True{} : Bool}, hrr: SH.AllRR(ms))
  -> {DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}:
  match mm:
    case None{}:
      absurd({DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}, LP.tf(Equal.sym(Bool, False{}, True{}, hr)))
    case Some{DC.Mem{+a, +r2, +w, +d}}:
      rootrec.mi(ms, r, a, r2, w, d, em, hr, hrr, SH.mem_of_in(ms, r, DC.Mem{a, r2, w, d}, em))

# a root's record is (r, r, 1, DSelf r)
def rootrec(+ms: List<&2, DC.Mem>, +r: DR.Node, hr: {SH.isroot(ms, r) == True{} : Bool}, hrr: SH.AllRR(ms))
  -> {DC.mem_of(ms, r) == Some{DC.Mem{r, r, DC.lone(), DR.DSelf{r}}} : Maybe<&2, DC.Mem>}:
  rootrec.m(DC.mem_of(ms, r), ms, r, {==}, hr, hrr)

# F's record
def frec(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> {DC.mem_of(DC.Sk.ms(s), DR.NFrame{}) == Some{DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}} : Maybe<&2, DC.Mem>}:
  rootrec(DC.Sk.ms(s), DR.NFrame{}, SH.sh.fr(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, h.sh(es, fs, ctx, t, s, H))), SH.sh.rr(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, h.sh(es, fs, ctx, t, s, H))))

def rp_eq(+m1: Maybe<&2, DC.Mem>, +m2: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +a: DR.Node, +x: SK.VE, e: {m1 == m2 : Maybe<&2, DC.Mem>},
  h: rp.m(m1, es, fs, t, s, a, x)) -> rp.m(m2, es, fs, t, s, a, x):
  %e : rp.m(_, es, fs, t, s, a, x)
  h

def svy(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameD(SK.VE.y(u), SK.VE.y(v)):
  (a, b) = h
  b

# par(F, x) is represented exactly when Im x is in K
def frame_in(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +x: SK.VE, h: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(x)) == True{} : Bool}) -> Repr(es, fs, t, s, DR.JP{DR.NFrame{}, x}):
  rp_eq(Some{DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}}, DC.mem_of(DC.Sk.ms(s), DR.NFrame{}), es, fs, t, s, DR.NFrame{}, x, Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), DR.NFrame{}), Some{DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}}, frec(es, fs, ctx, t, s, H)),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), SK.VE.y(x), SK.VE.y(DR.gmul(DC.lone(), x)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), h, svy(x, DR.gmul(DC.lone(), x), GN.one(x))))

def frame_out(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +x: SK.VE, h: Repr(es, fs, t, s, DR.JP{DR.NFrame{}, x})) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.y(x)) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), SK.VE.y(DR.gmul(DC.lone(), x)), SK.VE.y(x), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)),
    rp_eq(DC.mem_of(DC.Sk.ms(s), DR.NFrame{}), Some{DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}}, es, fs, t, s, DR.NFrame{}, x, frec(es, fs, ctx, t, s, H), h),
    svy(DR.gmul(DC.lone(), x), x, MG.samevd_sym(x, DR.gmul(DC.lone(), x), GN.one(x))))

# The rules without nodes to compare
# ----------------------------------

def rule_zero(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> Repr(es, fs, t, s, DR.JK{DR.zeroe()}):
  ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)))

def rule_prem(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +i: Nat, hf: DR.HasFact(DR.fact_at(fs, i))) -> Repr(es, fs, t, s, DR.JK{DR.fact.e(DR.fact_at(fs, i))}):
  SH.kf_at(fs, i, DC.Sk.k(s), SH.shi.k(es, fs, OP.cspan(ctx), DC.segids(es), s, h.sh(es, fs, ctx, t, s, H)), hf)

def ka.q(+l: S.Q, +A: S.Q, +B: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(l, A), S.Q.mul(DR.qo(), B)), S.Q.add(S.Q.mul(l, A), B)):
  LQ.q_add_cong_r(S.Q.mul(l, A), S.Q.mul(DR.qo(), B), B, QA.one_mul(B))

def ka.at(+p: List<&2, S.Q>, +l: S.Q, +e1: E.QExpr, +e2: E.QExpr) -> S.Q.eq(E.qeval(p, ST.lin2(l, e1, DR.qo(), e2)), E.qeval(p, E.QAdd{E.QMul{E.QCst{l}, e1}, e2})):
  ka.q(l, E.qeval(p, e1), E.qeval(p, e2))

def rule_kadd(j1: DR.Jd, j2: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +l: S.Q, h1: Repr(es, fs, t, s, j1), h2: Repr(es, fs, t, s, j2), k1: DR.IsK(j1), k2: DR.IsK(j2))
  -> Repr(es, fs, t, s, DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(j1)}, DR.Jd.e(j2)}}):
  match j1 j2:
    case DR.JK{+e1} DR.JK{+e2}:
      ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.lin2(l, e1, DR.qo(), e2), E.QAdd{E.QMul{E.QCst{l}, e1}, e2}, ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), l, e1, DR.qo(), e2, ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), h1, h2),
        ID.qzero_ident(ST.lin2(l, e1, DR.qo(), e2), E.QAdd{E.QMul{E.QCst{l}, e1}, e2}, p => ka.at(p, l, e1, e2)))
    case DR.JK{+e1} DR.JP{+a2, +x2}:
      absurd(Repr(es, fs, t, s, DR.JK{E.QAdd{E.QMul{E.QCst{l}, e1}, DR.zeroe()}}), k2)
    case DR.JP{+a1, +x1} j2:
      absurd(Repr(es, fs, t, s, DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.zeroe()}, DR.Jd.e(j2)}}), k1)

# a statement about node a, read at the same node b
def rp_node(+a: DR.Node, +b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +x: SK.VE, e: {a == b : DR.Node}, h: Repr(es, fs, t, s, DR.JP{a, x})) -> Repr(es, fs, t, s, DR.JP{b, x}):
  %e : Repr(es, fs, t, s, DR.JP{_, x})
  h

def rule_back(j: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), h: Repr(es, fs, t, s, j), hp: DR.IsP(j), ha: {DR.Jd.a(j) == DR.NFrame{} : DR.Node}) -> Repr(es, fs, t, s, DR.JK{SK.VE.y(DR.Jd.x(j))}):
  match j:
    case DR.JK{+e}:
      absurd(Repr(es, fs, t, s, DR.JK{SK.VE.y(DR.zerov())}), hp)
    case DR.JP{+a, +x}:
      frame_out(es, fs, ctx, t, s, H, x, rp_node(a, DR.NFrame{}, es, fs, t, s, x, ha, h))

def rule_frame(j: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +x: SK.VE, h: Repr(es, fs, t, s, j), hk: DR.IsK(j), hs: DR.Same(DR.Jd.e(j), SK.VE.y(x))) -> Repr(es, fs, t, s, DR.JP{DR.NFrame{}, x}):
  match j:
    case DR.JK{+e}:
      frame_in(es, fs, ctx, t, s, H, x, ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), e, SK.VE.y(x), ST.kri(es, fs, ctx, t, DC.Sk.k(s), h.k(es, fs, ctx, t, s, H)), h, VD.samed_of(e, SK.VE.y(x), hs)))
    case DR.JP{+a, +x0}:
      absurd(Repr(es, fs, t, s, DR.JP{DR.NFrame{}, x}), hk)

def rule_plin(j1: DR.Jd, j2: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +m1: S.Q, +m2: S.Q, h1: Repr(es, fs, t, s, j1), h2: Repr(es, fs, t, s, j2), p1: DR.IsP(j1), p2: DR.IsP(j2), ea: {DR.Jd.a(j1) == DR.Jd.a(j2) : DR.Node})
  -> Repr(es, fs, t, s, DR.JP{DR.Jd.a(j1), DR.vlin(m1, DR.Jd.x(j1), m2, DR.Jd.x(j2))}):
  match j1 j2:
    case DR.JP{+a1, +x1} DR.JP{+a2, +x2}:
      rp_lin(DC.mem_of(DC.Sk.ms(s), a1), es, fs, ctx, t, s, H, a1, m1, x1, m2, x2, h1, rp_node(a2, a1, es, fs, t, s, x2, Equal.sym(DR.Node, a1, a2, ea), h2))
    case DR.JP{+a1, +x1} DR.JK{+e2}:
      absurd(Repr(es, fs, t, s, DR.JP{a1, DR.vlin(m1, x1, m2, DR.zerov())}), p2)
    case DR.JK{+e1} j2:
      absurd(Repr(es, fs, t, s, DR.JP{DR.NFrame{}, DR.vlin(m1, DR.zerov(), m2, DR.Jd.x(j2))}), p1)

def kn.q(+X: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), X), S.Q.mul(DR.qo(), Y)), S.Q.add(X, Y)):
  QR.qring_eq([X, Y], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}}, E.QAdd{E.QVar{0n}, E.QVar{1n}}, {==})

def kn.ax(+p: List<&2, S.Q>, +x: SK.VE, +l: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(DR.qo(), x, DR.qo(), l))), E.qeval(p, SK.VE.x(SK.VE.add(x, l)))):
  kn.q(E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(l)))

def kn.ay(+p: List<&2, S.Q>, +x: SK.VE, +l: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(DR.qo(), x, DR.qo(), l))), E.qeval(p, SK.VE.y(SK.VE.add(x, l)))):
  kn.q(E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(l)))

def kn(+x: SK.VE, +l: SK.VE) -> VD.SameVD(DR.vlin(DR.qo(), x, DR.qo(), l), SK.VE.add(x, l)):
  (ID.qzero_ident(SK.VE.x(DR.vlin(DR.qo(), x, DR.qo(), l)), SK.VE.x(SK.VE.add(x, l)), p => kn.ax(p, x, l)),
   ID.qzero_ident(SK.VE.y(DR.vlin(DR.qo(), x, DR.qo(), l)), SK.VE.y(SK.VE.add(x, l)), p => kn.ay(p, x, l)))

def rule_known(j: DR.Jd, jr: DR.Jd, ji: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), h: Repr(es, fs, t, s, j), hr: Repr(es, fs, t, s, jr), hi: Repr(es, fs, t, s, ji), p: DR.IsP(j), kr: DR.IsK(jr), ki: DR.IsK(ji))
  -> Repr(es, fs, t, s, DR.JP{DR.Jd.a(j), SK.VE.add(DR.Jd.x(j), SK.VE{DR.Jd.e(jr), DR.Jd.e(ji)})}):
  match j jr ji:
    case DR.JP{+a, +x} DR.JK{+er} DR.JK{+ei}:
      rp_tr(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, DR.vlin(DR.qo(), x, DR.qo(), SK.VE{er, ei}), SK.VE.add(x, SK.VE{er, ei}),
        rp_lin(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, DR.qo(), x, DR.qo(), SK.VE{er, ei}, h, rp_k2(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, SK.VE{er, ei}, hr, hi)), kn(x, SK.VE{er, ei}))
    case DR.JP{+a, +x} DR.JK{+er} DR.JP{+ai, +xi}:
      absurd(Repr(es, fs, t, s, DR.JP{a, SK.VE.add(x, SK.VE{er, DR.zeroe()})}), ki)
    case DR.JP{+a, +x} DR.JP{+ar, +xr} ji:
      absurd(Repr(es, fs, t, s, DR.JP{a, SK.VE.add(x, SK.VE{DR.zeroe(), DR.Jd.e(ji)})}), kr)
    case DR.JK{+e} jr ji:
      absurd(Repr(es, fs, t, s, DR.JP{DR.NFrame{}, SK.VE.add(DR.zerov(), SK.VE{DR.Jd.e(jr), DR.Jd.e(ji)})}), p)

# Generators in the sets
# ----------------------

def fx.fb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, h: FX.Fx(es, fs, t, cs, ids, s))
  -> {DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>}:
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  c

def h.fb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> {DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>}:
  fx.fb(es, fs, t, OP.cspan(ctx), DC.segids(es), s, h.fx(es, fs, ctx, t, s, H))

def mok.sv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, h: GN.MOkD(es, fs, ctx, t, DC.Mem{a, r, w, d}))
  -> VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))):
  (h1, r1) = h
  (h2, r2) = r1
  (h3, r3) = r2
  (h4, r4) = r3
  h4

def rgi.tl(f: Bool, +g: DR.Der, +xs: List<&2, DR.Der>, +rest: List<&2, DR.Der>, h: ST.InD(g, rest)) -> ST.InD(g, DC.dcatif(f, xs, rest)):
  match f:
    case True{}:
      ST.ind_cat_r(g, xs, rest, h)
    case False{}:
      h

def rgi.hd(f: Bool, +g: DR.Der, +xs: List<&2, DR.Der>, +rest: List<&2, DR.Der>, ef: {f == True{} : Bool}, h: ST.InD(g, xs)) -> ST.InD(g, DC.dcatif(f, xs, rest)):
  match f:
    case True{}:
      ST.ind_cat_l(g, xs, rest, h)
    case False{}:
      absurd(ST.InD(g, rest), LP.tf(Equal.sym(Bool, False{}, True{}, ef)))

# a record's generators are among its root's
def mg_in(ms: List<&2, DC.Mem>, n: Nat, +fs: List<&2, DR.Fact>, +ls: List<&2, DC.Link>, +r: DR.Node, +m: DC.Mem, +g: DR.Der,
  en: {SH.mat(ms, n) == Some{m} : Maybe<&2, DC.Mem>}, er: {DC.node_eq(DC.Mem.r(m), r) == True{} : Bool}, h: ST.InD(g, DC.mgens(fs, ls, m))) -> ST.InD(g, DC.rgens(fs, r, ms, ls)):
  match ms n:
    case Nil{} n:
      absurd(ST.InD(g, Nil{}), SH.mnone_some(m, en))
    case Con{+m0, +tl} 0n:
      %Equal.sym(DC.Mem, m0, m, SH.msome_inj(m0, m, en)) : ST.InD(g, DC.dcatif(DC.node_eq(DC.Mem.r(_), r), DC.mgens(fs, ls, _), DC.rgens(fs, r, tl, ls)))
      rgi.hd(DC.node_eq(DC.Mem.r(m), r), g, DC.mgens(fs, ls, m), DC.rgens(fs, r, tl, ls), er, h)
    case Con{+m0, +tl} 1n+j:
      rgi.tl(DC.node_eq(DC.Mem.r(m0), r), g, DC.mgens(fs, ls, m0), DC.rgens(fs, r, tl, ls), mg_in(tl, j, fs, ls, r, m, g, en, er, h))

# a root's generators are in its set
def gen_rset(r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +g: DR.Der, hg: ST.InD(g, DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s))))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.Jd.x(DR.concl(es, fs, g))):
  match r:
    case DR.NFrame{}:
      (+n, +en) = hg
      RF.fback_none(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s), h.fb(es, fs, ctx, t, s, H), g, n, en)
    case DR.NSeg{+c}:
      ND.gen_root(es, fs, ctx, t, s, DR.NSeg{c}, g, hg, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))

# a record's set is a root set; it holds K squared
def rok(+r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s)) -> ST.StOk(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r)):
  ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), ND.sok_root(es, fs, ctx, t, s, r, h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H)))

# Self
# ----

def self.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +n: Nat, +en: {SH.mat(DC.Sk.ms(s), n) == Some{DC.Mem{a2, r, w, d}} : Maybe<&2, DC.Mem>}, ea: {a2 == a : DR.Node})
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.zdir(es, a))):
  %ea : ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.zdir(es, _)))
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a2)), rok(r, es, fs, ctx, t, s, H),
    gen_rset(r, es, fs, ctx, t, s, H, d, mg_in(DC.Sk.ms(s), n, fs, DC.Sk.ls(s), r, DC.Mem{a2, r, w, d}, d, en, SH.node_refl(r), ST.ind_hd(d, DC.dcat(DC.lstats(DC.pprems(DC.nstats(fs, a2)), a2, w, d), DC.llinks(DC.Sk.ls(s), a2, w, d))))),
    mok.sv(es, fs, ctx, t, a2, r, w, d, mok_at(DC.Sk.ms(s), n, es, fs, ctx, t, DC.Mem{a2, r, w, d}, en, h.ms(es, fs, ctx, t, s, H))))

def self.n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, hin: SH.Inm(DC.Mem{a2, r, w, d}, DC.Sk.ms(s)), hn: {DC.node_eq(a2, a) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.zdir(es, a))):
  (+n, +en) = hin
  self.go(es, fs, ctx, t, s, H, a, a2, r, w, d, n, en, GN.node_eq_ok(a2, a, hn))

def self.mi(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, +a2: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, mi: SH.MemIn(DC.Sk.ms(s), a, DC.Mem{a2, r, w, d}))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), DR.gmul(w, DR.zdir(es, a))):
  (hin, hn) = mi
  self.n(es, fs, ctx, t, s, H, a, a2, r, w, d, hin, hn)

def fnone(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), em: {DC.mem_of(DC.Sk.ms(s), DR.NFrame{}) == None{} : Maybe<&2, DC.Mem>}) -> Empty:
  SH.mnone_some(DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}, Equal.trans(Maybe<&2, DC.Mem>, None{}, DC.mem_of(DC.Sk.ms(s), DR.NFrame{}), Some{DC.Mem{DR.NFrame{}, DR.NFrame{}, DC.lone(), DR.DSelf{DR.NFrame{}}}},
    Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), DR.NFrame{}), None{}, em), frec(es, fs, ctx, t, s, H)))

def self.none(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), em: {DC.mem_of(DC.Sk.ms(s), a) == None{} : Maybe<&2, DC.Mem>}) -> rp.m(None{}, es, fs, t, s, a, DR.zdir(es, a)):
  match a:
    case DR.NFrame{}:
      absurd(rp.m(None{}, es, fs, t, s, DR.NFrame{}, DR.zdir(es, DR.NFrame{})), fnone(es, fs, ctx, t, s, H, em))
    case DR.NSeg{+c}:
      ND.gen_coll(es, fs, ctx, t, s, c, DR.DSelf{DR.NSeg{c}}, ST.ind_hd(DR.DSelf{DR.NSeg{c}}, DC.dcat(DC.pprems(DC.stats(fs, c, 0n)), DC.dcat(DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c)))), h.k(es, fs, ctx, t, s, H), h.ms(es, fs, ctx, t, s, H), h.ls(es, fs, ctx, t, s, H), h.msn(es, fs, ctx, t, s, H), h.lsn(es, fs, ctx, t, s, H), h.z(es, fs, ctx, t, s, H), h.b(es, fs, ctx, t, s, H))

def self.m(mm: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node, em: {DC.mem_of(DC.Sk.ms(s), a) == mm : Maybe<&2, DC.Mem>}) -> rp.m(mm, es, fs, t, s, a, DR.zdir(es, a)):
  match mm:
    case Some{DC.Mem{+a2, +r, +w, +d}}:
      self.mi(es, fs, ctx, t, s, H, a, a2, r, w, d, SH.mem_of_in(DC.Sk.ms(s), a, DC.Mem{a2, r, w, d}, em))
    case None{}:
      self.none(a, es, fs, ctx, t, s, H, em)

# par(a, z_a) is represented
def rule_self(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: Hyp(es, fs, ctx, t, s), +a: DR.Node) -> Repr(es, fs, t, s, DR.JP{a, DR.zdir(es, a)}):
  self.m(DC.mem_of(DC.Sk.ms(s), a), es, fs, ctx, t, s, H, a, {==})
