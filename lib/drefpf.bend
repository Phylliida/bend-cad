# bend-cad: the refutation decision is exact (PLAN-sk13b B3, "The
# refutation decision"). LRefOk is the spec's RefOk (spec/_draft13b.bend)
# over explicit side conditions and Angles. Whatever lib/dref.bend's dref
# returns is a refutation (dref_sound). At a fixpoint, when it returns
# none there is none (dref_complete): a Motzkin refutation over derivable
# K facts is one over K's generators (each fact is in their span, by the
# closure theorem), against sk-13a's refute; a derived collapse contradicts
# the fixpoint's void check; an Angle whose segment collapsed in K is one
# the decision's check finds. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./karith.bend as KA
import ./listpf.bend as LP2
import ./identpf.bend as ID
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./refute.bend as RF
import ./satpf.bend as SAT
import ./spanpf.bend as SN
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcopenpf.bend as OP
import ./dcinvpf.bend as IV
import ./dcroundpf.bend as RD
import ./dref.bend as DF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Refutations, with the sides and Angles given
# --------------------------------------------

def aat(as: List<&2, DF.Ang>, n: Nat) -> Maybe<&2, DF.Ang>:
  match as n:
    case Nil{} n:
      None{}
    case Con{x, tl} 0n:
      Some{x}
    case Con{x, tl} 1n+k:
      aat(tl, k)

# the Angle at position p has kind kc, among as
def AngIn(+p: Nat, +kc: SK.Constraint, +as: List<&2, DF.Ang>) -> Data:
  Sigma<&2, &2, Nat, n => {aat(as, n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>}>

def AngOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +as: List<&2, DF.Ang>, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool) -> Type:
  &kc: SK.Constraint -> (AngIn(p, kc, as) & DR.RefAngle(es, fs, ctx, dr, di, kc, fst))

# r refutes the facts fs with the sides ss, the Angles as, in the context ctx
def LRefOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, r: DR.DRef) -> Type:
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      DR.AllValidK(es, fs, ctx, ds) & SV.Refutes0(DR.dconcls(es, fs, ds), ss, ls, ms, k)
    case DR.RColl{+dr, +di, +s}:
      DR.RefColl(es, fs, ctx, dr, di, s)
    case DR.RAngle{+dr, +di, +p, +fst}:
      AngOk(es, fs, ctx, as, dr, di, p, fst)

def OptR(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, m: Maybe<&2, DR.DRef>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+r}:
      LRefOk(es, fs, ctx, ss, as, r)

# Sound
# -----

def zq_len(ss: List<&2, SK.Side>) -> {SV.eq(SV.qlen(DF.zq(ss)), SV.slen(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      zq_len(t)

def zq_nn(ss: List<&2, SK.Side>) -> {SV.nonneg(DF.zq(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      zq_nn(t)

def zq_slin(+p: List<&2, S.Q>, ss: List<&2, SK.Side>) -> S.Q.eq(E.qeval(p, SV.slin(DF.zq(ss), ss)), SV.qzero()):
  match ss:
    case Nil{}:
      LQ.q_refl(SV.qzero())
    case Con{+h, +t}:
      LQ.q_trans(E.qeval(p, SV.slin(DF.zq(Con{h, t}), Con{h, t})), S.Q.add(S.Q.mul(DR.qz(), E.qeval(p, SV.sexpr(h))), SV.qzero()), SV.qzero(),
        LQ.q_add_cong_r(S.Q.mul(DR.qz(), E.qeval(p, SV.sexpr(h))), E.qeval(p, SV.slin(DF.zq(t), t)), SV.qzero(), zq_slin(p, t)),
        QR.qring_eq([E.qeval(p, SV.sexpr(h))], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QCst{SV.qzero()}}, E.QCst{SV.qzero()}, {==}))

def one.at(+p: List<&2, S.Q>, +e: E.QExpr, +ss: List<&2, SK.Side>, +sd: VD.SameD(e, DR.cst(DR.qo())))
  -> S.Q.eq(E.qeval(p, E.QAdd{SV.lin(Con{DF.qm1(), Nil{}}, Con{e, Nil{}}), SV.slin(DF.zq(ss), ss)}), E.qeval(p, E.QCst{DF.qm1()})):
  LQ.q_trans(E.qeval(p, E.QAdd{SV.lin(Con{DF.qm1(), Nil{}}, Con{e, Nil{}}), SV.slin(DF.zq(ss), ss)}), S.Q.add(S.Q.add(S.Q.mul(DF.qm1(), DR.qo()), SV.qzero()), SV.qzero()), DF.qm1(),
    QA.add_cong(S.Q.add(S.Q.mul(DF.qm1(), E.qeval(p, e)), SV.qzero()), S.Q.add(S.Q.mul(DF.qm1(), DR.qo()), SV.qzero()), E.qeval(p, SV.slin(DF.zq(ss), ss)), SV.qzero(),
      LQ.q_add_cong_l(S.Q.mul(DF.qm1(), E.qeval(p, e)), S.Q.mul(DF.qm1(), DR.qo()), SV.qzero(), LQ.q_mul_cong_r(DF.qm1(), E.qeval(p, e), DR.qo(), ID.ident_ok(e, DR.cst(DR.qo()), sd)(p))),
      zq_slin(p, ss)),
    QR.qring_eq([], E.QAdd{E.QAdd{E.QMul{E.QCst{DF.qm1()}, E.QCst{DR.qo()}}, E.QCst{SV.qzero()}}, E.QCst{SV.qzero()}}, E.QCst{DF.qm1()}, {==}))

def refok_one(+e: E.QExpr, +ss: List<&2, SK.Side>) -> {SV.refok(Con{DF.qm1(), Nil{}}, DF.zq(ss), DF.qm1(), Con{e, Nil{}}, ss) == True{} : Bool}:
  %Equal.sym(Bool, SV.eq(SV.qlen(DF.zq(ss)), SV.slen(ss)), True{}, zq_len(ss))
    : {SV.band(SV.eq(SV.qlen(Con{DF.qm1(), Nil{}}), SV.neqs(Con{e, Nil{}})), SV.band(_, SV.band(SV.nonneg(DF.zq(ss)), SV.bor(SV.islt(S.Q.cmp(DF.qm1(), SV.qzero())), SV.band(SV.iszz(S.Q.num(DF.qm1())), SV.strict_pos(DF.zq(ss), ss)))))) == True{} : Bool}
  %Equal.sym(Bool, SV.nonneg(DF.zq(ss)), True{}, zq_nn(ss))
    : {SV.band(SV.eq(SV.qlen(Con{DF.qm1(), Nil{}}), SV.neqs(Con{e, Nil{}})), SV.band(True{}, SV.band(_, SV.bor(SV.islt(S.Q.cmp(DF.qm1(), SV.qzero())), SV.band(SV.iszz(S.Q.num(DF.qm1())), SV.strict_pos(DF.zq(ss), ss)))))) == True{} : Bool}
  {==}

def dref_one.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +d: DR.Der, vd: VD.VD(es, fs, ctx, d), ik: VD.Isk(DR.concl(es, fs, d)),
  +sd: VD.SameD(DR.Jd.e(DR.concl(es, fs, d)), DR.cst(DR.qo())))
  -> DR.AllValidK(es, fs, ctx, Con{d, Nil{}}) & SV.Refutes0(DR.dconcls(es, fs, Con{d, Nil{}}), ss, Con{DF.qm1(), Nil{}}, DF.zq(ss), DF.qm1()):
  ((VD.valid_of(es, fs, ctx, d, vd), (VD.isk_of(DR.concl(es, fs, d), ik), Unit{})),
   (refok_one(DR.Jd.e(DR.concl(es, fs, d)), ss), p => one.at(p, DR.Jd.e(DR.concl(es, fs, d)), ss, sd)))

# 1 in K: -1 times that fact is -1
def dref_one(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, +d: DR.Der, h: RD.KD(es, fs, ctx, d, DR.cst(DR.qo())))
  -> LRefOk(es, fs, ctx, ss, as, DR.RMotz{Con{d, Nil{}}, Con{DF.qm1(), Nil{}}, DF.zq(ss), DF.qm1()}):
  (vd, r1) = h
  (ik, sd) = r1
  dref_one.go(es, fs, ctx, ss, d, vd, ik, sd)

# an open segment with its direction in K squared: a derived collapse
def dref_void(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, +g: Nat, +dr: DR.Der, +di: DR.Der,
  h: RD.OutInv(es, fs, ctx, t, DC.OVoid{g, dr, di})) -> LRefOk(es, fs, ctx, ss, as, DR.RColl{dr, di, g}):
  (ho, r1) = h
  (kr, ki) = r1
  (vr, r2) = kr
  (ir, sr) = r2
  (vi, r3) = ki
  (ii, si) = r3
  (VD.valid_of(es, fs, ctx, dr, vr), (VD.valid_of(es, fs, ctx, di, vi), (VD.isk_of(DR.concl(es, fs, dr), ir), (VD.isk_of(DR.concl(es, fs, di), ii),
    (VD.same_of(DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zseg(es, g)), sr), (VD.same_of(DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zseg(es, g)), si), OP.open_of(es, ctx, DR.NSeg{g}, ho)))))))

def dconcls_k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, ds: List<&2, DR.Der>) -> {DR.dconcls(es, fs, ds) == KS.kexprs(es, fs, ds) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %Equal.sym(List<&2, E.QExpr>, DR.dconcls(es, fs, t), KS.kexprs(es, fs, t), dconcls_k(es, fs, t)) : {Con{DR.Jd.e(DR.concl(es, fs, d)), _} == Con{DR.Jd.e(DR.concl(es, fs, d)), KS.kexprs(es, fs, t)} : List<&2, E.QExpr>}
      {==}

def allk_valid(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, ds: List<&2, DR.Der>, h: KP.AllK(es, fs, ctx, ds)) -> DR.AllValidK(es, fs, ctx, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +t}:
      (v, r1) = h
      (k, rt) = r1
      (v, (k, allk_valid(es, fs, ctx, t, rt)))

def kinv_all(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, h: KP.KInv(es, fs, ctx, k)) -> DR.AllValidK(es, fs, ctx, KS.ks.ds(k)):
  match k:
    case KS.KS{+rows, +ds}:
      (a, r1) = h
      (b, c) = r1
      allk_valid(es, fs, ctx, ds, c)

def ain_tl(+p: Nat, +kc: SK.Constraint, +h0: DF.Ang, +t: List<&2, DF.Ang>, h: AngIn(p, kc, t)) -> AngIn(p, kc, Con{h0, t}):
  (n, e) = h
  (1n+n, e)

def optr_tl(m: Maybe<&2, DR.DRef>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +h0: DF.Ang, +t: List<&2, DF.Ang>, h: OptR(es, fs, ctx, ss, t, m))
  -> OptR(es, fs, ctx, ss, Con{h0, t}, m):
  match m:
    case None{}:
      Unit{}
    case Some{DR.RMotz{+ds, +ls, +ms, +k}}:
      h
    case Some{DR.RColl{+dr, +di, +s}}:
      h
    case Some{DR.RAngle{+dr, +di, +p, +fst}}:
      (+kc, r1) = h
      (hin, hra) = r1
      (kc, (ain_tl(p, kc, h0, t, hin), hra))

def angp_t(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: KS.KS, +s: Nat, +p: Nat, +kc: SK.Constraint, +fst: Bool,
  +t: List<&2, DF.Ang>, es0: {DR.angle_seg(kc, fst) == Some{s} : Maybe<&2, Nat>},
  hx: (DR.Valid(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s)))) & DR.IsK(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s)))))) & DR.Same(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))))), SK.VE.x(DR.zseg(es, s))),
  hy: (DR.Valid(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s)))) & DR.IsK(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s)))))) & DR.Same(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))))), SK.VE.y(DR.zseg(es, s))))
  -> OptR(es, fs, ctx, ss, Con{DF.Ang{p, kc}, t}, Some{DR.RAngle{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))), p, fst}}):
  (ax, sx) = hx
  (vx, kx) = ax
  (ay, sy) = hy
  (vy, ky) = ay
  (kc, ((0n, {==}), (vx, (vy, (kx, (ky, (%Equal.sym(Maybe<&2, Nat>, DR.angle_seg(kc, fst), Some{s}, es0) : DR.AngleColl(es, fs, KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))), _)
    (sx, sy))))))))

def angp_s(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: KS.KS, +s: Nat, +p: Nat, +kc: SK.Constraint, +fst: Bool,
  +t: List<&2, DF.Ang>, eb: {b == DC.fullc(es, k, s) : Bool}, +tt: Nat, +hkd: IV.KInvD(es, fs, ctx, tt, k), es0: {DR.angle_seg(kc, fst) == Some{s} : Maybe<&2, Nat>},
  +rest: Maybe<&2, DR.DRef>, hr: OptR(es, fs, ctx, ss, Con{DF.Ang{p, kc}, t}, rest)) -> OptR(es, fs, ctx, ss, Con{DF.Ang{p, kc}, t}, DF.ang.pick(b, es, fs, k, s, p, fst, rest)):
  match b:
    case True{}:
      +ef = Equal.sym(Bool, True{}, DC.fullc(es, k, s), eb)
      angp_t(es, fs, ctx, ss, k, s, p, kc, fst, t, es0,
        KP.ks_der_ok(es, fs, ctx, k, SK.VE.x(DR.zseg(es, s)), IV.kinv_of(es, fs, ctx, tt, k, hkd), LP2.band_l(KS.ks.inb(k, SK.VE.x(DR.zseg(es, s))), KS.ks.inb(k, SK.VE.y(DR.zseg(es, s))), ef)),
        KP.ks_der_ok(es, fs, ctx, k, SK.VE.y(DR.zseg(es, s)), IV.kinv_of(es, fs, ctx, tt, k, hkd), LP2.band_r(KS.ks.inb(k, SK.VE.x(DR.zseg(es, s))), KS.ks.inb(k, SK.VE.y(DR.zseg(es, s))), ef)))
    case False{}:
      hr

def angs_s.seg(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: KS.KS, +p: Nat, +kc: SK.Constraint, +fst: Bool,
  +tl: List<&2, DF.Ang>, em: {DR.angle_seg(kc, fst) == m : Maybe<&2, Nat>}, +tt: Nat, +hkd: IV.KInvD(es, fs, ctx, tt, k), +rest: Maybe<&2, DR.DRef>, hr: OptR(es, fs, ctx, ss, Con{DF.Ang{p, kc}, tl}, rest))
  -> OptR(es, fs, ctx, ss, Con{DF.Ang{p, kc}, tl}, DF.ang.seg(m, es, fs, k, p, fst, rest)):
  match m:
    case None{}:
      hr
    case Some{+s}:
      angp_s(DC.fullc(es, k, s), es, fs, ctx, ss, k, s, p, kc, fst, tl, {==}, tt, hkd, em, rest, hr)

def angs_s(as: List<&2, DF.Ang>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: KS.KS, +tt: Nat, +hkd: IV.KInvD(es, fs, ctx, tt, k))
  -> OptR(es, fs, ctx, ss, as, DF.angs(as, es, fs, k)):
  match as:
    case Nil{}:
      Unit{}
    case Con{DF.Ang{+p, +kc}, +tl}:
      angs_s.seg(DR.angle_seg(kc, True{}), es, fs, ctx, ss, k, p, kc, True{}, tl, {==}, tt, hkd, DF.ang.seg(DR.angle_seg(kc, False{}), es, fs, k, p, False{}, DF.angs(tl, es, fs, k)),
        angs_s.seg(DR.angle_seg(kc, False{}), es, fs, ctx, ss, k, p, kc, False{}, tl, {==}, tt, hkd, DF.angs(tl, es, fs, k),
          optr_tl(DF.angs(tl, es, fs, k), es, fs, ctx, ss, DF.Ang{p, kc}, tl, angs_s(tl, es, fs, ctx, ss, k, tt, hkd))))

def dfix_s(m: Maybe<&2, RF.Cert>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, +k: KS.KS, +tt: Nat, +hkd: IV.KInvD(es, fs, ctx, tt, k),
  hm: SAT.RefOk(KS.kexprs(es, fs, KS.ks.ds(k)), ss, m)) -> OptR(es, fs, ctx, ss, as, DF.dref.fix(m, es, fs, k, as)):
  match m:
    case Some{RF.Cert{+ls, +ms, +kk}}:
      (kinv_all(es, fs, ctx, k, IV.kinv_of(es, fs, ctx, tt, k, hkd)),
       (%Equal.sym(List<&2, E.QExpr>, DR.dconcls(es, fs, KS.ks.ds(k)), KS.kexprs(es, fs, KS.ks.ds(k)), dconcls_k(es, fs, KS.ks.ds(k))) : SV.Refutes0(_, ss, ls, ms, kk)
         hm))
    case None{}:
      angs_s(as, es, fs, ctx, ss, k, tt, hkd)

# whatever the decision returns is a refutation
def dref_sound(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>, h: RD.OutInv(es, fs, ctx, t, o))
  -> OptR(es, fs, ctx, ss, as, DF.dref(o, es, fs, ss, as)):
  match o:
    case DC.OStep{s}:
      Unit{}
    case DC.OFix{+s}:
      (hk, r1) = h
      dfix_s(RF.refute(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss), es, fs, ctx, ss, as, DC.Sk.k(s), t, hk, SAT.refute_ok(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss))
    case DC.OOne{+d}:
      dref_one(es, fs, ctx, ss, as, d, h)
    case DC.OVoid{+g, +dr, +di}:
      dref_void(es, fs, ctx, t, ss, as, g, dr, di, h)
