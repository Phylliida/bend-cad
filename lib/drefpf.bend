# bend-cad: the refutation decision is exact (PLAN-sk13b B3, "The
# refutation decision"). LRefOk is the spec's RefOk (spec/solve.bend)
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
import ./qnorm.bend as QN
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
import ./dcgenpf.bend as GN
import ./dcsetpf.bend as ST
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX
import ./dcreprpf.bend as RR
import ./dcclosepf.bend as CCF
import ./dcbasepf.bend as BS
import ./dckslpf.bend as KL
import ./dcclprogpf.bend as CP

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

# Complete
# --------

def hyp_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +fuel: Nat, +s: DC.Sk, +eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> RR.Hyp(es, fs, ctx, t, s):
  (FX.fix_at(es, fs, ctx, t, fuel, s, eo, hz, hb), (hz, hb))

def repr_k(j: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, hk: DR.IsK(j), hr: RR.Repr(es, fs, t, s, j)) -> {KS.ks.inb(DC.Sk.k(s), DR.Jd.e(j)) == True{} : Bool}:
  match j:
    case DR.JK{+e}:
      hr
    case DR.JP{+a, +x}:
      absurd({KS.ks.inb(DC.Sk.k(s), DR.zeroe()) == True{} : Bool}, hk)

def flip.at(+p: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: DR.Same(e1, e2)) -> S.Q.eq(E.qeval(p, e2), E.qeval(p, e1)):
  LQ.q_sym(E.qeval(p, e1), E.qeval(p, e2), h(p))

# K membership follows the polynomial
def inb_tr(+k: KS.KS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +e1: E.QExpr, +e2: E.QExpr, +hri: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  h1: {KS.ks.inb(k, e1) == True{} : Bool}, hs: DR.Same(e1, e2)) -> {KS.ks.inb(k, e2) == True{} : Bool}:
  (hr, hl) = hri
  SN.zero_of_in(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), e2, hr, hl,
    BS.in_tr(e1, e2, KS.kexprs(es, fs, KS.ks.ds(k)), SN.in_of_zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), e1, hr, h1), ID.qzero_ident(e2, e1, p => flip.at(p, e1, e2, hs))))

def kri_s(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s)) -> ST.RI(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s))):
  ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))

# a valid K derivation of something the same as x puts x in K, at a fixpoint
def der_k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +d: DR.Der, hv: DR.Valid(es, fs, ctx, d), hk: DR.IsK(DR.concl(es, fs, d)), +x: E.QExpr,
  hs: DR.Same(DR.Jd.e(DR.concl(es, fs, d)), x)) -> {KS.ks.inb(DC.Sk.k(s), x) == True{} : Bool}:
  inb_tr(DC.Sk.k(s), es, fs, DR.Jd.e(DR.concl(es, fs, d)), x, kri_s(es, fs, ctx, t, s, H),
    repr_k(DR.concl(es, fs, d), es, fs, t, s, hk, CCF.closed(d, es, fs, ctx, t, s, H, hv)), hs)

def iso_of.go(b: Bool, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +sg: Nat, eb: {b == DC.coll(es, OP.cspan(ctx), sg) : Bool}, ho: DR.Open(es, ctx, DR.NSeg{sg}))
  -> {SV.bnot(b) == True{} : Bool}:
  match b:
    case True{}:
      absurd({False{} == True{} : Bool}, ho(OP.coll_sound(es, ctx, sg, Equal.sym(Bool, True{}, DC.coll(es, OP.cspan(ctx), sg), eb))))
    case False{}:
      {==}

def iso_of(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +sg: Nat, ho: DR.Open(es, ctx, DR.NSeg{sg})) -> {DC.isopen(es, OP.cspan(ctx), DR.NSeg{sg}) == True{} : Bool}:
  iso_of.go(DC.coll(es, OP.cspan(ctx), sg), es, ctx, sg, {==}, ho)

def isnone(m: Maybe<&2, DR.DRef>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def dis_some(+x: DR.DRef, h: {Some{x} == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  KA.ft(Equal.cong(Maybe<&2, DR.DRef>, Bool, m => isnone(m), Some{x}, None{}, h))

# A derived collapse at a fixpoint
# --------------------------------

def nm_of.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +sg: Nat, +m: DC.Mem, mi: SH.MemIn(DC.Sk.ms(s), DR.NSeg{sg}, m))
  -> {SH.nmem(DR.NSeg{sg}, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}) == True{} : Bool}:
  (hi, hn) = mi
  (n, en) = hi
  (%GN.node_eq_ok(DC.Mem.a(m), DR.NSeg{sg}, hn) : {SH.nmem(_, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}) == True{} : Bool}
    RR.recn_at(DC.Sk.ms(s), n, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, m, en,
      SH.sh.rn(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H)))))

def nm_of.m(mm: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +sg: Nat,
  em: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{sg}) == mm : Maybe<&2, DC.Mem>}, +hop: {DC.isopen(es, OP.cspan(ctx), DR.NSeg{sg}) == True{} : Bool})
  -> {SH.nmem(DR.NSeg{sg}, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}) == True{} : Bool}:
  match mm:
    case None{}:
      absurd({SH.nmem(DR.NSeg{sg}, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}) == True{} : Bool}, RR.open_rec(DR.NSeg{sg}, es, fs, ctx, t, s, H, OP.open_of(es, ctx, DR.NSeg{sg}, hop), em))
    case Some{+m}:
      nm_of.go(es, fs, ctx, t, s, H, sg, m, SH.mem_of_in(DC.Sk.ms(s), DR.NSeg{sg}, m, em))

def rcoll_c.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +dr: DR.Der, +di: DR.Der, +sg: Nat,
  vr: DR.Valid(es, fs, ctx, dr), vi: DR.Valid(es, fs, ctx, di), kr: DR.IsK(DR.concl(es, fs, dr)), ki: DR.IsK(DR.concl(es, fs, di)),
  sr: DR.Same(DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zseg(es, sg))), si: DR.Same(DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zseg(es, sg))),
  +hop: {DC.isopen(es, OP.cspan(ctx), DR.NSeg{sg}) == True{} : Bool}) -> Empty:
  RR.void.node(DR.NSeg{sg}, es, fs, ctx, t, s, H, der_k(es, fs, ctx, t, s, H, dr, vr, kr, SK.VE.x(DR.zseg(es, sg)), sr),
    der_k(es, fs, ctx, t, s, H, di, vi, ki, SK.VE.y(DR.zseg(es, sg)), si), hop, nm_of.m(DC.mem_of(DC.Sk.ms(s), DR.NSeg{sg}), es, fs, ctx, t, s, H, sg, {==}, hop))

# no open segment has its direction in K at a fixpoint
def rcoll_c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +dr: DR.Der, +di: DR.Der, +sg: Nat, h: DR.RefColl(es, fs, ctx, dr, di, sg)) -> Empty:
  (vr, r1) = h
  (vi, r2) = r1
  (kr, r3) = r2
  (ki, r4) = r3
  (sr, r5) = r4
  (si, ho) = r5
  rcoll_c.go(es, fs, ctx, t, s, H, dr, di, sg, vr, vi, kr, ki, sr, si, iso_of(es, ctx, sg, ho))

# An Angle on a segment collapsed in K
# ------------------------------------

def segp_none(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +s: Nat, +p: Nat, +fst: Bool, +rest: Maybe<&2, DR.DRef>,
  h: {DF.ang.pick(b, es, fs, k, s, p, fst, rest) == None{} : Maybe<&2, DR.DRef>}) -> {rest == None{} : Maybe<&2, DR.DRef>}:
  match b:
    case True{}:
      absurd({rest == None{} : Maybe<&2, DR.DRef>}, dis_some(DR.RAngle{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))), p, fst}, h))
    case False{}:
      h

def seg_none(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +p: Nat, +fst: Bool, +rest: Maybe<&2, DR.DRef>,
  h: {DF.ang.seg(m, es, fs, k, p, fst, rest) == None{} : Maybe<&2, DR.DRef>}) -> {rest == None{} : Maybe<&2, DR.DRef>}:
  match m:
    case None{}:
      h
    case Some{+s}:
      segp_none(DC.fullc(es, k, s), es, fs, k, s, p, fst, rest, h)

def seg_some(+s: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +p: Nat, +fst: Bool, +rest: Maybe<&2, DR.DRef>, hf: {DC.fullc(es, k, s) == True{} : Bool},
  h: {DF.ang.seg(Some{s}, es, fs, k, p, fst, rest) == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  dis_some(DR.RAngle{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))), p, fst},
    (%hf : {DF.ang.pick(_, es, fs, k, s, p, fst, rest) == None{} : Maybe<&2, DR.DRef>} h))

def angs_tl(+p0: Nat, +k0: SK.Constraint, +t: List<&2, DF.Ang>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, h: {DF.angs(Con{DF.Ang{p0, k0}, t}, es, fs, k) == None{} : Maybe<&2, DR.DRef>})
  -> {DF.angs(t, es, fs, k) == None{} : Maybe<&2, DR.DRef>}:
  seg_none(DR.angle_seg(k0, False{}), es, fs, k, p0, False{}, DF.angs(t, es, fs, k),
    seg_none(DR.angle_seg(k0, True{}), es, fs, k, p0, True{}, DF.ang.seg(DR.angle_seg(k0, False{}), es, fs, k, p0, False{}, DF.angs(t, es, fs, k)), h))

def angs_hd(fst: Bool, +p: Nat, +kc: SK.Constraint, +t: List<&2, DF.Ang>, +s: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, es0: {DR.angle_seg(kc, fst) == Some{s} : Maybe<&2, Nat>},
  +hf: {DC.fullc(es, k, s) == True{} : Bool}, h: {DF.angs(Con{DF.Ang{p, kc}, t}, es, fs, k) == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  match fst:
    case True{}:
      seg_some(s, es, fs, k, p, True{}, DF.ang.seg(DR.angle_seg(kc, False{}), es, fs, k, p, False{}, DF.angs(t, es, fs, k)), hf,
        (%es0 : {DF.ang.seg(_, es, fs, k, p, True{}, DF.ang.seg(DR.angle_seg(kc, False{}), es, fs, k, p, False{}, DF.angs(t, es, fs, k))) == None{} : Maybe<&2, DR.DRef>} h))
    case False{}:
      seg_some(s, es, fs, k, p, False{}, DF.angs(t, es, fs, k), hf,
        (%es0 : {DF.ang.seg(_, es, fs, k, p, False{}, DF.angs(t, es, fs, k)) == None{} : Maybe<&2, DR.DRef>}
          seg_none(DR.angle_seg(kc, True{}), es, fs, k, p, True{}, DF.ang.seg(DR.angle_seg(kc, False{}), es, fs, k, p, False{}, DF.angs(t, es, fs, k)), h)))

def ag.p(m: Maybe<&2, DF.Ang>) -> Nat:
  match m:
    case Some{DF.Ang{p, k}}:
      p
    case None{}:
      0n

def ag.k(m: Maybe<&2, DF.Ang>) -> SK.Constraint:
  match m:
    case Some{DF.Ang{p, k}}:
      k
    case None{}:
      SK.Parallel{0n, 0n}

def ag.some(m: Maybe<&2, DF.Ang>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

# the check finds an Angle when one has its segment collapsed in K
def angs_found(as: List<&2, DF.Ang>, n: Nat, +p: Nat, +kc: SK.Constraint, fst: Bool, +s: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS,
  en: {aat(as, n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>}, es0: {DR.angle_seg(kc, fst) == Some{s} : Maybe<&2, Nat>}, +hf: {DC.fullc(es, k, s) == True{} : Bool},
  h: {DF.angs(as, es, fs, k) == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  match as n:
    case Nil{} n:
      KA.ft(Equal.cong(Maybe<&2, DF.Ang>, Bool, m => ag.some(m), None{}, Some{DF.Ang{p, kc}}, en))
    case Con{DF.Ang{+p0, +k0}, +t} 0n:
      +en2 = en
      angs_hd(fst, p, kc, t, s, es, fs, k, es0, hf,
        (%Equal.cong(Maybe<&2, DF.Ang>, SK.Constraint, m => ag.k(m), Some{DF.Ang{p0, k0}}, Some{DF.Ang{p, kc}}, en2) : {DF.angs(Con{DF.Ang{p, _}, t}, es, fs, k) == None{} : Maybe<&2, DR.DRef>}
          (%Equal.cong(Maybe<&2, DF.Ang>, Nat, m => ag.p(m), Some{DF.Ang{p0, k0}}, Some{DF.Ang{p, kc}}, en2) : {DF.angs(Con{DF.Ang{_, k0}, t}, es, fs, k) == None{} : Maybe<&2, DR.DRef>}
            h)))
    case Con{DF.Ang{+p0, +k0}, +t} 1n+m:
      angs_found(t, m, p, kc, fst, s, es, fs, k, en, es0, hf, angs_tl(p0, k0, t, es, fs, k, h))

def rangle.m(mm: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +as: List<&2, DF.Ang>, +n: Nat, +p: Nat, +kc: SK.Constraint, +fst: Bool, +dr: DR.Der, +di: DR.Der,
  en: {aat(as, n) == Some{DF.Ang{p, kc}} : Maybe<&2, DF.Ang>}, em: {DR.angle_seg(kc, fst) == mm : Maybe<&2, Nat>},
  vr: DR.Valid(es, fs, ctx, dr), vi: DR.Valid(es, fs, ctx, di), kr: DR.IsK(DR.concl(es, fs, dr)), ki: DR.IsK(DR.concl(es, fs, di)), hc: DR.AngleColl(es, fs, dr, di, mm),
  hna: {DF.angs(as, es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  match mm:
    case None{}:
      hc
    case Some{+sg}:
      (sr, si) = hc
      angs_found(as, n, p, kc, fst, sg, es, fs, DC.Sk.k(s), en, em,
        LP2.band_i(KS.ks.inb(DC.Sk.k(s), SK.VE.x(DR.zseg(es, sg))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.zseg(es, sg))),
          der_k(es, fs, ctx, t, s, H, dr, vr, kr, SK.VE.x(DR.zseg(es, sg)), sr), der_k(es, fs, ctx, t, s, H, di, vi, ki, SK.VE.y(DR.zseg(es, sg)), si)),
        hna)

def rangle_c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +as: List<&2, DF.Ang>, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool, h: AngOk(es, fs, ctx, as, dr, di, p, fst),
  hna: {DF.angs(as, es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.DRef>}) -> Empty:
  (+kc, r1) = h
  (hin, hra) = r1
  (n, en) = hin
  (vr, r2) = hra
  (vi, r3) = r2
  (kr, r4) = r3
  (ki, hc) = r4
  rangle.m(DR.angle_seg(kc, fst), es, fs, ctx, t, s, H, as, n, p, kc, fst, dr, di, en, {==}, vr, vi, kr, ki, hc, hna)

# A Motzkin refutation over derivable K facts
# -------------------------------------------

def qpad(B: List<&2, E.QExpr>, +ls: List<&2, S.Q>) -> List<&2, S.Q>:
  match B:
    case Nil{}:
      Nil{}
    case Con{b, bt}:
      Con{SN.qhd(ls), qpad(bt, SN.qtl(ls))}

def qpad_len(B: List<&2, E.QExpr>, +ls: List<&2, S.Q>) -> {SV.eq(SV.qlen(qpad(B, ls)), SV.neqs(B)) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      qpad_len(bt, SN.qtl(ls))

def lin_qpad.nil(+p: List<&2, S.Q>, B: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, SV.lin(qpad(B, Nil{}), B)), SV.qzero()):
  match B:
    case Nil{}:
      LQ.q_refl(SV.qzero())
    case Con{+b, +bt}:
      LQ.q_trans(E.qeval(p, SV.lin(qpad(Con{b, bt}, Nil{}), Con{b, bt})), S.Q.add(S.Q.mul(SV.qzero(), E.qeval(p, b)), SV.qzero()), SV.qzero(),
        LQ.q_add_cong_r(S.Q.mul(SV.qzero(), E.qeval(p, b)), E.qeval(p, SV.lin(qpad(bt, Nil{}), bt)), SV.qzero(), lin_qpad.nil(p, bt)),
        QR.qring_eq([E.qeval(p, b)], E.QAdd{E.QMul{E.QCst{SV.qzero()}, E.QVar{0n}}, E.QCst{SV.qzero()}}, E.QCst{SV.qzero()}, {==}))

# padding the coefficients to one per generator keeps the combination
def lin_qpad(+p: List<&2, S.Q>, ls: List<&2, S.Q>, B: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, SV.lin(qpad(B, ls), B)), E.qeval(p, SV.lin(ls, B))):
  match ls B:
    case Con{+l, +lt} Con{+b, +bt}:
      LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, b)), E.qeval(p, SV.lin(qpad(bt, lt), bt)), E.qeval(p, SV.lin(lt, bt)), lin_qpad(p, lt, bt))
    case Nil{} B:
      lin_qpad.nil(p, B)
    case Con{l, lt} Nil{}:
      LQ.q_refl(SV.qzero())

def ri_rv(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, h: ST.RI(B, rows)) -> {EP.rinv(B, rows, 0n) == True{} : Bool}:
  (a, b) = h
  a

def motz_in(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +hri: ST.RI(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s))), hv: DR.AllValidK(es, fs, ctx, ds))
  -> KL.AllIn(DR.dconcls(es, fs, ds), KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s)))):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (vd, r1) = hv
      (kd, rt) = r1
      (SN.in_of_zero(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.Jd.e(DR.concl(es, fs, d)), ri_rv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), hri),
         repr_k(DR.concl(es, fs, d), es, fs, t, s, kd, CCF.closed(d, es, fs, ctx, t, s, H, vd))),
       motz_in(tl, es, fs, ctx, t, s, H, hri, rt))

def refok_tr(+ls: List<&2, S.Q>, +ls2: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +ss: List<&2, SK.Side>,
  h: {SV.refok(ls, ms, k, D, ss) == True{} : Bool}, hl: {SV.eq(SV.qlen(ls2), SV.neqs(B)) == True{} : Bool}) -> {SV.refok(ls2, ms, k, B, ss) == True{} : Bool}:
  %Equal.sym(Bool, SV.eq(SV.qlen(ls2), SV.neqs(B)), True{}, hl)
    : {SV.band(_, SV.band(SV.eq(SV.qlen(ms), SV.slen(ss)), SV.band(SV.nonneg(ms), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss)))))) == True{} : Bool}
  LP2.band_r(SV.eq(SV.qlen(ls), SV.neqs(D)), SV.band(SV.eq(SV.qlen(ms), SV.slen(ss)), SV.band(SV.nonneg(ms), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(ms, ss))))), h)

def motz_id.at(+p: List<&2, S.Q>, +ls: List<&2, S.Q>, +ls2: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +ss: List<&2, SK.Side>,
  +q: {QN.qzero(E.QSub{SV.lin(ls, D), SV.lin(ls2, B)}) == True{} : Bool}, hi: SV.Ident(E.QAdd{SV.lin(ls, D), SV.slin(ms, ss)}, E.QCst{k}))
  -> S.Q.eq(E.qeval(p, E.QAdd{SV.lin(qpad(B, ls2), B), SV.slin(ms, ss)}), E.qeval(p, E.QCst{k})):
  LQ.q_trans(E.qeval(p, E.QAdd{SV.lin(qpad(B, ls2), B), SV.slin(ms, ss)}), E.qeval(p, E.QAdd{SV.lin(ls, D), SV.slin(ms, ss)}), k,
    LQ.q_add_cong_l(E.qeval(p, SV.lin(qpad(B, ls2), B)), E.qeval(p, SV.lin(ls, D)), E.qeval(p, SV.slin(ms, ss)),
      LQ.q_trans(E.qeval(p, SV.lin(qpad(B, ls2), B)), E.qeval(p, SV.lin(ls2, B)), E.qeval(p, SV.lin(ls, D)), lin_qpad(p, ls2, B),
        LQ.q_sym(E.qeval(p, SV.lin(ls, D)), E.qeval(p, SV.lin(ls2, B)), ID.ident_ok(SV.lin(ls, D), SV.lin(ls2, B), q)(p)))),
    hi(p))

def motz_c.go(+ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +D: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls2: List<&2, S.Q>,
  +q: {QN.qzero(E.QSub{SV.lin(ls, D), SV.lin(ls2, B)}) == True{} : Bool}, hok: {SV.refok(ls, ms, k, D, ss) == True{} : Bool}, hi: SV.Ident(E.QAdd{SV.lin(ls, D), SV.slin(ms, ss)}, E.QCst{k}),
  hnr: SAT.NoRef(B, ss)) -> Empty:
  hnr(qpad(B, ls2), ms, k, (refok_tr(ls, qpad(B, ls2), ms, k, D, B, ss, hok, qpad_len(B, ls2)), p => motz_id.at(p, ls, ls2, ms, k, D, B, ss, q, hi)))

# a Motzkin refutation over derivable K facts is one over K's generators
def motz_c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +ss: List<&2, SK.Side>, +ds: List<&2, DR.Der>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q,
  hv: DR.AllValidK(es, fs, ctx, ds), hr: SV.Refutes0(DR.dconcls(es, fs, ds), ss, ls, ms, k), hnr: SAT.NoRef(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss)) -> Empty:
  (hok, hi) = hr
  +hin = CP.in_lin_sub(ls, DR.dconcls(es, fs, ds), KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))),
    motz_in(ds, es, fs, ctx, t, s, H, kri_s(es, fs, ctx, t, s, H), hv))
  motz_c.go(ls, ms, k, DR.dconcls(es, fs, ds), KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss,
    SN.in_ls(SV.lin(ls, DR.dconcls(es, fs, ds)), KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), hin), SN.in_qz(SV.lin(ls, DR.dconcls(es, fs, ds)), KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), hin), hok, hi, hnr)

# The theorem
# -----------

def NoLRef(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>) -> Type:
  @r: DR.DRef -> LRefOk(es, fs, ctx, ss, as, r) -> Empty

def dcomp.r(r: DR.DRef, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>,
  +H: RR.Hyp(es, fs, ctx, t, s),
  hnr: SAT.NoRef(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss), hna: {DF.angs(as, es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.DRef>}, hr: LRefOk(es, fs, ctx, ss, as, r)) -> Empty:
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      (hv, hm) = hr
      motz_c(es, fs, ctx, t, s, H, ss, ds, ls, ms, k, hv, hm, hnr)
    case DR.RColl{+dr, +di, +sg}:
      rcoll_c(es, fs, ctx, t, s, H, dr, di, sg, hr)
    case DR.RAngle{+dr, +di, +p, +fst}:
      rangle_c(es, fs, ctx, t, s, H, as, dr, di, p, fst, hr, hna)

def dcomp.m(m: Maybe<&2, RF.Cert>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>,
  +H: RR.Hyp(es, fs, ctx, t, s),
  em: {RF.refute(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss) == m : Maybe<&2, RF.Cert>}, hn: {DF.dref.fix(m, es, fs, DC.Sk.k(s), as) == None{} : Maybe<&2, DR.DRef>},
  r: DR.DRef, hr: LRefOk(es, fs, ctx, ss, as, r)) -> Empty:
  match m:
    case Some{RF.Cert{+ls, +ms, +kk}}:
      dis_some(DR.RMotz{KS.ks.ds(DC.Sk.k(s)), ls, ms, kk}, hn)
    case None{}:
      dcomp.r(r, es, fs, ctx, t, s, ss, as, H,
        (%em : SAT.RefOk(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss, _)
          SAT.refute_ok(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss)), hn, hr)

# at a fixpoint with the closure's hypotheses (RR.Hyp), when the decision
# finds no refutation there is none
def dref_complete(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +ss: List<&2, SK.Side>, +as: List<&2, DF.Ang>,
  +H: RR.Hyp(es, fs, ctx, t, s),
  hn: {DF.dref(DC.OFix{s}, es, fs, ss, as) == None{} : Maybe<&2, DR.DRef>}) -> NoLRef(es, fs, ctx, ss, as):
  r => hr => dcomp.m(RF.refute(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss), es, fs, ctx, t, s, ss, as, H, {==}, hn, r, hr)
