# bend-cad: K's and a hull's derivations in reusable form (PLAN-sk13b B3).
# From KInvD and HInvD (lib/dcinvpf.bend), the K-add and par-lin chains
# are VD, and a member's derivation (ks.der, hs.der) is VD with its
# conclusion the same as what was asked (ks_der_okd, hs_der_okd), the
# hull's form also below t. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./identpf.bend as ID
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV

# K
# -

def kchain_okd.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +l: S.Q, +d: DR.Der, +rest: DR.Der,
  +v: VD.VD(es, fs, ctx, d), +k: VD.Isk(DR.concl(es, fs, d)), ih: SK.Both(VD.VD(es, fs, ctx, rest), VD.Isk(DR.concl(es, fs, rest))))
  -> SK.Both(VD.VD(es, fs, ctx, DR.DKAdd{l, d, rest}), VD.Isk(DR.concl(es, fs, DR.DKAdd{l, d, rest}))):
  (vr, kr) = ih
  ((v, (vr, (k, kr))), {==})

def kchain_okd(ls: List<&2, S.Q>, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, h: IV.AllKD(es, fs, ctx, t, ds))
  -> SK.Both(VD.VD(es, fs, ctx, KS.kchain(ls, ds)), VD.Isk(DR.concl(es, fs, KS.kchain(ls, ds)))):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (g, rt) = h
      (v, r1) = g
      (k, b) = r1
      kchain_okd.go(es, fs, ctx, l, d, KS.kchain(lt, dt), v, k, kchain_okd(lt, dt, es, fs, ctx, t, rt))
    case Nil{} ds:
      (Unit{}, {==})
    case Con{+l, +lt} Nil{}:
      (Unit{}, {==})

def samed_flip.at(+p: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: SV.Ident(e2, e1)) -> S.Q.eq(E.qeval(p, e1), E.qeval(p, e2)):
  LQ.q_sym(E.qeval(p, e2), E.qeval(p, e1), h(p))

def samed_flip(+e1: E.QExpr, +e2: E.QExpr, h: SV.Ident(e2, e1)) -> VD.SameD(e1, e2):
  ID.qzero_ident(e1, e2, p => samed_flip.at(p, e1, e2, h))

def ks_der.same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ls: List<&2, S.Q>, +ds: List<&2, DR.Der>, +e: E.QExpr, h: SV.Ident(e, SV.lin(ls, KS.kexprs(es, fs, ds))))
  -> VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.kchain(ls, ds))), e):
  %Equal.sym(E.QExpr, DR.Jd.e(DR.concl(es, fs, KS.kchain(ls, ds))), SV.lin(ls, KS.kexprs(es, fs, ds)), KP.kchain_e(es, fs, ls, ds)) : VD.SameD(_, e)
  samed_flip(SV.lin(ls, KS.kexprs(es, fs, ds)), e, h)

def ks_der.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +ls: List<&2, S.Q>, +ds: List<&2, DR.Der>, +e: E.QExpr,
  hc: SK.Both(VD.VD(es, fs, ctx, KS.kchain(ls, ds)), VD.Isk(DR.concl(es, fs, KS.kchain(ls, ds)))), h: SV.Ident(e, SV.lin(ls, KS.kexprs(es, fs, ds))))
  -> SK.Both(VD.VD(es, fs, ctx, KS.kchain(ls, ds)), SK.Both(VD.Isk(DR.concl(es, fs, KS.kchain(ls, ds))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.kchain(ls, ds))), e))):
  (v, k) = hc
  (v, (k, ks_der.same(es, fs, ls, ds, e, h)))

# e in K: its derivation is VD, a K judgment, the same as e
def ks_der_okd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, +e: E.QExpr, hk: IV.KInvD(es, fs, ctx, t, k), hz: {KS.ks.inb(k, e) == True{} : Bool})
  -> SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, k, e)), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, k, e))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, e))), e))):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = hk
      (hl, ha) = r1
      ks_der.go(es, fs, ctx, DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), ds, e,
        kchain_okd(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, KS.kexprs(es, fs, ds)), ds, es, fs, ctx, t, ha),
        DV.derivable(KS.kexprs(es, fs, ds), rows, e, hr, hz))

# Hulls
# -----

def pchain_okd.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +l: S.Q, +d: DR.Der, +rest: DR.Der,
  +v: VD.VD(es, fs, ctx, d), +p: VD.Isp(DR.concl(es, fs, d)), +n: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node},
  ih: SK.Both(VD.VD(es, fs, ctx, rest), SK.Both(VD.Isp(DR.concl(es, fs, rest)), {DR.Jd.a(DR.concl(es, fs, rest)) == r : DR.Node})))
  -> SK.Both(VD.VD(es, fs, ctx, DR.DPLin{l, d, DR.qo(), rest}), SK.Both(VD.Isp(DR.concl(es, fs, DR.DPLin{l, d, DR.qo(), rest})), {DR.Jd.a(DR.concl(es, fs, DR.DPLin{l, d, DR.qo(), rest})) == r : DR.Node})):
  (vr, r1) = ih
  (pr, nr) = r1
  ((v, (vr, (p, (pr, Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, d)), r, DR.Jd.a(DR.concl(es, fs, rest)), n, Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, rest)), r, nr)))))), ({==}, n))

# the chain over the generators is VD and parallel at r
def pchain_okd(ls: List<&2, S.Q>, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: IV.AllPD(es, fs, ctx, r, t, ds))
  -> SK.Both(VD.VD(es, fs, ctx, HS.pchain(r, ls, ds)), SK.Both(VD.Isp(DR.concl(es, fs, HS.pchain(r, ls, ds))), {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, ls, ds))) == r : DR.Node})):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (g, rt) = h
      (v, r1) = g
      (p, r2) = r1
      (n, b) = r2
      pchain_okd.go(es, fs, ctx, r, l, d, HS.pchain(r, lt, dt), v, p, n, pchain_okd(lt, dt, es, fs, ctx, r, t, rt))
    case Nil{} ds:
      ((Unit{}, (Unit{}, ({==}, ({==}, {==})))), ({==}, {==}))
    case Con{+l, +lt} Nil{}:
      ((Unit{}, (Unit{}, ({==}, ({==}, {==})))), ({==}, {==}))

def allpd_below(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: IV.AllPD(es, fs, ctx, r, t, ds)) -> HP.AllBelow(HS.hxs(es, fs, ds), t):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, tl}:
      (g, rt) = h
      (v, r1) = g
      (p, r2) = r1
      (n, b) = r2
      (b, allpd_below(tl, es, fs, ctx, r, t, rt))

def hs_der.sv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE,
  x: ((DR.Valid(es, fs, ctx, HS.hs.der(es, fs, t, r, h, y)) & DR.IsP(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y)))) & {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))) == r : DR.Node}) & DR.SameV(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y))
  -> VD.SameVD(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y):
  (a, sv) = x
  VD.samevd_of(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y, sv)

def hs_der.below(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +ls: List<&2, S.Q>, +ds: List<&2, DR.Der>, h: HP.VBelow(HS.clin(es, r, ls, HS.hxs(es, fs, ds)), t))
  -> HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), t):
  %Equal.sym(SK.VE, DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), HS.clin(es, r, ls, HS.hxs(es, fs, ds)), HP.pchain_x(es, fs, r, ls, ds)) : HP.VBelow(_, t)
  h

def hs_der.vd2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +ds: List<&2, DR.Der>, +ls: List<&2, S.Q>, +ha: IV.AllPD(es, fs, ctx, r, t, ds), +hr: HP.VBelow(DR.zdir(es, r), t))
  -> SK.Both(SK.Both(VD.VD(es, fs, ctx, HS.pchain(r, ls, ds)), SK.Both(VD.Isp(DR.concl(es, fs, HS.pchain(r, ls, ds))), {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, ls, ds))) == r : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, ds))), t)):
  (pchain_okd(ls, ds, es, fs, ctx, r, t, ha), hs_der.below(es, fs, r, t, ls, ds, HP.clin_below(es, r, t, ls, HS.hxs(es, fs, ds), allpd_below(ds, es, fs, ctx, r, t, ha), hr)))

def hs_der.vd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +y: SK.VE, hi: IV.HInvD(es, fs, ctx, r, t, h), +hr: HP.VBelow(DR.zdir(es, r), t))
  -> SK.Both(SK.Both(VD.VD(es, fs, ctx, HS.hs.der(es, fs, t, r, h, y)), SK.Both(VD.Isp(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))) == r : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), t)):
  match h:
    case HS.HS{+rows, +ds}:
      (hrv, r1) = hi
      (hl, ha) = r1
      hs_der.vd2(es, fs, ctx, r, t, ds, DV.dropls(DV.rescb(EL.resid(rows, HS.enc(y, t))), DV.resbt(EL.resid(rows, HS.enc(y, t))), HS.enc(y, t), HS.encs(HS.hxs(es, fs, ds), t)), ha, hr)

# y in the hull: its derivation is VD, parallel at r, below t, the same as y
def hs_der_okd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +h: HS.HS, +y: SK.VE, +hi: IV.HInvD(es, fs, ctx, r, t, h),
  hz: {HS.hs.inb(h, y, t) == True{} : Bool}, +hy: HP.VBelow(y, t), +hr: HP.VBelow(DR.zdir(es, r), t))
  -> SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, HS.hs.der(es, fs, t, r, h, y)), SK.Both(VD.Isp(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))) == r : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y)):
  (hs_der.vd(es, fs, ctx, r, t, h, y, hi, hr), hs_der.sv(es, fs, ctx, r, t, h, y, HP.hs_der_ok(es, fs, ctx, r, t, h, y, IV.hinv_of(es, fs, ctx, r, t, h, hi), hz, hy, hr)))
