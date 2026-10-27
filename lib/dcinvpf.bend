# bend-cad: the closure's span invariants in reusable form (PLAN-sk13b B3).
# K's and a hull's invariants (lib/kspacepf.bend's KInv, lib/hspacepf.bend's
# HInv) hold Valid, which Bend uses once; the closure reads one K into
# every hull, so it keeps KInvD and HInvD, the same with VD
# (lib/dcvd.bend) and each generator's form below t. They give KInv and
# HInv (kinv_of, hinv_of) for the membership lemmas, and are kept by
# adding and by folding (ks_add_invd, hs_add_invd, hfold_inv). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./seppf.bend as SP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dclose.bend as DC
import ./dcvd.bend as VD

# K
# -

# a K generator: valid, a K judgment, below t
def KGen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +d: DR.Der) -> Data:
  SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isk(DR.concl(es, fs, d)), {SP.vbelow(DR.Jd.e(DR.concl(es, fs, d)), t) == True{} : Bool}))

def AllKD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, ds: List<&2, DR.Der>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, tl}:
      SK.Both(KGen(es, fs, ctx, t, d), AllKD(es, fs, ctx, t, tl))

def KInvD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS) -> Data:
  match k:
    case KS.KS{+rows, +ds}:
      SK.Both({EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool}, SK.Both({EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat}, AllKD(es, fs, ctx, t, ds)))

def allk_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, ds: List<&2, DR.Der>, h: AllKD(es, fs, ctx, t, ds)) -> KP.AllK(es, fs, ctx, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, tl}:
      (g, rt) = h
      (v, r1) = g
      (k, b) = r1
      (VD.valid_of(es, fs, ctx, d, v), (VD.isk_of(DR.concl(es, fs, d), k), allk_of(es, fs, ctx, t, tl, rt)))

def kinv_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, h: KInvD(es, fs, ctx, t, k)) -> KP.KInv(es, fs, ctx, k):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = h
      (hl, ha) = r1
      (hr, (hl, allk_of(es, fs, ctx, t, ds, ha)))

def allkd_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, ds: List<&2, DR.Der>, +d: DR.Der, h: AllKD(es, fs, ctx, t, ds), +hd: KGen(es, fs, ctx, t, d))
  -> AllKD(es, fs, ctx, t, KS.dsnoc(ds, d)):
  match ds:
    case Nil{}:
      (hd, Unit{})
    case Con{+h0, +tl}:
      (g0, rt) = h
      (g0, allkd_snoc(es, fs, ctx, t, tl, d, rt, hd))

def ks_add.pickd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, b: Bool,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))) : Bool},
  +hr: {EP.rinv(KS.kexprs(es, fs, ds), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(KS.kexprs(es, fs, ds)) : Nat}, ha: AllKD(es, fs, ctx, t, ds), +hd: KGen(es, fs, ctx, t, d))
  -> KInvD(es, fs, ctx, t, KS.ks.pick(b, rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d)):
  match b:
    case True{}:
      (hr, (hl, ha))
    case False{}:
      (KP.ks_add.rinv(es, fs, rows, ds, d, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), eb)),
       (KP.ks_add.len(es, fs, rows, ds, d, EL.row_of(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d)))), hl), allkd_snoc(es, fs, ctx, t, ds, d, ha, hd)))

# adding a K generator keeps the invariant
def ks_add_invd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, +d: DR.Der, h: KInvD(es, fs, ctx, t, k), +hd: KGen(es, fs, ctx, t, d))
  -> KInvD(es, fs, ctx, t, KS.ks.add(es, fs, k, d)):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = h
      (hl, ha) = r1
      ks_add.pickd(es, fs, ctx, t, rows, ds, d, EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), {==}, hr, hl, ha, hd)

# Hulls
# -----

# a hull generator at r: valid, a parallel judgment at r, below t
def PGenD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der) -> Data:
  SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isp(DR.concl(es, fs, d)), SK.Both({DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t))))

def AllPD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, tl}:
      SK.Both(PGenD(es, fs, ctx, r, t, d), AllPD(es, fs, ctx, r, t, tl))

def HInvD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS) -> Data:
  match h:
    case HS.HS{+rows, +ds}:
      SK.Both({EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, SK.Both({EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, AllPD(es, fs, ctx, r, t, ds)))

def pgen_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der, h: PGenD(es, fs, ctx, r, t, d)) -> HP.PGen(es, fs, ctx, r, t, d):
  (v, r1) = h
  (p, r2) = r1
  (ea, b) = r2
  (VD.valid_of(es, fs, ctx, d, v), (VD.isp_of(DR.concl(es, fs, d), p), (ea, b)))

def allp_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>, h: AllPD(es, fs, ctx, r, t, ds)) -> HP.AllP(es, fs, ctx, r, t, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, tl}:
      (g, rt) = h
      (v, r1) = g
      (p, r2) = r1
      (ea, b) = r2
      (VD.valid_of(es, fs, ctx, d, v), (VD.isp_of(DR.concl(es, fs, d), p), (ea, (b, allp_of(es, fs, ctx, r, t, tl, rt)))))

def hinv_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, hi: HInvD(es, fs, ctx, r, t, h)) -> HP.HInv(es, fs, ctx, r, t, h):
  match h:
    case HS.HS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      (hr, (hl, allp_of(es, fs, ctx, r, t, ds, ha)))

def allpd_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, ds: List<&2, DR.Der>, +d: DR.Der, h: AllPD(es, fs, ctx, r, t, ds), +hd: PGenD(es, fs, ctx, r, t, d))
  -> AllPD(es, fs, ctx, r, t, KS.dsnoc(ds, d)):
  match ds:
    case Nil{}:
      (hd, Unit{})
    case Con{+h0, +tl}:
      (g0, rt) = h
      (g0, allpd_snoc(es, fs, ctx, r, t, tl, d, rt, hd))

def hs_add.pickd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, b: Bool,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) : Bool},
  +hr: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, ha: AllPD(es, fs, ctx, r, t, ds), +hd: PGenD(es, fs, ctx, r, t, d))
  -> HInvD(es, fs, ctx, r, t, HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d)):
  match b:
    case True{}:
      (hr, (hl, ha))
    case False{}:
      (HP.hs_add.rinv(es, fs, t, rows, ds, d, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), eb)),
       (HP.hs_add.len(es, fs, t, rows, ds, d, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))), hl), allpd_snoc(es, fs, ctx, r, t, ds, d, ha, hd)))

# adding a hull generator keeps the invariant
def hs_add_invd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +d: DR.Der, hi: HInvD(es, fs, ctx, r, t, h), +hd: PGenD(es, fs, ctx, r, t, d))
  -> HInvD(es, fs, ctx, r, t, HS.hs.add(es, fs, t, h, d)):
  match h:
    case HS.HS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      hs_add.pickd(es, fs, ctx, r, t, rows, ds, d, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), {==}, hr, hl, ha, hd)

def hs0_invd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat) -> HInvD(es, fs, ctx, r, t, HS.hs0()):
  ({==}, ({==}, Unit{}))

# folding generators in keeps the invariant
def hfold_inv(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +h: HS.HS,
  hi: HInvD(es, fs, ctx, r, t, h), hd: AllPD(es, fs, ctx, r, t, ds)) -> HInvD(es, fs, ctx, r, t, DC.hfold(ds, es, fs, t, h)):
  match ds:
    case Nil{}:
      hi
    case Con{+d, tl}:
      (g, rt) = hd
      hfold_inv(tl, es, fs, ctx, r, t, HS.hs.add(es, fs, t, h, d), hs_add_invd(es, fs, ctx, r, t, h, d, hi, g), rt)

def allpd_cat(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, hx: AllPD(es, fs, ctx, r, t, xs), hy: AllPD(es, fs, ctx, r, t, ys))
  -> AllPD(es, fs, ctx, r, t, DC.dcat(xs, ys)):
  match xs:
    case Nil{}:
      hy
    case Con{+d, tl}:
      (g, rt) = hx
      (g, allpd_cat(es, fs, ctx, r, t, tl, ys, rt, hy))
