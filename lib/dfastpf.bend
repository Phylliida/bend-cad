# bend-cad: the fast run is the run (PLAN-sk13b B4.8 B.4). lib/dclose.bend's
# dclose returns exactly what dclose_ref returns (dclose_eq), so every
# proof about the closure stands: the three that unfold dclose
# (lib/dcroundpf.bend's dclose_ok, lib/dctermpf.bend's dclose_term,
# lib/dcfixpf.bend's dclose_fix) rewrite by it first.
# - Each lean check decides as the full one (lib/lrespf.bend), and stops at
#   the first item, which it builds by the same function: so each check
#   returns what the full check returns (fvoid_eq, ffback_eq, fclxs_eq,
#   fmgs_eq).
# - The cache holds, for each node it lists, the lean rows of K squared's
#   part of that node's hull for the current K (CInv), so a lookup is that
#   (kc_get_eq); adding to K keeps it (kc_add_inv).
# - So a fast round's Out is the round's, with the cache right for it
#   (fround_ok), and the fast run's is the run's (frun_eq).
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./zring.bend as R
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./lab.bend as LB
import ./dclose.bend as DC
import ./lres.bend as LR
import ./lrespf.bend as LP
import ./listpf.bend as LS

# Void
# ----

def fvoid_g(t: List<&2, Nat>, b: Bool, +i: Nat, +es: List<&2, SK.Ent>, +k: KS.KS) -> {DC.fvoid.g(t, b, i, es, k) == DC.vpick(b, i, DC.fvoid(t, es, k)) : Maybe<&2, Nat>}:
  match t b:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{j, t2} True{}:
      {==}
    case Con{+j, +t2} False{}:
      {==}

def fullc_eq(+es: List<&2, SK.Ent>, +k: KS.KS, +c: Nat) -> {DC.fullc.l(es, k, c) == DC.fullc(es, k, c) : Bool}:
  %LP.ks_inb_eq(k, SK.VE.x(DR.zseg(es, c))) : {SV.band(_, LR.ks.linb(k, SK.VE.y(DR.zseg(es, c)))) == DC.fullc(es, k, c) : Bool}
  %LP.ks_inb_eq(k, SK.VE.y(DR.zseg(es, c))) : {SV.band(KS.ks.inb(k, SK.VE.x(DR.zseg(es, c))), _) == DC.fullc(es, k, c) : Bool}
  {==}

def fv.h(b: Bool, +i: Nat, +t: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS, ih: {DC.fvoid(DC.oids(t, es, cs), es, k) == DC.voidseg(t, es, cs, k) : Maybe<&2, Nat>})
  -> {DC.fvoid(DC.oids.p(b, i, DC.oids(t, es, cs)), es, k) == DC.vpick(SV.band(SV.bnot(b), DC.fullc(es, k, i)), i, DC.voidseg(t, es, cs, k)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      ih
    case False{}:
      %fullc_eq(es, k, i) : {DC.fvoid.g(DC.oids(t, es, cs), DC.fullc.l(es, k, i), i, es, k) == DC.vpick(_, i, DC.voidseg(t, es, cs, k)) : Maybe<&2, Nat>}
      %ih : {DC.fvoid.g(DC.oids(t, es, cs), DC.fullc.l(es, k, i), i, es, k) == DC.vpick(DC.fullc.l(es, k, i), i, _) : Maybe<&2, Nat>}
      fvoid_g(DC.oids(t, es, cs), DC.fullc.l(es, k, i), i, es, k)

# the void check over the open segments is voidseg
def fvoid_eq(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS) -> {DC.fvoid(DC.oids(ids, es, cs), es, k) == DC.voidseg(ids, es, cs, k) : Maybe<&2, Nat>}:
  match ids:
    case Nil{}:
      {==}
    case Con{+i, +t}:
      fv.h(DC.coll(es, cs, i), i, t, es, cs, k, fvoid_eq(t, es, cs, k))

# Frame-back
# ----------

def ffback_g(t: List<&2, DR.Der>, b: Bool, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> {DC.ffback.g(t, b, g, es, fs, k) == DC.mpick2(SV.bnot(b), DR.DBack{g}, DC.ffback(t, es, fs, k)) : Maybe<&2, DR.Der>}:
  match t b:
    case Nil{} False{}:
      {==}
    case Nil{} True{}:
      {==}
    case Con{g2, t2} False{}:
      {==}
    case Con{+g2, +t2} True{}:
      {==}

def ffback_eq(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> {DC.ffback(gs, es, fs, k) == DC.fback(gs, es, fs, k) : Maybe<&2, DR.Der>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      %LP.ks_inb_eq(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))) : {DC.ffback.g(t, _, g, es, fs, k) == DC.mpick2(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), DR.DBack{g}, DC.fback(t, es, fs, k)) : Maybe<&2, DR.Der>}
      %ffback_eq(t, es, fs, k) : {DC.ffback.g(t, KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))), g, es, fs, k) == DC.mpick2(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), DR.DBack{g}, _) : Maybe<&2, DR.Der>}
      ffback_g(t, KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))), g, es, fs, k)

# Complex lines
# -------------

def osome(m: Maybe<&2, DR.Der>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

# lcl.g by its residual: found when 0, else on with it as a row
def lcl.c(rp: List<&2, R.ZTerm>, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows2: List<&2, LR.LRow>) -> Bool:
  match rp:
    case Nil{}:
      True{}
    case Con{x, xt}:
      DC.lcl.go(ds, es, fs, t, LR.lsnoc(rows2, LR.lrow_of(Con{x, xt})))

def lcl_g(ds: List<&2, DR.Der>, rp: List<&2, R.ZTerm>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rows2: List<&2, LR.LRow>) -> {DC.lcl.g(ds, rp, es, fs, t, rows2) == lcl.c(rp, ds, es, fs, t, rows2) : Bool}:
  match ds rp:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{x, xt}:
      {==}
    case Con{d, tl} Nil{}:
      {==}
    case Con{+d, +tl} Con{+x, +xt}:
      {==}

def lcl.h(res: EL.Res, +tl: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>, +d: DR.Der, +e: E.QExpr,
  ih: {DC.lcl.go(tl, es, fs, t, LR.lproj(EL.rsnoc(rows2, EL.row_of(res)))) == osome(DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d))) : Bool})
  -> {lcl.c(EP.resp(res), tl, es, fs, t, LR.lproj(rows2)) == osome(DC.cl.pick(EP.isnil(EP.resp(res)), DC.cl.found(es, fs, t, r, h, k, d, res, e, bb, prev), DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d)))) : Bool}:
  match res:
    case EL.Res{+p, +cb, +bt}:
      match p:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          %LP.snoc_eq(rows2, EL.Res{Con{x, xt}, cb, bt}) : {DC.lcl.go(tl, es, fs, t, _) == osome(DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.Res{Con{x, xt}, cb, bt})), EP.qsnoc(bb, e), KS.dsnoc(prev, d))) : Bool}
          ih

# cl.go finds a line exactly when the lean walk does
def lcl_eq(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>)
  -> {DC.lcl.go(ds, es, fs, t, LR.lproj(rows2)) == osome(DC.cl.go(ds, es, fs, t, r, h, k, rows2, bb, prev)) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      Equal.trans(Bool, DC.lcl.g(tl, LR.lresid(LR.lproj(rows2), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), es, fs, t, LR.lproj(rows2)), lcl.c(LR.lresid(LR.lproj(rows2), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), tl, es, fs, t, LR.lproj(rows2)), osome(DC.cl.pick(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), DC.cl.found(es, fs, t, r, h, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev), DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)))),
        lcl_g(tl, LR.lresid(LR.lproj(rows2), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), es, fs, t, LR.lproj(rows2)),
        (%LP.resid_eq(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)) : {lcl.c(_, tl, es, fs, t, LR.lproj(rows2)) == osome(DC.cl.pick(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), DC.cl.found(es, fs, t, r, h, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev), DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)))) : Bool}
          lcl.h(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), tl, es, fs, t, r, h, k, rows2, bb, prev, d, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), lcl_eq(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)))))

def lclx_eq(hk: HS.HS, h: HS.HS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +k: KS.KS)
  -> {DC.lclx(LR.lean(hk), LR.lean(h), es, fs, t) == osome(DC.cl.go(DC.ddrop(DC.dlen(HS.hs.ds(hk)), HS.hs.ds(h)), es, fs, t, r, h, k, HS.hs.rows(h), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{})) : Bool}:
  match hk h:
    case HS.HS{+rk, +dk} HS.HS{+rows, +ds}:
      lcl_eq(DC.ddrop(DC.dlen(dk), ds), es, fs, t, r, HS.HS{rows, ds}, k, rows, HS.encs(HS.hxs(es, fs, ds), t), Nil{})

# r's lean set, its K squared part lk right: a line exactly when clx finds one
def clx_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +lk: LR.LH, ek: {lk == LR.lean(DC.khull(es, fs, t, DC.Sk.k(s), r)) : LR.LH})
  -> {DC.lclx(lk, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, lk), es, fs, t) == osome(DC.clx(es, fs, t, s, r)) : Bool}:
  %Equal.sym(LR.LH, lk, LR.lean(DC.khull(es, fs, t, DC.Sk.k(s), r)), ek) : {DC.lclx(_, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, _), es, fs, t) == osome(DC.clx(es, fs, t, s, r)) : Bool}
  %LP.fold_eq(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.khull(es, fs, t, DC.Sk.k(s), r)) : {DC.lclx(LR.lean(DC.khull(es, fs, t, DC.Sk.k(s), r)), _, es, fs, t) == osome(DC.clx(es, fs, t, s, r)) : Bool}
  lclx_eq(DC.khull(es, fs, t, DC.Sk.k(s), r), DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.khull(es, fs, t, DC.Sk.k(s), r)), es, fs, t, r, DC.Sk.k(s))

# The cache
# ---------

def absurd(-A: Type, x: Empty) -> A:
  match x:

def bf(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ft(h: {False{} == True{} : Bool}) -> Empty:
  %h : bf(_)
  Unit{}

def neq_t(a: DR.Node, b: DR.Node, h: {DC.node_eq(a, b) == True{} : Bool}) -> {a == b : DR.Node}:
  match a b:
    case DR.NFrame{} DR.NFrame{}:
      {==}
    case DR.NFrame{} DR.NSeg{t}:
      absurd({DR.NFrame{} == DR.NSeg{t} : DR.Node}, ft(h))
    case DR.NSeg{s} DR.NFrame{}:
      absurd({DR.NSeg{s} == DR.NFrame{} : DR.Node}, ft(h))
    case DR.NSeg{+s} DR.NSeg{+t}:
      %LS.eq_ok(s, t, h) : {DR.NSeg{s} == DR.NSeg{_} : DR.Node}
      {==}

# every entry is its node's K squared lean rows, for K = k
def CInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, C: List<&2, DC.KC>) -> Data:
  match C:
    case Nil{}:
      Unit
    case Con{DC.KC{+n, +h}, tl}:
      SK.Both({h == DC.lkhull(es, fs, t, k, n) : LR.LH}, CInv(es, fs, t, k, tl))

def lkhull_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +r: DR.Node) -> {DC.lkhull(es, fs, t, k, r) == LR.lean(DC.khull(es, fs, t, k, r)) : LR.LH}:
  Equal.sym(LR.LH, LR.lean(DC.khull(es, fs, t, k, r)), DC.lkhull(es, fs, t, k, r), LP.fold_eq(DC.kgens(r, KS.ks.ds(k)), es, fs, t, HS.hs0()))

def kc.sel(b: Bool, +h: LR.LH, C: List<&2, DC.KC>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS) -> LR.LH:
  match b:
    case True{}:
      h
    case False{}:
      DC.kc.get(C, r, es, fs, t, k)

def kc_g(C: List<&2, DC.KC>, b: Bool, +h: LR.LH, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS) -> {DC.kc.g(C, b, h, r, es, fs, t, k) == kc.sel(b, h, C, r, es, fs, t, k) : LR.LH}:
  match C b:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{DC.KC{n, h2}, tl} True{}:
      {==}
    case Con{DC.KC{+n, +h2}, +tl} False{}:
      {==}

def kc.s(b: Bool, +n: DR.Node, +h: LR.LH, +tl: List<&2, DC.KC>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, eb: {b == DC.node_eq(n, r) : Bool}, hn: {h == DC.lkhull(es, fs, t, k, n) : LR.LH},
  ih: {DC.kc.get(tl, r, es, fs, t, k) == DC.lkhull(es, fs, t, k, r) : LR.LH}) -> {kc.sel(b, h, tl, r, es, fs, t, k) == DC.lkhull(es, fs, t, k, r) : LR.LH}:
  match b:
    case True{}:
      Equal.trans(LR.LH, h, DC.lkhull(es, fs, t, k, n), DC.lkhull(es, fs, t, k, r), hn,
        (%neq_t(n, r, Equal.sym(Bool, True{}, DC.node_eq(n, r), eb)) : {DC.lkhull(es, fs, t, k, n) == DC.lkhull(es, fs, t, k, _) : LR.LH}
          {==}))
    case False{}:
      ih

# a lookup is the node's K squared lean rows
def kc_get_eq(C: List<&2, DC.KC>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, inv: CInv(es, fs, t, k, C)) -> {DC.kc.get(C, r, es, fs, t, k) == DC.lkhull(es, fs, t, k, r) : LR.LH}:
  match C:
    case Nil{}:
      {==}
    case Con{DC.KC{+n, +h}, +tl}:
      (hn, it) = inv
      Equal.trans(LR.LH, DC.kc.g(tl, DC.node_eq(n, r), h, r, es, fs, t, k), kc.sel(DC.node_eq(n, r), h, tl, r, es, fs, t, k), DC.lkhull(es, fs, t, k, r),
        kc_g(tl, DC.node_eq(n, r), h, r, es, fs, t, k), kc.s(DC.node_eq(n, r), n, h, tl, r, es, fs, t, k, {==}, hn, kc_get_eq(tl, r, es, fs, t, k, it)))

def kc_lean(+C: List<&2, DC.KC>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +inv: CInv(es, fs, t, k, C)) -> {DC.kc.get(C, r, es, fs, t, k) == LR.lean(DC.khull(es, fs, t, k, r)) : LR.LH}:
  Equal.trans(LR.LH, DC.kc.get(C, r, es, fs, t, k), DC.lkhull(es, fs, t, k, r), LR.lean(DC.khull(es, fs, t, k, r)), kc_get_eq(C, r, es, fs, t, k, inv), lkhull_eq(es, fs, t, k, r))

# The complex-line check over the roots
# -------------------------------------

def fsel(b: Bool, +r: DR.Node, tl: List<&2, DC.RL>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk) -> Maybe<&2, DR.Der>:
  match b:
    case True{}:
      DC.clx(es, fs, t, s, r)
    case False{}:
      DC.fclxs(tl, es, fs, t, s)

def fclxs_g(tl: List<&2, DC.RL>, b: Bool, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk) -> {DC.fclxs.g(tl, b, r, es, fs, t, s) == fsel(b, r, tl, es, fs, t, s) : Maybe<&2, DR.Der>}:
  match tl b:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{DC.RLF{}, tl2} True{}:
      {==}
    case Con{DC.RLR{r2, lk, lh}, tl2} True{}:
      {==}
    case Con{DC.RLF{}, +tl2} False{}:
      {==}
    case Con{DC.RLR{+r2, +lk, +lh}, +tl2} False{}:
      {==}

def fclxs.c(m: Maybe<&2, DR.Der>, +r: DR.Node, +rest: List<&2, DC.RL>, +old: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk,
  em: {DC.clx(es, fs, t, s, r) == m : Maybe<&2, DR.Der>}, ih: {DC.fclxs(rest, es, fs, t, s) == old : Maybe<&2, DR.Der>}) -> {fsel(osome(m), r, rest, es, fs, t, s) == DC.clxs.pick(m, old) : Maybe<&2, DR.Der>}:
  match m:
    case Some{+x}:
      em
    case None{}:
      ih

def fx.h(b: Bool, +r: DR.Node, +tl: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C),
  ih: {DC.fclxs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s) == DC.clxs(tl, es, fs, t, s) : Maybe<&2, DR.Der>})
  -> {DC.fclxs(Con{DC.rl.of(b, r, es, fs, t, s, C), DC.rls(tl, es, fs, t, s, C)}, es, fs, t, s) == DC.clxs.if(SV.bnot(b), es, fs, t, s, r, DC.clxs(tl, es, fs, t, s)) : Maybe<&2, DR.Der>}:
  match b:
    case True{}:
      ih
    case False{}:
      Equal.trans(Maybe<&2, DR.Der>, DC.fclxs.g(DC.rls(tl, es, fs, t, s, C), DC.lclx(DC.kc.get(C, r, es, fs, t, DC.Sk.k(s)), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), es, fs, t), r, es, fs, t, s), fsel(DC.lclx(DC.kc.get(C, r, es, fs, t, DC.Sk.k(s)), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), es, fs, t), r, DC.rls(tl, es, fs, t, s, C), es, fs, t, s),
        DC.clxs.pick(DC.clx(es, fs, t, s, r), DC.clxs(tl, es, fs, t, s)),
        fclxs_g(DC.rls(tl, es, fs, t, s, C), DC.lclx(DC.kc.get(C, r, es, fs, t, DC.Sk.k(s)), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), es, fs, t), r, es, fs, t, s),
        (%Equal.sym(Bool, DC.lclx(DC.kc.get(C, r, es, fs, t, DC.Sk.k(s)), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), es, fs, t), osome(DC.clx(es, fs, t, s, r)), clx_eq(es, fs, t, s, r, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s)), kc_lean(C, r, es, fs, t, DC.Sk.k(s), inv)))
          : {fsel(_, r, DC.rls(tl, es, fs, t, s, C), es, fs, t, s) == DC.clxs.pick(DC.clx(es, fs, t, s, r), DC.clxs(tl, es, fs, t, s)) : Maybe<&2, DR.Der>}
          fclxs.c(DC.clx(es, fs, t, s, r), r, DC.rls(tl, es, fs, t, s, C), DC.clxs(tl, es, fs, t, s), es, fs, t, s, {==}, ih)))

# the lean complex-line check over the roots is clxs
def fclxs_eq(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> {DC.fclxs(DC.rls(rs, es, fs, t, s, C), es, fs, t, s) == DC.clxs(rs, es, fs, t, s) : Maybe<&2, DR.Der>}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +tl}:
      fx.h(DC.node_eq(r, DR.NFrame{}), r, tl, es, fs, t, s, C, inv, fclxs_eq(tl, es, fs, t, s, C, inv))

# The merge checks
# ----------------

def fmgF.sel(f: Bool, +mb: DC.Mem, +b: DR.Node, t: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>) -> Maybe<&2, List<&2, DC.Mem>>:
  match f:
    case True{}:
      DC.mgF.pick(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, mb, b, None{})
    case False{}:
      DC.fmgF(t, es, fs, k, ms)

def fmgF_g(t: List<&2, DC.Mem>, f: Bool, +mb: DC.Mem, +b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>)
  -> {DC.fmgF.g(t, f, mb, b, es, fs, k, ms) == fmgF.sel(f, mb, b, t, es, fs, k, ms) : Maybe<&2, List<&2, DC.Mem>>}:
  match t f:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{DC.Mem{b2, rb, wb, db}, t2} True{}:
      {==}
    case Con{DC.Mem{+b2, +rb, +wb, +db}, +t2} False{}:
      {==}

def mgf.m(m: Maybe<&2, DR.Lab>, +mb: DC.Mem, +b: DR.Node, +t: List<&2, DC.Mem>, +old: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>,
  em: {LB.ks.lab(es, fs, k, DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, ih: {DC.fmgF(t, es, fs, k, ms) == old : Maybe<&2, List<&2, DC.Mem>>})
  -> {fmgF.sel(LP.lab.some(m), mb, b, t, es, fs, k, ms) == DC.mgF.pick(m, es, fs, k, ms, mb, b, old) : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case Some{+w}:
      %Equal.sym(Maybe<&2, DR.Lab>, LB.ks.lab(es, fs, k, DR.zdir(es, b)), Some{w}, em) : {DC.mgF.pick(_, es, fs, k, ms, mb, b, None{}) == DC.mgF.pick(Some{w}, es, fs, k, ms, mb, b, old) : Maybe<&2, List<&2, DC.Mem>>}
      {==}
    case None{}:
      ih

def mgf.i(c: Bool, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +t: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>,
  ih: {DC.fmgF(t, es, fs, k, ms) == DC.mgF(t, es, fs, k, ms) : Maybe<&2, List<&2, DC.Mem>>})
  -> {fmgF.sel(SV.band(c, LR.ks.llab(k, DR.zdir(es, b))), DC.Mem{b, rb, wb, db}, b, t, es, fs, k, ms) == DC.mgF.if(c, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, DC.mgF(t, es, fs, k, ms)) : Maybe<&2, List<&2, DC.Mem>>}:
  match c:
    case False{}:
      ih
    case True{}:
      %LP.ks_lab_eq(es, fs, k, DR.zdir(es, b)) : {fmgF.sel(_, DC.Mem{b, rb, wb, db}, b, t, es, fs, k, ms) == DC.mgF.pick(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, DC.mgF(t, es, fs, k, ms)) : Maybe<&2, List<&2, DC.Mem>>}
      mgf.m(LB.ks.lab(es, fs, k, DR.zdir(es, b)), DC.Mem{b, rb, wb, db}, b, t, DC.mgF(t, es, fs, k, ms), es, fs, k, ms, {==}, ih)

# the lean frame merge check is mgF
def fmgF_eq(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>) -> {DC.fmgF(sc, es, fs, k, ms) == DC.mgF(sc, es, fs, k, ms) : Maybe<&2, List<&2, DC.Mem>>}:
  match sc:
    case Nil{}:
      {==}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +t}:
      Equal.trans(Maybe<&2, List<&2, DC.Mem>>, DC.fmgF.g(t, SV.band(SV.bnot(DC.node_eq(rb, DR.NFrame{})), LR.ks.llab(k, DR.zdir(es, b))), DC.Mem{b, rb, wb, db}, b, es, fs, k, ms),
        fmgF.sel(SV.band(SV.bnot(DC.node_eq(rb, DR.NFrame{})), LR.ks.llab(k, DR.zdir(es, b))), DC.Mem{b, rb, wb, db}, b, t, es, fs, k, ms),
        DC.mgF.if(SV.bnot(DC.node_eq(rb, DR.NFrame{})), es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, DC.mgF(t, es, fs, k, ms)),
        fmgF_g(t, SV.band(SV.bnot(DC.node_eq(rb, DR.NFrame{})), LR.ks.llab(k, DR.zdir(es, b))), DC.Mem{b, rb, wb, db}, b, es, fs, k, ms),
        mgf.i(SV.bnot(DC.node_eq(rb, DR.NFrame{})), b, rb, wb, db, t, es, fs, k, ms, fmgF_eq(t, es, fs, k, ms)))

def fmgR.sel(f: Bool, +mb: DC.Mem, +b: DR.Node, tl: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +lh: LR.LH, +s: DC.Sk, +r: DR.Node, +ms: List<&2, DC.Mem>) -> Maybe<&2, List<&2, DC.Mem>>:
  match f:
    case True{}:
      DC.mgR.pick(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)), es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, mb, b, None{})
    case False{}:
      DC.fmgR(tl, es, fs, t, lh, s, r, ms)

def fmgR_g(tl: List<&2, DC.Mem>, f: Bool, +mb: DC.Mem, +b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +lh: LR.LH, +s: DC.Sk, +r: DR.Node, +ms: List<&2, DC.Mem>)
  -> {DC.fmgR.g(tl, f, mb, b, es, fs, t, lh, s, r, ms) == fmgR.sel(f, mb, b, tl, es, fs, t, lh, s, r, ms) : Maybe<&2, List<&2, DC.Mem>>}:
  match tl f:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{DC.Mem{b2, rb, wb, db}, t2} True{}:
      {==}
    case Con{DC.Mem{+b2, +rb, +wb, +db}, +t2} False{}:
      {==}

def mgr.m(m: Maybe<&2, DR.Lab>, +mb: DC.Mem, +b: DR.Node, +tl: List<&2, DC.Mem>, +old: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +lh: LR.LH, +s: DC.Sk, +r: DR.Node, +ms: List<&2, DC.Mem>,
  em: {LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, ih: {DC.fmgR(tl, es, fs, t, lh, s, r, ms) == old : Maybe<&2, List<&2, DC.Mem>>})
  -> {fmgR.sel(LP.lab.some(m), mb, b, tl, es, fs, t, lh, s, r, ms) == DC.mgR.pick(m, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, mb, b, old) : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case Some{+w}:
      %Equal.sym(Maybe<&2, DR.Lab>, LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)), Some{w}, em) : {DC.mgR.pick(_, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, mb, b, None{}) == DC.mgR.pick(Some{w}, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, mb, b, old) : Maybe<&2, List<&2, DC.Mem>>}
      {==}
    case None{}:
      ih

def mgr.i(c: Bool, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +tl: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +lh: LR.LH, +s: DC.Sk, +r: DR.Node, +ms: List<&2, DC.Mem>,
  elh: {lh == LR.lean(DC.rhull(es, fs, t, s, r)) : LR.LH}, ih: {DC.fmgR(tl, es, fs, t, lh, s, r, ms) == DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms) : Maybe<&2, List<&2, DC.Mem>>})
  -> {fmgR.sel(SV.band(c, LR.lh.lab(lh, DR.zdir(es, b), t)), DC.Mem{b, rb, wb, db}, b, tl, es, fs, t, lh, s, r, ms) == DC.mgR.if(c, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, DC.Mem{b, rb, wb, db}, b, DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms)) : Maybe<&2, List<&2, DC.Mem>>}:
  match c:
    case False{}:
      ih
    case True{}:
      %Equal.sym(LR.LH, lh, LR.lean(DC.rhull(es, fs, t, s, r)), elh) : {fmgR.sel(LR.lh.lab(_, DR.zdir(es, b), t), DC.Mem{b, rb, wb, db}, b, tl, es, fs, t, lh, s, r, ms) == DC.mgR.pick(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)), es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, DC.Mem{b, rb, wb, db}, b, DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms)) : Maybe<&2, List<&2, DC.Mem>>}
      %LP.hs_lab_eq(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)) : {fmgR.sel(_, DC.Mem{b, rb, wb, db}, b, tl, es, fs, t, lh, s, r, ms) == DC.mgR.pick(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)), es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, DC.Mem{b, rb, wb, db}, b, DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms)) : Maybe<&2, List<&2, DC.Mem>>}
      mgr.m(LB.hs.lab(es, fs, t, DC.rhull(es, fs, t, s, r), DR.zdir(es, b)), DC.Mem{b, rb, wb, db}, b, tl, DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms), es, fs, t, lh, s, r, ms, {==}, ih)

# the lean merge check at a free root r (lh its lean set) is mgR
def fmgR_eq(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +lh: LR.LH, +s: DC.Sk, +r: DR.Node, +ms: List<&2, DC.Mem>, +elh: {lh == LR.lean(DC.rhull(es, fs, t, s, r)) : LR.LH})
  -> {DC.fmgR(sc, es, fs, t, lh, s, r, ms) == DC.mgR(sc, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms) : Maybe<&2, List<&2, DC.Mem>>}:
  match sc:
    case Nil{}:
      {==}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      Equal.trans(Maybe<&2, List<&2, DC.Mem>>, DC.fmgR.g(tl, SV.band(SV.bnot(DC.node_eq(rb, r)), LR.lh.lab(lh, DR.zdir(es, b), t)), DC.Mem{b, rb, wb, db}, b, es, fs, t, lh, s, r, ms),
        fmgR.sel(SV.band(SV.bnot(DC.node_eq(rb, r)), LR.lh.lab(lh, DR.zdir(es, b), t)), DC.Mem{b, rb, wb, db}, b, tl, es, fs, t, lh, s, r, ms),
        DC.mgR.if(SV.bnot(DC.node_eq(rb, r)), es, fs, t, DC.rhull(es, fs, t, s, r), r, ms, DC.Mem{b, rb, wb, db}, b, DC.mgR(tl, es, fs, t, DC.rhull(es, fs, t, s, r), r, ms)),
        fmgR_g(tl, SV.band(SV.bnot(DC.node_eq(rb, r)), LR.lh.lab(lh, DR.zdir(es, b), t)), DC.Mem{b, rb, wb, db}, b, es, fs, t, lh, s, r, ms),
        mgr.i(SV.bnot(DC.node_eq(rb, r)), b, rb, wb, db, tl, es, fs, t, lh, s, r, ms, elh, fmgR_eq(tl, es, fs, t, lh, s, r, ms, elh)))

def fmgs_g(tl: List<&2, DC.RL>, m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk)
  -> {DC.fmgs.g(tl, m, es, fs, t, s) == DC.mgs.pick(m, DC.fmgs(tl, es, fs, t, s)) : Maybe<&2, List<&2, DC.Mem>>}:
  match tl m:
    case Nil{} Some{+x}:
      {==}
    case Nil{} None{}:
      {==}
    case Con{DC.RLF{}, tl2} Some{+x}:
      {==}
    case Con{DC.RLR{r, lk, lh}, tl2} Some{+x}:
      {==}
    case Con{DC.RLF{}, +tl2} None{}:
      {==}
    case Con{DC.RLR{+r, +lk, +lh}, +tl2} None{}:
      {==}

# r's lean set is the lean projection of its hull
def lh_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C)) -> {LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))) == LR.lean(DC.rhull(es, fs, t, s, r)) : LR.LH}:
  Equal.trans(LR.LH, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, LR.lean(DC.khull(es, fs, t, DC.Sk.k(s), r))), LR.lean(DC.rhull(es, fs, t, s, r)),
    (%kc_lean(C, r, es, fs, t, DC.Sk.k(s), inv) : {LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))) == LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, _) : LR.LH}
      {==}),
    Equal.sym(LR.LH, LR.lean(DC.rhull(es, fs, t, s, r)), LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, LR.lean(DC.khull(es, fs, t, DC.Sk.k(s), r))), LP.fold_eq(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.khull(es, fs, t, DC.Sk.k(s), r))))

def fm.h(b: Bool, +r: DR.Node, +tl: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C),
  ih: {DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s) == DC.mgs(tl, es, fs, t, s) : Maybe<&2, List<&2, DC.Mem>>})
  -> {DC.fmgs(Con{DC.rl.of(b, r, es, fs, t, s, C), DC.rls(tl, es, fs, t, s, C)}, es, fs, t, s) == DC.mgs.pick(DC.mgs.root(b, es, fs, t, s, r), DC.mgs(tl, es, fs, t, s)) : Maybe<&2, List<&2, DC.Mem>>}:
  match b:
    case True{}:
      Equal.trans(Maybe<&2, List<&2, DC.Mem>>, DC.fmgs.g(DC.rls(tl, es, fs, t, s, C), DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), es, fs, t, s),
        DC.mgs.pick(DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)), DC.mgs.pick(DC.mgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), DC.mgs(tl, es, fs, t, s)),
        fmgs_g(DC.rls(tl, es, fs, t, s, C), DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), es, fs, t, s),
        (%fmgF_eq(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)) : {DC.mgs.pick(DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)) == DC.mgs.pick(_, DC.mgs(tl, es, fs, t, s)) : Maybe<&2, List<&2, DC.Mem>>}
          (%ih : {DC.mgs.pick(DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)) == DC.mgs.pick(DC.fmgF(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s)), _) : Maybe<&2, List<&2, DC.Mem>>}
            {==})))
    case False{}:
      Equal.trans(Maybe<&2, List<&2, DC.Mem>>, DC.fmgs.g(DC.rls(tl, es, fs, t, s, C), DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), es, fs, t, s),
        DC.mgs.pick(DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)), DC.mgs.pick(DC.mgR(DC.Sk.ms(s), es, fs, t, DC.rhull(es, fs, t, s, r), r, DC.Sk.ms(s)), DC.mgs(tl, es, fs, t, s)),
        fmgs_g(DC.rls(tl, es, fs, t, s, C), DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), es, fs, t, s),
        (%fmgR_eq(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s), lh_eq(es, fs, t, s, r, C, inv)) : {DC.mgs.pick(DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)) == DC.mgs.pick(_, DC.mgs(tl, es, fs, t, s)) : Maybe<&2, List<&2, DC.Mem>>}
          (%ih : {DC.mgs.pick(DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), DC.fmgs(DC.rls(tl, es, fs, t, s, C), es, fs, t, s)) == DC.mgs.pick(DC.fmgR(DC.Sk.ms(s), es, fs, t, LR.lfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.kc.get(C, r, es, fs, t, DC.Sk.k(s))), s, r, DC.Sk.ms(s)), _) : Maybe<&2, List<&2, DC.Mem>>}
            {==})))

# the lean merge check over the roots is mgs
def fmgs_eq(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> {DC.fmgs(DC.rls(rs, es, fs, t, s, C), es, fs, t, s) == DC.mgs(rs, es, fs, t, s) : Maybe<&2, List<&2, DC.Mem>>}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +tl}:
      fm.h(DC.node_eq(r, DR.NFrame{}), r, tl, es, fs, t, s, C, inv, fmgs_eq(tl, es, fs, t, s, C, inv))

# Adding to K keeps the cache
# ---------------------------

def kc_of_inv(ns: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS) -> CInv(es, fs, t, k, DC.kc.of(ns, es, fs, t, k)):
  match ns:
    case Nil{}:
      Unit{}
    case Con{+n, tl}:
      ({==}, kc_of_inv(tl, es, fs, t, k))

def kgens_snoc(+n: DR.Node, ds: List<&2, DR.Der>, +d: DR.Der) -> {DC.kgens(n, KS.dsnoc(ds, d)) == DC.dcat(DC.kgens(n, ds), Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}) : List<&2, DR.Der>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      %kgens_snoc(n, tl, d) : {Con{HS.kre(n, h), Con{HS.kim(n, h), DC.kgens(n, KS.dsnoc(tl, d))}} == Con{HS.kre(n, h), Con{HS.kim(n, h), _}} : List<&2, DR.Der>}
      {==}

def lfold_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: LR.LH)
  -> {LR.lfold(DC.dcat(xs, ys), es, fs, t, h) == LR.lfold(ys, es, fs, t, LR.lfold(xs, es, fs, t, h)) : LR.LH}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      lfold_cat(xt, ys, es, fs, t, LR.lh.add(es, fs, t, h, x))

def kc_upd_inv(C: List<&2, DC.KC>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +x: EL.Row, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, inv: CInv(es, fs, t, KS.KS{rows, ds}, C))
  -> CInv(es, fs, t, KS.KS{EL.rsnoc(rows, x), KS.dsnoc(ds, d)}, DC.kc.upd(C, d, es, fs, t)):
  match C:
    case Nil{}:
      Unit{}
    case Con{DC.KC{+n, +h}, +tl}:
      (hn, it) = inv
      ((%Equal.sym(LR.LH, h, DC.lkhull(es, fs, t, KS.KS{rows, ds}, n), hn) : {LR.lfold(Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}, es, fs, t, _) == DC.lkhull(es, fs, t, KS.KS{EL.rsnoc(rows, x), KS.dsnoc(ds, d)}, n) : LR.LH}
        %Equal.sym(List<&2, DR.Der>, DC.kgens(n, KS.dsnoc(ds, d)), DC.dcat(DC.kgens(n, ds), Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}), kgens_snoc(n, ds, d))
          : {LR.lfold(Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}, es, fs, t, DC.lkhull(es, fs, t, KS.KS{rows, ds}, n)) == LR.lfold(_, es, fs, t, LR.LH{Nil{}, Nil{}}) : LR.LH}
        Equal.sym(LR.LH, LR.lfold(DC.dcat(DC.kgens(n, ds), Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}), es, fs, t, LR.LH{Nil{}, Nil{}}), LR.lfold(Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}, es, fs, t, DC.lkhull(es, fs, t, KS.KS{rows, ds}, n)),
          lfold_cat(DC.kgens(n, ds), Con{HS.kre(n, d), Con{HS.kim(n, d), Nil{}}}, es, fs, t, LR.LH{Nil{}, Nil{}}))),
       kc_upd_inv(tl, rows, ds, x, d, es, fs, t, it))

def ka.h(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der, +C: List<&2, DC.KC>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, inv: CInv(es, fs, t, KS.KS{rows, ds}, C))
  -> CInv(es, fs, t, KS.ks.pick(b, rows, ds, r, d), DC.kc.upd.k(b, C, d, es, fs, t)):
  match b:
    case True{}:
      inv
    case False{}:
      kc_upd_inv(C, rows, ds, EL.row_of(r), d, es, fs, t, inv)

# K given d, the cache given d
def kc_add_inv(k: KS.KS, +C: List<&2, DC.KC>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, inv: CInv(es, fs, t, k, C))
  -> CInv(es, fs, t, KS.ks.add(es, fs, k, d), DC.kc.add(C, d, es, fs, t, k)):
  match k:
    case KS.KS{+rows, +ds}:
      %LP.inb_eq(rows, DR.Jd.e(DR.concl(es, fs, d))) : CInv(es, fs, t, KS.ks.add(es, fs, KS.KS{rows, ds}, d), DC.kc.upd.k(_, C, d, es, fs, t))
      ka.h(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d, C, es, fs, t, inv)

# The round
# ---------

# the cache is right for the round's result, when that is a step
def CacheOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +C: List<&2, DC.KC>, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      CInv(es, fs, t, DC.Sk.k(s), C)
    case DC.OFix{s}:
      Unit
    case DC.OOne{d}:
      Unit
    case DC.OVoid{g, dr, di}:
      Unit

def FRel(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, fo: DC.FO, +o: DC.Out) -> Data:
  match fo:
    case DC.FO{+o2, +C}:
      SK.Both({o2 == o : DC.Out}, CacheOk(es, fs, t, C, o))

def c4_cache(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C)) -> CacheOk(es, fs, t, C, DC.r.c4(m, s)):
  match m:
    case None{}:
      Unit{}
    case Some{+l}:
      inv

def c3_cache(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> CacheOk(es, fs, t, C, DC.r.c3(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      c4_cache(DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))), es, fs, t, s, C, inv)
    case Some{+ms2}:
      inv

def fr.c2_ok(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> FRel(es, fs, t, DC.fr.c2(m, DC.rls(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C), es, fs, t, cs, ids, s, C), DC.r.c2(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      ((%fmgs_eq(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C, inv) : {DC.r.c3(DC.fmgs(DC.rls(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C), es, fs, t, s), es, fs, t, cs, ids, s) == DC.r.c3(_, es, fs, t, cs, ids, s) : DC.Out}
        {==}),
       c3_cache(DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, t, cs, ids, s, C, inv))
    case Some{+d}:
      ({==}, kc_add_inv(DC.Sk.k(s), C, d, es, fs, t, inv))

def fr.c1_ok(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> FRel(es, fs, t, DC.fr.c1(m, es, fs, t, cs, ids, s, C), DC.r.c1(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      %fclxs_eq(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C, inv) : FRel(es, fs, t, DC.fr.c2(DC.fclxs(DC.rls(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C), es, fs, t, s), DC.rls(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C), es, fs, t, cs, ids, s, C), DC.r.c2(_, es, fs, t, cs, ids, s))
      fr.c2_ok(DC.fclxs(DC.rls(DC.roots(DC.Sk.ms(s)), es, fs, t, s, C), es, fs, t, s), es, fs, t, cs, ids, s, C, inv)
    case Some{+d}:
      ({==}, kc_add_inv(DC.Sk.k(s), C, d, es, fs, t, inv))

def fr.e2_ok(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> FRel(es, fs, t, DC.fr.e2(m, es, fs, t, cs, ids, s, C), DC.r.e2(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      %ffback_eq(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) : FRel(es, fs, t, DC.fr.c1(DC.ffback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), es, fs, t, cs, ids, s, C), DC.r.c1(_, es, fs, t, cs, ids, s))
      fr.c1_ok(DC.ffback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), es, fs, t, cs, ids, s, C, inv)
    case Some{+g}:
      ({==}, Unit{})

def fr.e1_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> FRel(es, fs, t, DC.fr.e1(f, es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), DC.r.e1(f, es, fs, t, cs, ids, s)):
  match f:
    case True{}:
      ({==}, Unit{})
    case False{}:
      %fvoid_eq(ids, es, cs, DC.Sk.k(s)) : FRel(es, fs, t, DC.fr.e2(DC.fvoid(DC.oids(ids, es, cs), es, DC.Sk.k(s)), es, fs, t, cs, ids, s, C), DC.r.e2(_, es, fs, t, cs, ids, s))
      fr.e2_ok(DC.fvoid(DC.oids(ids, es, cs), es, DC.Sk.k(s)), es, fs, t, cs, ids, s, C, inv)

# a fast round returns the round's Out, with the cache right for it
def fround_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, +C: List<&2, DC.KC>, +inv: CInv(es, fs, t, DC.Sk.k(s), C))
  -> FRel(es, fs, t, DC.fround(es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), DC.round(es, fs, t, cs, ids, s)):
  %LP.ks_inb_eq(DC.Sk.k(s), DR.cst(DR.qo())) : FRel(es, fs, t, DC.fr.e1(_, es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), DC.round(es, fs, t, cs, ids, s))
  fr.e1_ok(KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), es, fs, t, cs, ids, s, C, inv)

# The run
# -------

def frun_eq(fuel: Nat, fo: DC.FO, +o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, h: FRel(es, fs, t, fo, o))
  -> {DC.frun(fuel, fo, es, fs, t, cs, DC.oids(ids, es, cs), ids) == DC.run(fuel, o, es, fs, t, cs, ids) : DC.Out}:
  match fuel fo:
    case 0n DC.FO{+o2, +C}:
      (eo, hc) = h
      eo
    case 1n+f DC.FO{DC.OStep{+s}, +C}:
      (+eo, hc) = h
      %eo : {DC.frun(f, DC.fround(es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), es, fs, t, cs, DC.oids(ids, es, cs), ids) == DC.run(1n+f, _, es, fs, t, cs, ids) : DC.Out}
      frun_eq(f, DC.fround(es, fs, t, cs, DC.oids(ids, es, cs), ids, s, C), DC.round(es, fs, t, cs, ids, s), es, fs, t, cs, ids,
        fround_ok(es, fs, t, cs, ids, s, C, (%Equal.sym(DC.Out, DC.OStep{s}, o, eo) : CacheOk(es, fs, t, C, _) hc)))
    case 1n+f DC.FO{DC.OFix{+s}, +C}:
      (eo, hc) = h
      %eo : {DC.OFix{s} == DC.run(1n+f, _, es, fs, t, cs, ids) : DC.Out}
      {==}
    case 1n+f DC.FO{DC.OOne{+d}, +C}:
      (eo, hc) = h
      %eo : {DC.OOne{d} == DC.run(1n+f, _, es, fs, t, cs, ids) : DC.Out}
      {==}
    case 1n+f DC.FO{DC.OVoid{+sg, +dr, +di}, +C}:
      (eo, hc) = h
      %eo : {DC.OVoid{sg, dr, di} == DC.run(1n+f, _, es, fs, t, cs, ids) : DC.Out}
      {==}

# the fast run returns what the run as designed returns
def dclose_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat) -> {DC.dclose(es, fs, ctx, t, fuel) == DC.dclose_ref(es, fs, ctx, t, fuel) : DC.Out}:
  frun_eq(fuel, DC.FO{DC.OStep{DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))}, DC.kc.of(DC.snodes(DC.oids(DC.segids(es), es, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))), es, fs, t, DC.Sk.k(DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))))}, DC.OStep{DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))}, es, fs, t, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}), DC.segids(es),
    ({==}, kc_of_inv(DC.snodes(DC.oids(DC.segids(es), es, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))), es, fs, t, DC.Sk.k(DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))))))
