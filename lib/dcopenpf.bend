# bend-cad: the closure's open test is right (lib/dclose.bend). The
# context's span (sp.of) keeps sk-13a's row invariant, and every context
# equation lies in the span of the expressions it kept; so a constant
# combination of the context is in that span (in_dlin), and a segment
# collapsed in the context passes coll. Hence isopen true means
# spec/dir.bend's Open (open_of). Conversely the span keeps only context
# expressions, so what passes coll is collapsed in the context
# (coll_sound). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./spanpf.bend as SN
import ./pairpf.bend as PP
import ./hspacepf.bend as HP
import ./labpf.bend as LP
import ./dclose.bend as DC
import ./q.bend as LQ
import ./qring.bend as QR
import ./identpf.bend as ID
import ./listpf.bend as LP2

def absurd(-A: Type, x: Empty) -> A:
  match x:

# every expression of src is in the span of bs
def AllIn(src: List<&2, E.QExpr>, +bs: List<&2, E.QExpr>) -> Data:
  match src:
    case Nil{}:
      Unit
    case Con{+e, t}:
      SK.Both(SN.InSpan(e, bs), AllIn(t, bs))

def SPInv(s: DC.SP) -> Data:
  match s:
    case DC.SP{+rows, +bs}:
      SK.Both({EP.rinv(bs, rows, 0n) == True{} : Bool}, {EL.rlen(rows) == SV.neqs(bs) : Nat})

def sp.bs(s: DC.SP) -> List<&2, E.QExpr>:
  match s:
    case DC.SP{rows, bs}:
      bs

# The span keeps its invariant
# ----------------------------

def sp_add.pick(b: Bool, +rows: List<&2, EL.Row>, +bs: List<&2, E.QExpr>, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, e))) : Bool},
  +hr: {EP.rinv(bs, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(bs) : Nat}) -> SPInv(DC.sp.pick(b, rows, bs, EL.resid(rows, e), e)):
  match b:
    case True{}:
      (hr, hl)
    case False{}:
      (EP.new_rinv(bs, rows, e, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, e))), eb)), PP.len_snoc(bs, rows, e, EL.row_of(EL.resid(rows, e)), hl))

def sp_add_inv(s: DC.SP, +e: E.QExpr, h: SPInv(s)) -> SPInv(DC.sp.add(s, e)):
  match s:
    case DC.SP{+rows, +bs}:
      (hr, hl) = h
      sp_add.pick(EP.isnil(EP.resp(EL.resid(rows, e))), rows, bs, e, {==}, hr, hl)

def sp_of_inv(es: List<&2, E.QExpr>, +s: DC.SP, h: SPInv(s)) -> SPInv(DC.sp.of(es, s)):
  match es:
    case Nil{}:
      h
    case Con{+e, t}:
      sp_of_inv(t, DC.sp.add(s, e), sp_add_inv(s, e, h))

def sp0_inv() -> SPInv(DC.SP{Nil{}, Nil{}}):
  ({==}, {==})

# Spans only grow, and take in what is added
# ------------------------------------------

def sp_mono.pick(b: Bool, +rows: List<&2, EL.Row>, +bs: List<&2, E.QExpr>, +r: EL.Res, +e: E.QExpr, +x: E.QExpr, +h: SN.InSpan(x, bs))
  -> SN.InSpan(x, sp.bs(DC.sp.pick(b, rows, bs, r, e))):
  match b:
    case True{}:
      h
    case False{}:
      SN.in_snoc(x, bs, e, h)

def sp_add_mono(s: DC.SP, +e: E.QExpr, +x: E.QExpr, +h: SN.InSpan(x, sp.bs(s))) -> SN.InSpan(x, sp.bs(DC.sp.add(s, e))):
  match s:
    case DC.SP{+rows, +bs}:
      sp_mono.pick(EP.isnil(EP.resp(EL.resid(rows, e))), rows, bs, EL.resid(rows, e), e, x, h)

def sp_of_mono(es: List<&2, E.QExpr>, +s: DC.SP, +x: E.QExpr, +h: SN.InSpan(x, sp.bs(s))) -> SN.InSpan(x, sp.bs(DC.sp.of(es, s))):
  match es:
    case Nil{}:
      h
    case Con{+e, t}:
      sp_of_mono(t, DC.sp.add(s, e), x, sp_add_mono(s, e, x, h))

def sp_in.pick(b: Bool, +rows: List<&2, EL.Row>, +bs: List<&2, E.QExpr>, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, e))) : Bool},
  +hr: {EP.rinv(bs, rows, 0n) == True{} : Bool}) -> SN.InSpan(e, sp.bs(DC.sp.pick(b, rows, bs, EL.resid(rows, e), e))):
  match b:
    case True{}:
      SN.in_of_zero(bs, rows, e, hr, Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, e))), eb))
    case False{}:
      SN.in_last(bs, e)

def sp_add_in(s: DC.SP, +e: E.QExpr, h: SPInv(s)) -> SN.InSpan(e, sp.bs(DC.sp.add(s, e))):
  match s:
    case DC.SP{+rows, +bs}:
      (hr, hl) = h
      sp_in.pick(EP.isnil(EP.resp(EL.resid(rows, e))), rows, bs, e, {==}, hr)

# every expression folded in is in the final span
def sp_of_all(es: List<&2, E.QExpr>, +s: DC.SP, +h: SPInv(s)) -> AllIn(es, sp.bs(DC.sp.of(es, s))):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (sp_of_mono(t, DC.sp.add(s, e), e, sp_add_in(s, e, h)), sp_of_all(t, DC.sp.add(s, e), sp_add_inv(s, e, h)))

# Collapsed in the context
# ------------------------

def in_dlin(ls: List<&2, S.Q>, src: List<&2, E.QExpr>, +bs: List<&2, E.QExpr>, h: AllIn(src, bs)) -> SN.InSpan(DR.dlin(ls, src), bs):
  match ls src:
    case Con{+l, +lt} Con{+e, +et}:
      (h1, h2) = h
      SN.in_comb(l, e, DR.dlin(lt, et), bs, h1, in_dlin(lt, et, bs, h2))
    case Nil{} src:
      SN.in_zero(bs)
    case Con{+l, +lt} Nil{}:
      SN.in_zero(bs)

def in_of_dr(+e: E.QExpr, +src: List<&2, E.QExpr>, +bs: List<&2, E.QExpr>, h: DR.InSpan(e, src), ha: AllIn(src, bs)) -> SN.InSpan(e, bs):
  (+ls, hs) = h
  PP.in_tr(DR.dlin(ls, src), e, bs, in_dlin(ls, src, bs, ha), hs)

def nb(b: Bool, h1: {b == True{} : Bool}, h2: {SV.bnot(b) == True{} : Bool}) -> Empty:
  match b:
    case True{}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h2))
    case False{}:
      LP.tf(Equal.sym(Bool, False{}, True{}, h1))

def coll_of(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, cs: DC.SP, +s: Nat, hi: SPInv(cs), +ha: AllIn(ctx, sp.bs(cs)), hc: DR.Collapsed(es, ctx, s))
  -> {DC.coll(es, cs, s) == True{} : Bool}:
  match cs:
    case DC.SP{+rows, +bs}:
      (+hr, +hl) = hi
      (cx, cy) = hc
      HP.band_tt(DC.sp.inb(DC.SP{rows, bs}, SK.VE.x(DR.zseg(es, s))), DC.sp.inb(DC.SP{rows, bs}, SK.VE.y(DR.zseg(es, s))),
        SN.zero_of_in(bs, rows, SK.VE.x(DR.zseg(es, s)), hr, hl, in_of_dr(SK.VE.x(DR.zseg(es, s)), ctx, bs, cx, ha)),
        SN.zero_of_in(bs, rows, SK.VE.y(DR.zseg(es, s)), hr, hl, in_of_dr(SK.VE.y(DR.zseg(es, s)), ctx, bs, cy, ha)))

# the context's span, as the closure builds it
def cspan(+ctx: List<&2, E.QExpr>) -> DC.SP:
  DC.sp.of(ctx, DC.SP{Nil{}, Nil{}})

# a node the closure finds open is open
def open_of(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, n: DR.Node, h: {DC.isopen(es, cspan(ctx), n) == True{} : Bool}) -> DR.Open(es, ctx, n):
  match n:
    case DR.NFrame{}:
      Unit{}
    case DR.NSeg{+s}:
      hc => nb(DC.coll(es, cspan(ctx), s),
        coll_of(es, ctx, cspan(ctx), s, sp_of_inv(ctx, DC.SP{Nil{}, Nil{}}, sp0_inv()), sp_of_all(ctx, DC.SP{Nil{}, Nil{}}, sp0_inv()), hc), h)

# The test is sound
# -----------------

def in_hd.at(+p: List<&2, S.Q>, +e: E.QExpr, +t: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, e), E.qeval(p, SV.lin(Con{DR.qo(), Nil{}}, Con{e, t}))):
  QR.qring_eq([E.qeval(p, e)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==})

# an expression is in the span of a list it heads
def in_hd(+e: E.QExpr, +t: List<&2, E.QExpr>) -> SN.InSpan(e, Con{e, t}):
  SN.in_of_ident(e, Con{e, t}, Con{DR.qo(), Nil{}}, p => in_hd.at(p, e, t))

def in_tl.q(+X: S.Q, +E0: S.Q, +L: S.Q, h: S.Q.eq(X, L)) -> S.Q.eq(X, S.Q.add(S.Q.mul(DR.qz(), E0), L)):
  LQ.q_trans(X, L, S.Q.add(S.Q.mul(DR.qz(), E0), L), h, QR.qring_eq([E0, L], E.QVar{1n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QVar{1n}}, {==}))

def in_tl.at(+p: List<&2, S.Q>, +x: E.QExpr, +e: E.QExpr, +t: List<&2, E.QExpr>, +ls: List<&2, S.Q>, i: SV.Ident(x, SV.lin(ls, t)))
  -> S.Q.eq(E.qeval(p, x), E.qeval(p, SV.lin(Con{DR.qz(), ls}, Con{e, t}))):
  in_tl.q(E.qeval(p, x), E.qeval(p, e), E.qeval(p, SV.lin(ls, t)), i(p))

# and of the list with one more in front
def in_tl(+x: E.QExpr, +e: E.QExpr, +t: List<&2, E.QExpr>, +h: SN.InSpan(x, t)) -> SN.InSpan(x, Con{e, t}):
  SN.in_of_ident(x, Con{e, t}, Con{DR.qz(), SN.in_ls(x, t, h)}, p => in_tl.at(p, x, e, t, SN.in_ls(x, t, h), SN.in_ident(x, t, h)))

def allin_tl(xs: List<&2, E.QExpr>, +e: E.QExpr, +t: List<&2, E.QExpr>, h: AllIn(xs, t)) -> AllIn(xs, Con{e, t}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, xt}:
      (+h1, h2) = h
      (in_tl(x, e, t, h1), allin_tl(xt, e, t, h2))

# every expression of a list is in its span
def all_self(xs: List<&2, E.QExpr>) -> AllIn(xs, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (in_hd(e, t), allin_tl(t, e, t, all_self(t)))

def allin_snoc(bs: List<&2, E.QExpr>, +e: E.QExpr, +full: List<&2, E.QExpr>, hb: AllIn(bs, full), he: SN.InSpan(e, full)) -> AllIn(EP.qsnoc(bs, e), full):
  match bs:
    case Nil{}:
      (he, Unit{})
    case Con{+b, bt}:
      (h1, h2) = hb
      (h1, allin_snoc(bt, e, full, h2, he))

def sp_back.pick(b: Bool, +rows: List<&2, EL.Row>, +bs: List<&2, E.QExpr>, +r: EL.Res, +e: E.QExpr, +full: List<&2, E.QExpr>, hb: AllIn(bs, full), he: SN.InSpan(e, full))
  -> AllIn(sp.bs(DC.sp.pick(b, rows, bs, r, e)), full):
  match b:
    case True{}:
      hb
    case False{}:
      allin_snoc(bs, e, full, hb, he)

def sp_back_add(s: DC.SP, +e: E.QExpr, +full: List<&2, E.QExpr>, hs: AllIn(sp.bs(s), full), he: SN.InSpan(e, full)) -> AllIn(sp.bs(DC.sp.add(s, e)), full):
  match s:
    case DC.SP{+rows, +bs}:
      sp_back.pick(EP.isnil(EP.resp(EL.resid(rows, e))), rows, bs, EL.resid(rows, e), e, full, hs, he)

# the span keeps only what is in the full list's span
def sp_back_of(es: List<&2, E.QExpr>, +s: DC.SP, +full: List<&2, E.QExpr>, hs: AllIn(sp.bs(s), full), he: AllIn(es, full)) -> AllIn(sp.bs(DC.sp.of(es, s)), full):
  match es:
    case Nil{}:
      hs
    case Con{+e, t}:
      (h1, h2) = he
      sp_back_of(t, DC.sp.add(s, e), full, sp_back_add(s, e, full, hs, h1), h2)

def in_lin(ls: List<&2, S.Q>, src: List<&2, E.QExpr>, +bs: List<&2, E.QExpr>, h: AllIn(src, bs)) -> SN.InSpan(SV.lin(ls, src), bs):
  match ls src:
    case Con{+l, +lt} Con{+e, +et}:
      (h1, h2) = h
      SN.in_comb(l, e, SV.lin(lt, et), bs, h1, in_lin(lt, et, bs, h2))
    case Nil{} src:
      SN.in_zero(bs)
    case Con{+l, +lt} Nil{}:
      SN.in_zero(bs)

# spans compose: in the span of bs, each in the span of full
def in_back(+e: E.QExpr, +bs: List<&2, E.QExpr>, +full: List<&2, E.QExpr>, +h: SN.InSpan(e, bs), ha: AllIn(bs, full)) -> SN.InSpan(e, full):
  PP.in_tr(SV.lin(SN.in_ls(e, bs, h), bs), e, full, in_lin(SN.in_ls(e, bs, h), bs, full, ha), SN.in_ident(e, bs, h))

def lin_dlin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>) -> {SV.lin(ls, es) == DR.dlin(ls, es) : E.QExpr}:
  match ls es:
    case Con{+l, lt} Con{+e, et}:
      Equal.cong(E.QExpr, E.QExpr, r => E.QAdd{E.QMul{E.QCst{l}, e}, r}, SV.lin(lt, et), DR.dlin(lt, et), lin_dlin(lt, et))
    case Nil{} es:
      {==}
    case Con{l, lt} Nil{}:
      {==}

def same_of(+e: E.QExpr, +ls: List<&2, S.Q>, +ctx: List<&2, E.QExpr>, i: SV.Ident(e, SV.lin(ls, ctx))) -> DR.Same(e, DR.dlin(ls, ctx)):
  %lin_dlin(ls, ctx) : DR.Same(e, _)
  i

def dr_of_in(+e: E.QExpr, +ctx: List<&2, E.QExpr>, +h: SN.InSpan(e, ctx)) -> DR.InSpan(e, ctx):
  (SN.in_ls(e, ctx, h), same_of(e, SN.in_ls(e, ctx, h), ctx, SN.in_ident(e, ctx, h)))

def coll_sound.go(cs: DC.SP, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +s: Nat, hi: SPInv(cs), +ha: AllIn(sp.bs(cs), ctx), +h: {DC.coll(es, cs, s) == True{} : Bool})
  -> DR.Collapsed(es, ctx, s):
  match cs:
    case DC.SP{+rows, +bs}:
      (+hr, +hl) = hi
      (dr_of_in(SK.VE.x(DR.zseg(es, s)), ctx, in_back(SK.VE.x(DR.zseg(es, s)), bs, ctx,
         SN.in_of_zero(bs, rows, SK.VE.x(DR.zseg(es, s)), hr, LP2.band_l(DC.sp.inb(DC.SP{rows, bs}, SK.VE.x(DR.zseg(es, s))), DC.sp.inb(DC.SP{rows, bs}, SK.VE.y(DR.zseg(es, s))), h)), ha)),
       dr_of_in(SK.VE.y(DR.zseg(es, s)), ctx, in_back(SK.VE.y(DR.zseg(es, s)), bs, ctx,
         SN.in_of_zero(bs, rows, SK.VE.y(DR.zseg(es, s)), hr, LP2.band_r(DC.sp.inb(DC.SP{rows, bs}, SK.VE.x(DR.zseg(es, s))), DC.sp.inb(DC.SP{rows, bs}, SK.VE.y(DR.zseg(es, s))), h)), ha)))

# a segment the closure finds collapsed is collapsed in the context
def coll_sound(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +s: Nat, h: {DC.coll(es, cspan(ctx), s) == True{} : Bool}) -> DR.Collapsed(es, ctx, s):
  coll_sound.go(cspan(ctx), es, ctx, s, sp_of_inv(ctx, DC.SP{Nil{}, Nil{}}, sp0_inv()), sp_back_of(ctx, DC.SP{Nil{}, Nil{}}, ctx, Unit{}, all_self(ctx)), h)
