# bend-cad: a complex line's K fact is new (PLAN-sk13b B3, termination).
# The complex-line check (lib/dclose.bend's cl.go) walks a free root's
# kept non-K generators D in order. When i g_d closes a line, the line is
# x = g_d - (a combination of the earlier ones). cl.k gives K the real
# part of x when K lacks it, and else the imaginary part, which K lacks
# too: were both in K, x's encoding would lie in the span of K squared's
# part of the hull (khull spans each K generator k as (k, 0) and (0, k)),
# so g_d's encoding would lie in the span of K squared's and the earlier
# ones', and the hull kept g_d because it did not (clxs_n). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qnorm.bend as QN
import ./karith.bend as KA
import ./listpf.bend as LP2
import ./identpf.bend as ID
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./cwpf.bend as CW
import ./indset.bend as IS
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./pair.bend as PT
import ./spanpf.bend as SN
import ./seppf.bend as SP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcbasepf.bend as BS
import ./dckslpf.bend as KL

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Lists
# -----

def qcat_nil(A: List<&2, E.QExpr>) -> {DC.qcat(A, Nil{}) == A : List<&2, E.QExpr>}:
  match A:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(List<&2, E.QExpr>, DC.qcat(t, Nil{}), t, qcat_nil(t)) : {Con{a, _} == Con{a, t} : List<&2, E.QExpr>}
      {==}

def qcat_snoc(A: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +e: E.QExpr) -> {DC.qcat(A, EP.qsnoc(B, e)) == EP.qsnoc(DC.qcat(A, B), e) : List<&2, E.QExpr>}:
  match A:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(List<&2, E.QExpr>, DC.qcat(t, EP.qsnoc(B, e)), EP.qsnoc(DC.qcat(t, B), e), qcat_snoc(t, B, e)) : {Con{a, _} == Con{a, EP.qsnoc(DC.qcat(t, B), e)} : List<&2, E.QExpr>}
      {==}

def lin_tcat(ls: List<&2, S.Q>, A: List<&2, E.QExpr>, +C: List<&2, E.QExpr>) -> {SV.lin(SN.ltrunc(ls, A), DC.qcat(A, C)) == SV.lin(SN.ltrunc(ls, A), A) : E.QExpr}:
  match ls A:
    case Con{+l, +lt} Con{+a, +at}:
      %Equal.sym(E.QExpr, SV.lin(SN.ltrunc(lt, at), DC.qcat(at, C)), SV.lin(SN.ltrunc(lt, at), at), lin_tcat(lt, at, C)) : {E.QAdd{E.QMul{E.QCst{l}, a}, _} == E.QAdd{E.QMul{E.QCst{l}, a}, SV.lin(SN.ltrunc(lt, at), at)} : E.QExpr}
      {==}
    case Nil{} A:
      {==}
    case Con{l, lt} Nil{}:
      {==}

def in_catl.mk(+A: List<&2, E.QExpr>, +C: List<&2, E.QExpr>, +e: E.QExpr, +ls: List<&2, S.Q>, q: {QN.qzero(E.QSub{e, SV.lin(ls, A)}) == True{} : Bool})
  -> {QN.qzero(E.QSub{e, SV.lin(SN.ltrunc(ls, A), DC.qcat(A, C))}) == True{} : Bool}:
  %Equal.sym(E.QExpr, SV.lin(SN.ltrunc(ls, A), DC.qcat(A, C)), SV.lin(SN.ltrunc(ls, A), A), lin_tcat(ls, A, C)) : {QN.qzero(E.QSub{e, _}) == True{} : Bool}
  %Equal.sym(E.QExpr, SV.lin(SN.ltrunc(ls, A), A), SV.lin(ls, A), SN.lin_trunc(ls, A)) : {QN.qzero(E.QSub{e, _}) == True{} : Bool}
  q

# a span grows at the back
def in_catl(+A: List<&2, E.QExpr>, +C: List<&2, E.QExpr>, +e: E.QExpr, +h: SN.InSpan(e, A)) -> SN.InSpan(e, DC.qcat(A, C)):
  (SN.ltrunc(SN.in_ls(e, A, h), A), in_catl.mk(A, C, e, SN.in_ls(e, A, h), SN.in_qz(e, A, h)))

def dcat_snoc(xs: List<&2, DR.Der>, +x: DR.Der, +ys: List<&2, DR.Der>) -> {DC.dcat(KS.dsnoc(xs, x), ys) == DC.dcat(xs, Con{x, ys}) : List<&2, DR.Der>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, DR.Der>, DC.dcat(KS.dsnoc(t, x), ys), DC.dcat(t, Con{x, ys}), dcat_snoc(t, x, ys)) : {Con{h, _} == Con{h, DC.dcat(t, Con{x, ys})} : List<&2, DR.Der>}
      {==}

def dcat_nil(xs: List<&2, DR.Der>) -> {DC.dcat(xs, Nil{}) == xs : List<&2, DR.Der>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, DR.Der>, DC.dcat(t, Nil{}), t, dcat_nil(t)) : {Con{h, _} == Con{h, t} : List<&2, DR.Der>}
      {==}

def ddrop_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>) -> {DC.ddrop(DC.dlen(xs), DC.dcat(xs, ys)) == ys : List<&2, DR.Der>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      ddrop_cat(t, ys)

def encs_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat)
  -> {HS.encs(HS.hxs(es, fs, DC.dcat(xs, ys)), t) == DC.qcat(HS.encs(HS.hxs(es, fs, xs), t), HS.encs(HS.hxs(es, fs, ys), t)) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, DC.dcat(tl, ys)), t), DC.qcat(HS.encs(HS.hxs(es, fs, tl), t), HS.encs(HS.hxs(es, fs, ys), t)), encs_cat(tl, ys, es, fs, t)) : {Con{HS.enc(DR.Jd.x(DR.concl(es, fs, h)), t), _} == Con{HS.enc(DR.Jd.x(DR.concl(es, fs, h)), t), DC.qcat(HS.encs(HS.hxs(es, fs, tl), t), HS.encs(HS.hxs(es, fs, ys), t))} : List<&2, E.QExpr>}
      {==}

# What a hull fold keeps
# ----------------------

def kbit(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +g: DR.Der) -> Bool:
  SV.bnot(EP.isnil(EP.resp(EL.resid(HS.hs.rows(h), HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))))

# the generators a fold keeps, in order
def hkept(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS) -> List<&2, DR.Der>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+g, tl}:
      DC.dpick(kbit(es, fs, t, h, g), g, hkept(tl, es, fs, t, HS.hs.add(es, fs, t, h, g)))

def hk_ds.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +rr: EL.Res, +g: DR.Der, +K: List<&2, DR.Der>)
  -> {DC.dcat(HS.hs.ds(HS.hs.pick(b, rows, ds, rr, g)), K) == DC.dcat(ds, DC.dpick(SV.bnot(b), g, K)) : List<&2, DR.Der>}:
  match b:
    case True{}:
      {==}
    case False{}:
      dcat_snoc(ds, g, K)

def hk_ds.step(h: HS.HS, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +K: List<&2, DR.Der>)
  -> {DC.dcat(HS.hs.ds(HS.hs.add(es, fs, t, h, g)), K) == DC.dcat(HS.hs.ds(h), DC.dpick(kbit(es, fs, t, h, g), g, K)) : List<&2, DR.Der>}:
  match h:
    case HS.HS{+rows, +ds}:
      hk_ds.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g, K)

# a fold's generators are its start's and the ones it kept
def hfold_ds(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS)
  -> {HS.hs.ds(DC.hfold(gs, es, fs, t, h)) == DC.dcat(HS.hs.ds(h), hkept(gs, es, fs, t, h)) : List<&2, DR.Der>}:
  match gs:
    case Nil{}:
      Equal.sym(List<&2, DR.Der>, DC.dcat(HS.hs.ds(h), Nil{}), HS.hs.ds(h), dcat_nil(HS.hs.ds(h)))
    case Con{+g, +tl}:
      Equal.trans(List<&2, DR.Der>, HS.hs.ds(DC.hfold(tl, es, fs, t, HS.hs.add(es, fs, t, h, g))), DC.dcat(HS.hs.ds(HS.hs.add(es, fs, t, h, g)), hkept(tl, es, fs, t, HS.hs.add(es, fs, t, h, g))),
        DC.dcat(HS.hs.ds(h), DC.dpick(kbit(es, fs, t, h, g), g, hkept(tl, es, fs, t, HS.hs.add(es, fs, t, h, g)))),
        hfold_ds(tl, es, fs, t, HS.hs.add(es, fs, t, h, g)), hk_ds.step(h, g, es, fs, t, hkept(tl, es, fs, t, HS.hs.add(es, fs, t, h, g))))

def hk_ind.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +g: DR.Der, +tl: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))) : Bool},
  ih: {IS.indset(HS.encs(HS.hxs(es, fs, hkept(tl, es, fs, t, HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g))), t), HS.hs.rows(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g))) == True{} : Bool})
  -> {IS.indset(HS.encs(HS.hxs(es, fs, DC.dpick(SV.bnot(b), g, hkept(tl, es, fs, t, HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g)))), t), rows) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %eb : {SV.band(SV.bnot(_), IS.indset(HS.encs(HS.hxs(es, fs, hkept(tl, es, fs, t, HS.hs.pick(False{}, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g))), t), EL.rsnoc(rows, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))))) == True{} : Bool}
      ih

def hk_ind.step(h: HS.HS, +g: DR.Der, +tl: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat,
  ih: {IS.indset(HS.encs(HS.hxs(es, fs, hkept(tl, es, fs, t, HS.hs.add(es, fs, t, h, g))), t), HS.hs.rows(HS.hs.add(es, fs, t, h, g))) == True{} : Bool})
  -> {IS.indset(HS.encs(HS.hxs(es, fs, hkept(Con{g, tl}, es, fs, t, h)), t), HS.hs.rows(h)) == True{} : Bool}:
  match h:
    case HS.HS{+rows, +ds}:
      hk_ind.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), rows, ds, g, tl, es, fs, t, {==}, ih)

# the kept generators pass indset after the start's rows
def hk_ind(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS) -> {IS.indset(HS.encs(HS.hxs(es, fs, hkept(gs, es, fs, t, h)), t), HS.hs.rows(h)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +tl}:
      hk_ind.step(h, g, tl, es, fs, t, hk_ind(tl, es, fs, t, HS.hs.add(es, fs, t, h, g)))

# The hull's rows describe its kept generators
# --------------------------------------------

def HR(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS) -> Data:
  SK.Both({EP.rinv(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h), 0n) == True{} : Bool}, {EL.rlen(HS.hs.rows(h)) == SV.neqs(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)) : Nat})

def hadd_hr.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))) : Bool}, +h: HR(es, fs, t, HS.HS{rows, ds}))
  -> HR(es, fs, t, HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g)):
  match b:
    case True{}:
      h
    case False{}:
      (+hr, +hl) = h
      (HP.hs_add.rinv(es, fs, t, rows, ds, g, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), eb)), HP.hs_add.len(es, fs, t, rows, ds, g, EL.row_of(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t))), hl))

def hadd_hr(h: HS.HS, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +hh: HR(es, fs, t, h)) -> HR(es, fs, t, HS.hs.add(es, fs, t, h, g)):
  match h:
    case HS.HS{+rows, +ds}:
      hadd_hr.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), rows, ds, g, es, fs, t, {==}, hh)

def hfold_hr(gs: List<&2, DR.Der>, +h: HS.HS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +hh: HR(es, fs, t, h)) -> HR(es, fs, t, DC.hfold(gs, es, fs, t, h)):
  match gs:
    case Nil{}:
      hh
    case Con{+g, +tl}:
      hfold_hr(tl, HS.hs.add(es, fs, t, h, g), es, fs, t, hadd_hr(h, g, es, fs, t, hh))

def hadd_in.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))) : Bool}, +h: HR(es, fs, t, HS.HS{rows, ds}))
  -> SN.InSpan(HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(HS.hs.pick(b, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), g))), t)):
  match b:
    case True{}:
      (+hr, hl) = h
      SN.in_of_zero(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), hr, Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), eb))
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(ds, g)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)), HP.encs_snoc(es, fs, t, ds, g))
        : SN.InSpan(HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), _)
      SN.in_last(HS.encs(HS.hxs(es, fs, ds), t), HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t))

# a generator added is in the hull's span after
def hadd_in(h: HS.HS, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +hh: HR(es, fs, t, h))
  -> SN.InSpan(HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(HS.hs.add(es, fs, t, h, g))), t)):
  match h:
    case HS.HS{+rows, +ds}:
      hadd_in.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t)))), rows, ds, g, es, fs, t, {==}, hh)

# a fold's span holds its start's
def hfold_mono(+gs: List<&2, DR.Der>, +h: HS.HS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +e: E.QExpr, +hi: SN.InSpan(e, HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)))
  -> SN.InSpan(e, HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(gs, es, fs, t, h))), t)):
  %Equal.sym(List<&2, DR.Der>, HS.hs.ds(DC.hfold(gs, es, fs, t, h)), DC.dcat(HS.hs.ds(h), hkept(gs, es, fs, t, h)), hfold_ds(gs, es, fs, t, h)) : SN.InSpan(e, HS.encs(HS.hxs(es, fs, _), t))
  %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, DC.dcat(HS.hs.ds(h), hkept(gs, es, fs, t, h))), t), DC.qcat(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.encs(HS.hxs(es, fs, hkept(gs, es, fs, t, h)), t)),
      encs_cat(HS.hs.ds(h), hkept(gs, es, fs, t, h), es, fs, t)) : SN.InSpan(e, _)
  in_catl(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.encs(HS.hxs(es, fs, hkept(gs, es, fs, t, h)), t), e, hi)

def AllInE(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +B: List<&2, E.QExpr>) -> Data:
  match gs:
    case Nil{}:
      Unit
    case Con{+g, tl}:
      SK.Both(SN.InSpan(HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), B), AllInE(tl, es, fs, t, B))

def alline_mono(+gs: List<&2, DR.Der>, +h: HS.HS, +ks: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, hg: AllInE(ks, es, fs, t, HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)))
  -> AllInE(ks, es, fs, t, HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(gs, es, fs, t, h))), t)):
  match ks:
    case Nil{}:
      Unit{}
    case Con{+g, +tl}:
      (a, b) = hg
      (hfold_mono(gs, h, es, fs, t, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), a), alline_mono(gs, h, tl, es, fs, t, b))

# a fold's span holds everything it was given
def hfold_in(gs: List<&2, DR.Der>, +h: HS.HS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +hh: HR(es, fs, t, h))
  -> AllInE(gs, es, fs, t, HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(gs, es, fs, t, h))), t)):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +tl}:
      (hfold_mono(tl, HS.hs.add(es, fs, t, h, g), es, fs, t, HS.enc(DR.Jd.x(DR.concl(es, fs, g)), t), hadd_in(h, g, es, fs, t, hh)),
       hfold_in(tl, HS.hs.add(es, fs, t, h, g), es, fs, t, hadd_hr(h, g, es, fs, t, hh)))

# K squared in the hull
# ---------------------

def tks(xs: List<&2, E.QExpr>, +t: Nat) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, tl}:
      Con{E.QMul{E.QVar{t}, x}, tks(tl, t)}

def kre.id(+p: List<&2, S.Q>, +k: E.QExpr, +z: SK.VE, +t: Nat) -> S.Q.eq(E.qeval(p, k), E.qeval(p, HS.enc(SK.VE.add(DR.vlin(DR.qz(), z, DR.qz(), z), SK.VE{k, DR.zeroe()}), t))):
  QR.qring_eq([E.qeval(p, k), E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z)), E.qlookup(p, t)], E.QVar{0n},
    E.QAdd{E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, E.QVar{0n}},
      E.QMul{E.QVar{3n}, E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}, E.QCst{DR.qz()}}}}, {==})

def kim.id(+p: List<&2, S.Q>, +k: E.QExpr, +z: SK.VE, +t: Nat) -> S.Q.eq(E.qeval(p, E.QMul{E.QVar{t}, k}), E.qeval(p, HS.enc(SK.VE.add(DR.vlin(DR.qz(), z, DR.qz(), z), SK.VE{DR.zeroe(), k}), t))):
  QR.qring_eq([E.qeval(p, k), E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z)), E.qlookup(p, t)], E.QMul{E.QVar{3n}, E.QVar{0n}},
    E.QAdd{E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, E.QCst{DR.qz()}},
      E.QMul{E.QVar{3n}, E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}, E.QVar{0n}}}}, {==})

def kb_of.go(+k: E.QExpr, +ks: List<&2, E.QExpr>, +tk: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +t: Nat, +h1: SN.InSpan(k, B), +h2: SN.InSpan(E.QMul{E.QVar{t}, k}, B), r: SK.Both(KL.AllIn(ks, B), KL.AllIn(tk, B)))
  -> SK.Both(KL.AllIn(Con{k, ks}, B), KL.AllIn(Con{E.QMul{E.QVar{t}, k}, tk}, B)):
  (a, b) = r
  ((h1, a), (h2, b))

# K squared's generators give each K generator k as (k, 0) and (0, k)
def kb_of(ds: List<&2, DR.Der>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +B: List<&2, E.QExpr>, h: AllInE(DC.kgens(r, ds), es, fs, t, B))
  -> SK.Both(KL.AllIn(KS.kexprs(es, fs, ds), B), KL.AllIn(tks(KS.kexprs(es, fs, ds), t), B)):
  match ds:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+d, +tl}:
      (h1, r1) = h
      (h2, r2) = r1
      kb_of.go(DR.Jd.e(DR.concl(es, fs, d)), KS.kexprs(es, fs, tl), tks(KS.kexprs(es, fs, tl), t), B, t,
        BS.in_id(HS.enc(SK.VE.add(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), SK.VE{DR.Jd.e(DR.concl(es, fs, d)), DR.zeroe()}), t), DR.Jd.e(DR.concl(es, fs, d)), B, h1,
          p => kre.id(p, DR.Jd.e(DR.concl(es, fs, d)), DR.zdir(es, r), t)),
        BS.in_id(HS.enc(SK.VE.add(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), SK.VE{DR.zeroe(), DR.Jd.e(DR.concl(es, fs, d))}), t), E.QMul{E.QVar{t}, DR.Jd.e(DR.concl(es, fs, d))}, B, h2,
          p => kim.id(p, DR.Jd.e(DR.concl(es, fs, d)), DR.zdir(es, r), t)),
        kb_of(tl, r, es, fs, t, B, r2))

# A line with both parts in K
# ---------------------------

def in_lin_sub(ls: List<&2, S.Q>, A: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, h: KL.AllIn(A, B)) -> SN.InSpan(SV.lin(ls, A), B):
  match ls A:
    case Con{+l, +lt} Con{+a, +at}:
      (ha, ht) = h
      SN.in_comb(l, a, SV.lin(lt, at), B, ha, in_lin_sub(lt, at, B, ht))
    case Nil{} A:
      SN.in_zero(B)
    case Con{l, lt} Nil{}:
      SN.in_zero(B)

def tlin.step(+tv: S.Q, +l: S.Q, +a: S.Q, +L: S.Q, +L2: S.Q, ih: S.Q.eq(S.Q.mul(tv, L), L2))
  -> S.Q.eq(S.Q.mul(tv, S.Q.add(S.Q.mul(l, a), L)), S.Q.add(S.Q.mul(l, S.Q.mul(tv, a)), L2)):
  LQ.q_trans(S.Q.mul(tv, S.Q.add(S.Q.mul(l, a), L)), S.Q.add(S.Q.mul(l, S.Q.mul(tv, a)), S.Q.mul(tv, L)), S.Q.add(S.Q.mul(l, S.Q.mul(tv, a)), L2),
    QR.qring_eq([tv, l, a, L], E.QMul{E.QVar{0n}, E.QAdd{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QVar{3n}}}, E.QAdd{E.QMul{E.QVar{1n}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, E.QMul{E.QVar{0n}, E.QVar{3n}}}, {==}),
    LQ.q_add_cong_r(S.Q.mul(l, S.Q.mul(tv, a)), S.Q.mul(tv, L), L2, ih))

def tlin.zero(+tv: S.Q) -> S.Q.eq(S.Q.mul(tv, S.Q{S.Z0{}, S.XH{}}), S.Q{S.Z0{}, S.XH{}}):
  QR.qring_eq([tv], E.QMul{E.QVar{0n}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, {==})

# t times a combination is the combination of t times each
def tlin(+p: List<&2, S.Q>, ls: List<&2, S.Q>, A: List<&2, E.QExpr>, +t: Nat) -> S.Q.eq(E.qeval(p, E.QMul{E.QVar{t}, SV.lin(ls, A)}), E.qeval(p, SV.lin(ls, tks(A, t)))):
  match ls A:
    case Con{+l, +lt} Con{+a, +at}:
      tlin.step(E.qlookup(p, t), l, E.qeval(p, a), E.qeval(p, SV.lin(lt, at)), E.qeval(p, SV.lin(lt, tks(at, t))), tlin(p, lt, at, t))
    case Nil{} A:
      tlin.zero(E.qlookup(p, t))
    case Con{l, lt} Nil{}:
      tlin.zero(E.qlookup(p, t))

def tb.at(+p: List<&2, S.Q>, +b: E.QExpr, +ls: List<&2, S.Q>, +A: List<&2, E.QExpr>, +t: Nat, +q: VD.SameD(b, SV.lin(ls, A)))
  -> S.Q.eq(E.qeval(p, E.QMul{E.QVar{t}, b}), E.qeval(p, SV.lin(ls, tks(A, t)))):
  LQ.q_trans(E.qeval(p, E.QMul{E.QVar{t}, b}), E.qeval(p, E.QMul{E.QVar{t}, SV.lin(ls, A)}), E.qeval(p, SV.lin(ls, tks(A, t))),
    LQ.q_mul_cong_r(E.qlookup(p, t), E.qeval(p, b), E.qeval(p, SV.lin(ls, A)), ID.ident_ok(b, SV.lin(ls, A), q)(p)), tlin(p, ls, A, t))

def in_t.go(+b: E.QExpr, +A: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +t: Nat, +ls: List<&2, S.Q>, +q: VD.SameD(b, SV.lin(ls, A)), htA: KL.AllIn(tks(A, t), B))
  -> SN.InSpan(E.QMul{E.QVar{t}, b}, B):
  BS.in_id(SV.lin(ls, tks(A, t)), E.QMul{E.QVar{t}, b}, B, in_lin_sub(ls, tks(A, t), B, htA), p => tb.at(p, b, ls, A, t, q))

# A's span inside B's, and t A's, take a and t b into B's span
def enc_in(+a: E.QExpr, +b: E.QExpr, +A: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +t: Nat, +ha: SN.InSpan(a, A), +hb: SN.InSpan(b, A), hA: KL.AllIn(A, B), htA: KL.AllIn(tks(A, t), B))
  -> SN.InSpan(SP.tag(a, b, t), B):
  BS.in_add(a, E.QMul{E.QVar{t}, b}, B,
    BS.in_tr(SV.lin(SN.in_ls(a, A, ha), A), a, B, in_lin_sub(SN.in_ls(a, A, ha), A, B, hA), SN.in_qz(a, A, ha)),
    in_t.go(b, A, B, t, SN.in_ls(b, A, hb), SN.in_qz(b, A, hb), htA))

def lsym.at(+p: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: SV.Ident(e1, e2)) -> S.Q.eq(E.qeval(p, e2), E.qeval(p, e1)):
  LQ.q_sym(E.qeval(p, e1), E.qeval(p, e2), h(p))

def pch_in.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +ls: List<&2, S.Q>, +prev: List<&2, DR.Der>)
  -> S.Q.eq(E.qeval(p, HS.enc(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, prev))), t)), E.qeval(p, SV.lin(ls, HS.encs(HS.hxs(es, fs, prev), t)))):
  LQ.q_trans(E.qeval(p, HS.enc(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, prev))), t)), E.qeval(p, HS.enc(HS.clin(es, r, ls, HS.hxs(es, fs, prev)), t)), E.qeval(p, SV.lin(ls, HS.encs(HS.hxs(es, fs, prev), t))),
    HP.enc_cong.at(p, DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, prev))), HS.clin(es, r, ls, HS.hxs(es, fs, prev)), t, HP.pchain_x(es, fs, r, ls, prev)),
    lsym.at(p, SV.lin(ls, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(HS.clin(es, r, ls, HS.hxs(es, fs, prev)), t), HP.enc_lin(es, r, t, ls, HS.hxs(es, fs, prev))))

# a chain over the earlier generators is in their span
def pch_in(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +t: Nat, +ls: List<&2, S.Q>, +prev: List<&2, DR.Der>)
  -> SN.InSpan(HS.enc(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, prev))), t), HS.encs(HS.hxs(es, fs, prev), t)):
  (ls, ID.qzero_ident(HS.enc(DR.Jd.x(DR.concl(es, fs, HS.pchain(r, ls, prev))), t), SV.lin(ls, HS.encs(HS.hxs(es, fs, prev), t)), p => pch_in.at(p, es, fs, r, t, ls, prev)))

# g = (g - c) + c
def split.id(+p: List<&2, S.Q>, +fd: SK.VE, +fp: SK.VE, +t: Nat)
  -> S.Q.eq(E.qeval(p, HS.enc(fd, t)), E.qeval(p, E.QAdd{HS.enc(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp), t), HS.enc(fp, t)})):
  QR.qring_eq([E.qeval(p, SK.VE.x(fd)), E.qeval(p, SK.VE.y(fd)), E.qeval(p, SK.VE.x(fp)), E.qeval(p, SK.VE.y(fp)), E.qlookup(p, t)],
    E.QAdd{E.QVar{0n}, E.QMul{E.QVar{4n}, E.QVar{1n}}},
    E.QAdd{E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{S.Q.neg(DR.qo())}, E.QVar{2n}}}, E.QMul{E.QVar{4n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}, E.QMul{E.QCst{S.Q.neg(DR.qo())}, E.QVar{3n}}}}},
      E.QAdd{E.QVar{2n}, E.QMul{E.QVar{4n}, E.QVar{3n}}}}, {==})

# both parts of the line in K: g's encoding in the span of K squared's and
# the earlier ones', against its nonzero residual
def found_contra(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +fd: SK.VE, +fp: SK.VE, +Bk: List<&2, E.QExpr>, +P: List<&2, E.QExpr>, +rc: List<&2, EL.Row>,
  hx: {KS.ks.inb(k, SK.VE.x(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) == True{} : Bool}, hy: {KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) == True{} : Bool},
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), 0n) == True{} : Bool}, hA: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), Bk), htA: KL.AllIn(tks(KS.kexprs(es, fs, KS.ks.ds(k)), t), Bk),
  hp: SN.InSpan(HS.enc(fp, t), P), hn: {EP.isnil(EP.resp(EL.resid(rc, HS.enc(fd, t)))) == False{} : Bool},
  +hr: {EP.rinv(DC.qcat(Bk, P), rc, 0n) == True{} : Bool}, +hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, P)) : Nat}) -> Empty:
  KA.tf(Equal.trans(Bool, True{}, EP.isnil(EP.resp(EL.resid(rc, HS.enc(fd, t)))), False{},
    Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rc, HS.enc(fd, t)))), True{},
      SN.zero_of_in(DC.qcat(Bk, P), rc, HS.enc(fd, t), hr, hl,
        BS.in_id(E.QAdd{HS.enc(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp), t), HS.enc(fp, t)}, HS.enc(fd, t), DC.qcat(Bk, P),
          BS.in_add(HS.enc(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp), t), HS.enc(fp, t), DC.qcat(Bk, P),
            in_catl(Bk, P, HS.enc(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp), t),
              enc_in(SK.VE.x(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp)), SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp)), KS.kexprs(es, fs, KS.ks.ds(k)), Bk, t,
                SN.in_of_zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), SK.VE.x(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp)), hkr, hx),
                SN.in_of_zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp)), hkr, hy), hA, htA)),
            BS.in_catr(Bk, P, HS.enc(fp, t), hp)),
          p => split.id(p, fd, fp, t)))),
    hn))

# The walk
# --------

# a new K fact, if any, is not in K
def OptN(+k: KS.KS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, m: Maybe<&2, DR.Der>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{+d}:
      {KS.ks.inb(k, DR.Jd.e(DR.concl(es, fs, d))) == False{} : Bool}

def bnot_t(b: Bool, h: {SV.bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

def clk_n.y(c: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +fd: SK.VE, +fp: SK.VE, +Bk: List<&2, E.QExpr>, +P: List<&2, E.QExpr>, +rc: List<&2, EL.Row>,
  ec: {c == KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) : Bool}, hx: {KS.ks.inb(k, SK.VE.x(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) == True{} : Bool},
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), 0n) == True{} : Bool}, hA: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), Bk), htA: KL.AllIn(tks(KS.kexprs(es, fs, KS.ks.ds(k)), t), Bk),
  hp: SN.InSpan(HS.enc(fp, t), P), hn: {EP.isnil(EP.resp(EL.resid(rc, HS.enc(fd, t)))) == False{} : Bool},
  +hr: {EP.rinv(DC.qcat(Bk, P), rc, 0n) == True{} : Bool}, +hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, P)) : Nat})
  -> {KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) == False{} : Bool}:
  match c:
    case True{}:
      absurd({KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))) == False{} : Bool}, found_contra(es, fs, t, k, fd, fp, Bk, P, rc, hx, Equal.sym(Bool, True{}, KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))), ec),
        hkr, hA, htA, hp, hn, hr, hl))
    case False{}:
      Equal.sym(Bool, False{}, KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), fd, S.Q.neg(DR.qo()), fp))), ec)

# the part cl.k gives K is not in K
def clk_n(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +r: DR.Node, +d: DR.Der, +lsI: List<&2, S.Q>, +prev: List<&2, DR.Der>, +d2: DR.Der,
  +Bk: List<&2, E.QExpr>, +rc: List<&2, EL.Row>,
  eb: {b == KS.ks.inb(k, SK.VE.x(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev)))))) : Bool},
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), 0n) == True{} : Bool}, hA: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), Bk), htA: KL.AllIn(tks(KS.kexprs(es, fs, KS.ks.ds(k)), t), Bk),
  hn: {EP.isnil(EP.resp(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) == False{} : Bool},
  +hr: {EP.rinv(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), rc, 0n) == True{} : Bool}, +hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat})
  -> OptN(k, es, fs, Some{DC.cl.k(b, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)}, d2)}):
  match b:
    case True{}:
      clk_n.y(KS.ks.inb(k, SK.VE.y(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev)))))), es, fs, t, k,
        DR.Jd.x(DR.concl(es, fs, d)), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev))), Bk, HS.encs(HS.hxs(es, fs, prev), t), rc, {==},
        Equal.sym(Bool, True{}, KS.ks.inb(k, SK.VE.x(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev)))))), eb),
        hkr, hA, htA, pch_in(es, fs, r, t, lsI, prev), hn, hr, hl)
    case False{}:
      Equal.sym(Bool, False{}, KS.ks.inb(k, SK.VE.x(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev)))))), eb)

def clp_n(b: Bool, +found: DR.Der, +k: KS.KS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hf: OptN(k, es, fs, Some{found}), +rest: Maybe<&2, DR.Der>, hr: OptN(k, es, fs, rest))
  -> OptN(k, es, fs, DC.cl.pick(b, found, rest)):
  match b:
    case True{}:
      hf
    case False{}:
      hr

def bc_snoc(+Bk: List<&2, E.QExpr>, +prev: List<&2, DR.Der>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat)
  -> {DC.qcat(Bk, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t)) == EP.qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t), EP.qsnoc(HS.encs(HS.hxs(es, fs, prev), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), HP.encs_snoc(es, fs, t, prev, d)) : {DC.qcat(Bk, _) == EP.qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)) : List<&2, E.QExpr>}
  qcat_snoc(Bk, HS.encs(HS.hxs(es, fs, prev), t), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))

def step_r(+Bk: List<&2, E.QExpr>, +prev: List<&2, DR.Der>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rc: List<&2, EL.Row>,
  +hr: {EP.rinv(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), rc, 0n) == True{} : Bool}, +hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat},
  +hn: {EP.isnil(EP.resp(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))) == False{} : Bool})
  -> {EP.rinv(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t)), EL.rsnoc(rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), 0n) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, DC.qcat(Bk, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t)), EP.qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), bc_snoc(Bk, prev, d, es, fs, t))
    : {EP.rinv(_, EL.rsnoc(rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), 0n) == True{} : Bool}
  EP.new_rinv(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t), hr, hl, hn)

def step_l(+Bk: List<&2, E.QExpr>, +prev: List<&2, DR.Der>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +rc: List<&2, EL.Row>, +x: EL.Row,
  hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat})
  -> {EL.rlen(EL.rsnoc(rc, x)) == SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t))) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, DC.qcat(Bk, HS.encs(HS.hxs(es, fs, KS.dsnoc(prev, d)), t)), EP.qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), bc_snoc(Bk, prev, d, es, fs, t))
    : {EL.rlen(EL.rsnoc(rc, x)) == SV.neqs(_) : Nat}
  %Equal.sym(Nat, SV.neqs(EP.qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))), 1n+SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))),
      CW.neqs_qsnoc(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))) : {EL.rlen(EL.rsnoc(rc, x)) == _ : Nat}
  %Equal.sym(Nat, EL.rlen(EL.rsnoc(rc, x)), 1n+EL.rlen(rc), CW.rlen_rsnoc(rc, x)) : {_ == 1n+SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat}
  %Equal.sym(Nat, EL.rlen(rc), SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))), hl) : {1n+_ == 1n+SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat}
  {==}

# the check walks the kept generators with K squared's and the earlier
# ones' rows rc beside its own
def clgo_n(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>,
  +Bk: List<&2, E.QExpr>, +rc: List<&2, EL.Row>, hi: {IS.indset(HS.encs(HS.hxs(es, fs, ds), t), rc) == True{} : Bool},
  +hr: {EP.rinv(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t)), rc, 0n) == True{} : Bool}, +hl: {EL.rlen(rc) == SV.neqs(DC.qcat(Bk, HS.encs(HS.hxs(es, fs, prev), t))) : Nat},
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), 0n) == True{} : Bool}, +hA: KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(k)), Bk), +htA: KL.AllIn(tks(KS.kexprs(es, fs, KS.ks.ds(k)), t), Bk))
  -> OptN(k, es, fs, DC.cl.go(ds, es, fs, t, r, h, k, rows2, bb, prev)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      +hi2 = hi
      +e = HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)
      +res = EL.resid(rows2, e)
      +lsI = PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)), DV.dropls(DV.rescb(res), DV.resbt(res), e, bb))
      +px = {DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)} : DR.Der}
      +hn = bnot_t(EP.isnil(EP.resp(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))),
        LP2.band_l(SV.bnot(EP.isnil(EP.resp(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))))), IS.indset(HS.encs(HS.hxs(es, fs, tl), t), EL.rsnoc(rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))))), hi2))
      clp_n(EP.isnil(EP.resp(res)), DC.cl.found(es, fs, t, r, h, k, d, res, e, bb, prev), k, es, fs,
        clk_n(KS.ks.inb(k, SK.VE.x(DR.Jd.x(DR.concl(es, fs, px)))), es, fs, t, k, r, d, lsI, prev, HS.hs.der(es, fs, t, r, h, DR.imul(DR.Jd.x(DR.concl(es, fs, px)))), Bk, rc, {==}, hkr, hA, htA, hn, hr, hl),
        DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d)),
        clgo_n(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(res)), EP.qsnoc(bb, e), KS.dsnoc(prev, d), Bk, EL.rsnoc(rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))),
          LP2.band_r(SV.bnot(EP.isnil(EP.resp(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))))), IS.indset(HS.encs(HS.hxs(es, fs, tl), t), EL.rsnoc(rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))))), hi2),
          step_r(Bk, prev, d, es, fs, t, rc, hr, hl, hn), step_l(Bk, prev, d, es, fs, t, rc, EL.row_of(EL.resid(rc, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t))), hl), hkr, hA, htA))

# The checks' new K facts
# -----------------------

def d0_eq(+gs: List<&2, DR.Der>, +h0: HS.HS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat)
  -> {DC.ddrop(DC.dlen(HS.hs.ds(h0)), HS.hs.ds(DC.hfold(gs, es, fs, t, h0))) == hkept(gs, es, fs, t, h0) : List<&2, DR.Der>}:
  %Equal.sym(List<&2, DR.Der>, HS.hs.ds(DC.hfold(gs, es, fs, t, h0)), DC.dcat(HS.hs.ds(h0), hkept(gs, es, fs, t, h0)), hfold_ds(gs, es, fs, t, h0)) : {DC.ddrop(DC.dlen(HS.hs.ds(h0)), _) == hkept(gs, es, fs, t, h0) : List<&2, DR.Der>}
  ddrop_cat(HS.hs.ds(h0), hkept(gs, es, fs, t, h0))

def hr0_r(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +hh: HR(es, fs, t, h))
  -> {EP.rinv(DC.qcat(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{}), HS.hs.rows(h), 0n) == True{} : Bool}:
  (a, b) = hh
  %Equal.sym(List<&2, E.QExpr>, DC.qcat(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{}), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), qcat_nil(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t))) : {EP.rinv(_, HS.hs.rows(h), 0n) == True{} : Bool}
  a

def hr0_l(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +hh: HR(es, fs, t, h))
  -> {EL.rlen(HS.hs.rows(h)) == SV.neqs(DC.qcat(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{})) : Nat}:
  (a, b) = hh
  %Equal.sym(List<&2, E.QExpr>, DC.qcat(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{}), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), qcat_nil(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t))) : {EL.rlen(HS.hs.rows(h)) == SV.neqs(_) : Nat}
  b

def clx_n.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: HS.HS, +ek: {hk == DC.khull(es, fs, t, DC.Sk.k(s), r) : HS.HS},
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool},
  kb: SK.Both(KL.AllIn(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), HS.encs(HS.hxs(es, fs, HS.hs.ds(hk)), t)), KL.AllIn(tks(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(hk)), t))),
  +hh: HR(es, fs, t, hk))
  -> OptN(DC.Sk.k(s), es, fs, DC.cl.go(DC.ddrop(DC.dlen(HS.hs.ds(hk)), HS.hs.ds(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk))), es, fs, t, r,
    DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk), DC.Sk.k(s), HS.hs.rows(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk)),
    HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk))), t), Nil{})):
  (hA, htA) = kb
  %Equal.sym(List<&2, DR.Der>, DC.ddrop(DC.dlen(HS.hs.ds(hk)), HS.hs.ds(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk))), hkept(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk),
      d0_eq(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), hk, es, fs, t))
    : OptN(DC.Sk.k(s), es, fs, DC.cl.go(_, es, fs, t, r, DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk), DC.Sk.k(s), HS.hs.rows(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk)),
      HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk))), t), Nil{}))
  clgo_n(hkept(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk), es, fs, t, r, DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk), DC.Sk.k(s),
    HS.hs.rows(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk)), HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.hfold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk))), t), Nil{},
    HS.encs(HS.hxs(es, fs, HS.hs.ds(hk)), t), HS.hs.rows(hk), hk_ind(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, hk), hr0_r(es, fs, t, hk, hh), hr0_l(es, fs, t, hk, hh), hkr, hA, htA)

# a complex line's K fact is not in K
def clx_n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool})
  -> OptN(DC.Sk.k(s), es, fs, DC.clx(es, fs, t, s, r)):
  clx_n.go(es, fs, t, s, r, DC.khull(es, fs, t, DC.Sk.k(s), r), {==}, hkr,
    kb_of(KS.ks.ds(DC.Sk.k(s)), r, es, fs, t, HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), t),
      hfold_in(DC.kgens(r, KS.ks.ds(DC.Sk.k(s))), HS.hs0(), es, fs, t, ({==}, {==}))),
    hfold_hr(DC.kgens(r, KS.ks.ds(DC.Sk.k(s))), HS.hs0(), es, fs, t, ({==}, {==})))

def clxs.pick_n(m: Maybe<&2, DR.Der>, +k: KS.KS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, hm: OptN(k, es, fs, m), +rest: Maybe<&2, DR.Der>, hr: OptN(k, es, fs, rest)) -> OptN(k, es, fs, DC.clxs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+d}:
      hm

def clxs.if_n(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool},
  +rest: Maybe<&2, DR.Der>, hr: OptN(DC.Sk.k(s), es, fs, rest)) -> OptN(DC.Sk.k(s), es, fs, DC.clxs.if(f, es, fs, t, s, r, rest)):
  match f:
    case True{}:
      clxs.pick_n(DC.clx(es, fs, t, s, r), DC.Sk.k(s), es, fs, clx_n(es, fs, t, s, r, hkr), rest, hr)
    case False{}:
      hr

# the complex-line check's K fact is new
def clxs_n(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool})
  -> OptN(DC.Sk.k(s), es, fs, DC.clxs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      clxs.if_n(SV.bnot(DC.node_eq(r, DR.NFrame{})), es, fs, t, s, r, hkr, DC.clxs(tl, es, fs, t, s), clxs_n(tl, es, fs, t, s, hkr))

def fbp_n(b: Bool, +g: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, eb: {b == SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))) : Bool},
  +rest: Maybe<&2, DR.Der>, hr: OptN(k, es, fs, rest)) -> OptN(k, es, fs, DC.mpick2(b, DR.DBack{g}, rest)):
  match b:
    case True{}:
      bnot_t(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))), Equal.sym(Bool, True{}, SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), eb))
    case False{}:
      hr

# frame-back's K fact is new
def fback_n(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> OptN(k, es, fs, DC.fback(gs, es, fs, k)):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +tl}:
      fbp_n(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), g, es, fs, k, {==}, DC.fback(tl, es, fs, k), fback_n(tl, es, fs, k))
