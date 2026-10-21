# bend-cad: the deletion filter gives a conflict's support (PLAN-sk13a S3),
# the spec's ConflictOk, given candidates that are kept, driving, before c,
# distinct, and with c refute. The support s is a sublist of them; c with
# s still refutes (the filter drops a member only when the rest does);
# without any one member m of s it does not: when m was tested, c with the
# kept and untested candidates but m had none, so refute found a point
# there (lib/satpf.bend), and that point is one for c with s but m, whose
# equations and sides are among those. Proofs only.
#
# Generated from tools/drafts/conflictpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./lqfield.bend as LQF
import ./indpf.bend as IP
import ./refute.bend as RF
import ./satpf.bend as ST
import ./conflict.bend as CO
import ./listpf.bend as LI
import ./lexpf.bend as LX

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Sublists
# --------

# xs is ys with some entries left out, in order
def SubN(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Data:
  match xs ys:
    case Nil{} ys:
      Unit
    case Con{x, xt} Nil{}:
      Empty
    case Con{+x, +xt} Con{y, yt}:
      Either<&2, &2, M.Both({x == y : Nat}, SubN(xt, yt)), SubN(Con{x, xt}, yt)>

def SubE(xs: List<&2, E.QExpr>, ys: List<&2, E.QExpr>) -> Data:
  match xs ys:
    case Nil{} ys:
      Unit
    case Con{x, xt} Nil{}:
      Empty
    case Con{+x, +xt} Con{y, yt}:
      Either<&2, &2, M.Both({x == y : E.QExpr}, SubE(xt, yt)), SubE(Con{x, xt}, yt)>

def SubS(xs: List<&2, SK.Side>, ys: List<&2, SK.Side>) -> Data:
  match xs ys:
    case Nil{} ys:
      Unit
    case Con{x, xt} Nil{}:
      Empty
    case Con{+x, +xt} Con{y, yt}:
      Either<&2, &2, M.Both({x == y : SK.Side}, SubS(xt, yt)), SubS(Con{x, xt}, yt)>

def subn_cons_r(xs: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, h: SubN(xs, ys)) -> SubN(xs, Con{y, ys}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +xt}:
      Inr{h}

def sube_cons_r(xs: List<&2, E.QExpr>, +y: E.QExpr, +ys: List<&2, E.QExpr>, h: SubE(xs, ys)) -> SubE(xs, Con{y, ys}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +xt}:
      Inr{h}

def subs_cons_r(xs: List<&2, SK.Side>, +y: SK.Side, +ys: List<&2, SK.Side>, h: SubS(xs, ys)) -> SubS(xs, Con{y, ys}):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +xt}:
      Inr{h}

def subs_refl(xs: List<&2, SK.Side>) -> SubS(xs, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +xt}:
      Inl{({==}, subs_refl(xt))}

# both sides lengthened by the same list
def subs_cats(+xs: List<&2, SK.Side>, ys: List<&2, SK.Side>, +zs: List<&2, SK.Side>, h: SubS(ys, zs)) -> SubS(SK.cats(xs, ys), SK.cats(xs, zs)):
  match xs:
    case Nil{}:
      h
    case Con{+x, +xt}:
      Inl{({==}, subs_cats(xt, ys, zs, h))}

# the larger side lengthened in front
def subs_cats_r(+ys: List<&2, SK.Side>, xs: List<&2, SK.Side>, +zs: List<&2, SK.Side>, h: SubS(ys, zs)) -> SubS(ys, SK.cats(xs, zs)):
  match xs:
    case Nil{}:
      h
    case Con{+x, +xt}:
      subs_cons_r(ys, x, SK.cats(xt, zs), subs_cats_r(ys, xt, zs, h))

# both lengthened behind by the same list
def subs_cats_l(xs: List<&2, SK.Side>, ys: List<&2, SK.Side>, +zs: List<&2, SK.Side>, h: SubS(xs, ys)) -> SubS(SK.cats(xs, zs), SK.cats(ys, zs)):
  match xs ys:
    case Nil{} ys:
      subs_cats_r(zs, ys, zs, subs_refl(zs))
    case Con{x, xt} Nil{}:
      absurd(SubS(SK.cats(Con{x, xt}, zs), zs), h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          Inl{(LX.both_l({x == y : SK.Side}, SubS(xt, yt), p), subs_cats_l(xt, yt, zs, LX.both_r({x == y : SK.Side}, SubS(xt, yt), p)))}
        case Inr{q}:
          Inr{subs_cats_l(Con{x, xt}, yt, zs, q)}

def mem_cons.go(b: Bool, +v: Nat, +x: Nat, +xt: List<&2, Nat>, +yt: List<&2, Nat>, hb: {b == SV.eq(v, x) : Bool}, hm: {SV.bor(SV.eq(v, x), SV.mem(v, xt)) == True{} : Bool},
  ih: {SV.mem(v, xt) == True{} : Bool} -> {SV.mem(v, yt) == True{} : Bool}) -> {SV.bor(SV.eq(v, x), SV.mem(v, yt)) == True{} : Bool}:
  match b:
    case True{}:
      LI.bor_l(SV.eq(v, x), SV.mem(v, yt), Equal.sym(Bool, True{}, SV.eq(v, x), hb))
    case False{}:
      LI.bor_r(SV.eq(v, x), SV.mem(v, yt), ih(LI.bor_rf(SV.eq(v, x), SV.mem(v, xt), hm, Equal.sym(Bool, False{}, SV.eq(v, x), hb))))

def mem_subn(+v: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>, h: SubN(xs, ys), hm: {SV.mem(v, xs) == True{} : Bool}) -> {SV.mem(v, ys) == True{} : Bool}:
  match xs ys:
    case Nil{} ys:
      absurd({SV.mem(v, ys) == True{} : Bool}, LI.mem_nil(v, hm))
    case Con{x, xt} Nil{}:
      absurd({SV.mem(v, Nil{}) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          %LX.both_l({x == y : Nat}, SubN(xt, yt), p) : {SV.mem(v, Con{_, yt}) == True{} : Bool}
          mem_cons.go(SV.eq(v, x), v, x, xt, yt, {==}, hm, a => mem_subn(v, xt, yt, LX.both_r({x == y : Nat}, SubN(xt, yt), p), a))
        case Inr{q}:
          LI.mem_tl(v, y, yt, mem_subn(v, Con{x, xt}, yt, q, hm))

# The filter
# ----------

def lcat_snoc(keep: List<&2, Nat>, +x: Nat, +R: List<&2, Nat>) -> {CO.lcat(CO.lsnoc(keep, x), R) == CO.lcat(keep, Con{x, R}) : List<&2, Nat>}:
  match keep:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %lcat_snoc(t, x, R) : {Con{h, CO.lcat(CO.lsnoc(t, x), R)} == Con{h, _} : List<&2, Nat>}
      {==}

def fs.c(b: Bool, +x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, ih: @k: List<&2, Nat> -> SubN(CO.filt(t, sk, c, k), t))
  -> SubN(CO.fcons(b, x, CO.filt(t, sk, c, CO.kpick(b, keep, x))), Con{x, t}):
  match b:
    case True{}:
      subn_cons_r(CO.filt(t, sk, c, keep), x, t, ih(keep))
    case False{}:
      Inl{({==}, ih(CO.lsnoc(keep, x)))}

# the support is a sublist of the candidates
def filt_sub(rest: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>) -> SubN(CO.filt(rest, sk, c, keep), rest):
  match rest:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      fs.c(CO.refutable(sk, c, CO.lcat(keep, t)), x, t, sk, c, keep, k => filt_sub(t, sk, c, k))

def fr.c(b: Bool, +x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, hb: {b == CO.refutable(sk, c, CO.lcat(keep, t)) : Bool},
  h: {CO.refutable(sk, c, CO.lcat(keep, Con{x, t})) == True{} : Bool},
  ih: @k: List<&2, Nat> -> {CO.refutable(sk, c, CO.lcat(k, t)) == True{} : Bool} -> {CO.refutable(sk, c, CO.lcat(k, CO.filt(t, sk, c, k))) == True{} : Bool})
  -> {CO.refutable(sk, c, CO.lcat(keep, CO.fcons(b, x, CO.filt(t, sk, c, CO.kpick(b, keep, x))))) == True{} : Bool}:
  match b:
    case True{}:
      ih(keep, Equal.sym(Bool, True{}, CO.refutable(sk, c, CO.lcat(keep, t)), hb))
    case False{}:
      %lcat_snoc(keep, x, CO.filt(t, sk, c, CO.lsnoc(keep, x))) : {CO.refutable(sk, c, _) == True{} : Bool}
      ih(CO.lsnoc(keep, x), (%Equal.sym(List<&2, Nat>, CO.lcat(CO.lsnoc(keep, x), t), CO.lcat(keep, Con{x, t}), lcat_snoc(keep, x, t)) : {CO.refutable(sk, c, _) == True{} : Bool}
        h))

# with c, what the filter keeps still refutes
def filt_ref(rest: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, h: {CO.refutable(sk, c, CO.lcat(keep, rest)) == True{} : Bool})
  -> {CO.refutable(sk, c, CO.lcat(keep, CO.filt(rest, sk, c, keep))) == True{} : Bool}:
  match rest:
    case Nil{}:
      h
    case Con{+x, +t}:
      fr.c(CO.refutable(sk, c, CO.lcat(keep, t)), x, t, sk, c, keep, {==}, h, k => a => filt_ref(t, sk, c, k, a))

# Points of smaller premises
# --------------------------

def allk_sub(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, ys: List<&2, E.QExpr>, hs: SubE(xs, ys), h: ST.AllK(~F, ms, cs, ys)) -> ST.AllK(~F, ms, cs, xs):
  match xs ys:
    case Nil{} ys:
      Unit{}
    case Con{x, xt} Nil{}:
      absurd(ST.AllK(~F, ms, cs, Con{x, xt}), hs)
    case Con{+x, +xt} Con{+y, +yt}:
      match hs:
        case Inl{+p}:
          (h1, h2) = h
          ((%Equal.sym(E.QExpr, x, y, LX.both_l({x == y : E.QExpr}, SubE(xt, yt), p)) : {IP.psi(~F, ms, cs, _) == O.zero(F) : O.C(F)}
             h1),
           allk_sub(~F, ms, cs, xt, yt, LX.both_r({x == y : E.QExpr}, SubE(xt, yt), p), h2))
        case Inr{q}:
          (h1, h2) = h
          allk_sub(~F, ms, cs, Con{x, xt}, yt, q, h2)

def alls_sub(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, xs: List<&2, SK.Side>, ys: List<&2, SK.Side>, hs: SubS(xs, ys), h: ST.AllS(~F, ms, c0, c1, ys)) -> ST.AllS(~F, ms, c0, c1, xs):
  match xs ys:
    case Nil{} ys:
      Unit{}
    case Con{x, xt} Nil{}:
      absurd(ST.AllS(~F, ms, c0, c1, Con{x, xt}), hs)
    case Con{+x, +xt} Con{+y, +yt}:
      match hs:
        case Inl{+p}:
          (h1, h2) = h
          ((%Equal.sym(SK.Side, x, y, LX.both_l({x == y : SK.Side}, SubS(xt, yt), p)) : ST.SideOK(~F, IP.psi(~F, ms, c0, SV.sexpr(_)), IP.psi(~F, ms, c1, SV.sexpr(_)), _)
             h1),
           alls_sub(~F, ms, c0, c1, xt, yt, LX.both_r({x == y : SK.Side}, SubS(xt, yt), p), h2))
        case Inr{q}:
          (h1, h2) = h
          alls_sub(~F, ms, c0, c1, Con{x, xt}, yt, q, h2)

# a point for more equations and sides is one for fewer
def pt_sub(~F: O.OField, +es1: List<&2, E.QExpr>, +es: List<&2, E.QExpr>, +ss1: List<&2, SK.Side>, +ss: List<&2, SK.Side>, +he: SubE(es1, es), +hs: SubS(ss1, ss), p: ST.Point(~F, es, ss)) -> ST.Point(~F, es1, ss1):
  (+ms, p1) = p
  (+c0, p2) = p1
  (+c1, p3) = p2
  (hk0, q1) = p3
  (hk1, q2) = q1
  (hss, q3) = q2
  (ms, (c0, (c1, (allk_sub(~F, ms, c0, es1, es, he, hk0), (allk_sub(~F, ms, c1, es1, es, he, hk1), (alls_sub(~F, ms, c0, c1, ss1, ss, hs, hss), q3))))))

# Fewer constraints, fewer premises
# ---------------------------------

def eq_nat(a: Nat, b: Nat, h: {SV.eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      absurd({0n == 1n+j : Nat}, KA.ft(h))
    case 1n+i 0n:
      absurd({1n+i == 0n : Nat}, KA.ft(h))
    case 1n+i 1n++j:
      %eq_nat(i, j, h) : {1n+i == 1n+_ : Nat}
      {==}

def ms.c(b: Bool, +v: Nat, +h: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, hb: {b == SV.eq(v, h) : Bool}, hm: {SV.bor(SV.eq(v, h), SV.mem(v, t)) == True{} : Bool},
  hh: {SV.mem(h, ys) == True{} : Bool}, ih: {SV.mem(v, t) == True{} : Bool} -> {SV.mem(v, ys) == True{} : Bool}) -> {SV.mem(v, ys) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, v, h, eq_nat(v, h, Equal.sym(Bool, True{}, SV.eq(v, h), hb))) : {SV.mem(_, ys) == True{} : Bool}
      hh
    case False{}:
      ih(LI.bor_rf(SV.eq(v, h), SV.mem(v, t), hm, Equal.sym(Bool, False{}, SV.eq(v, h), hb)))

def mem_sub(+v: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hs: {SV.sub(xs, ys) == True{} : Bool}, hm: {SV.mem(v, xs) == True{} : Bool}) -> {SV.mem(v, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(v, ys) == True{} : Bool}, LI.mem_nil(v, hm))
    case Con{+h, +t}:
      ms.c(SV.eq(v, h), v, h, t, ys, {==}, hm, LI.band_l(SV.mem(h, ys), SV.sub(t, ys), hs), a => mem_sub(v, t, ys, LI.band_r(SV.mem(h, ys), SV.sub(t, ys), hs), a))

def sub_cons(xs: List<&2, Nat>, +a: Nat, +ys: List<&2, Nat>, +h: {SV.sub(xs, ys) == True{} : Bool}) -> {SV.sub(xs, Con{a, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LI.band_i(SV.mem(x, Con{a, ys}), SV.sub(t, Con{a, ys}), LI.mem_tl(x, a, ys, LI.band_l(SV.mem(x, ys), SV.sub(t, ys), h)), sub_cons(t, a, ys, LI.band_r(SV.mem(x, ys), SV.sub(t, ys), h)))

def sub_ct(+c: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, h: {SV.sub(xs, ys) == True{} : Bool}) -> {SV.sub(Con{c, xs}, Con{c, ys}) == True{} : Bool}:
  LI.band_i(SV.mem(c, Con{c, ys}), SV.sub(xs, Con{c, ys}), LI.mem_hd(c, ys), sub_cons(xs, c, ys, h))

def eqs_mono.c(b1: Bool, b2: Bool, +e: E.QExpr, +r1: List<&2, E.QExpr>, +r2: List<&2, E.QExpr>, hb: {b1 == True{} : Bool} -> {b2 == True{} : Bool}, ih: SubE(r1, r2))
  -> SubE(SV.solved.pick(b1, e, r1), SV.solved.pick(b2, e, r2)):
  match b1 b2:
    case True{} True{}:
      Inl{({==}, ih)}
    case True{} False{}:
      absurd(SubE(Con{e, r1}, r2), KA.ft(hb({==})))
    case False{} True{}:
      sube_cons_r(r1, e, r2, ih)
    case False{} False{}:
      ih

def eqs_mono(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +k: Nat, +hsub: {SV.sub(cs1, cs2) == True{} : Bool})
  -> SubE(SV.eqs_of.go(es, own, cs1, k), SV.eqs_of.go(es, own, cs2, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      eqs_mono.c(SV.mem(SV.nth(own, k), cs1), SV.mem(SV.nth(own, k), cs2), e, SV.eqs_of.go(t, own, cs1, 1n+k), SV.eqs_of.go(t, own, cs2, 1n+k),
        a => mem_sub(SV.nth(own, k), cs1, cs2, hsub, a), eqs_mono(t, own, cs1, cs2, 1n+k, hsub))

def sides_mono.c(b1: Bool, b2: Bool, +xs: List<&2, SK.Side>, +r1: List<&2, SK.Side>, +r2: List<&2, SK.Side>, hb: {b1 == True{} : Bool} -> {b2 == True{} : Bool}, ih: SubS(r1, r2))
  -> SubS(SV.csides.pick(b1, xs, r1), SV.csides.pick(b2, xs, r2)):
  match b1 b2:
    case True{} True{}:
      subs_cats(xs, r1, r2, ih)
    case True{} False{}:
      absurd(SubS(SK.cats(xs, r1), r2), KA.ft(hb({==})))
    case False{} True{}:
      subs_cats_r(r1, xs, r2, ih)
    case False{} False{}:
      ih

def sides_mono(+es: List<&2, SK.Ent>, rs: List<&2, SK.Rec>, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +i: Nat, +hsub: {SV.sub(cs1, cs2) == True{} : Bool})
  -> SubS(SV.csides.go(es, rs, cs1, i), SV.csides.go(es, rs, cs2, i)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{id, True{}, k}, t}:
      sides_mono(es, t, cs1, cs2, 1n+i, hsub)
    case Con{SK.Rec{id, False{}, +k}, +t}:
      sides_mono.c(SV.mem(i, cs1), SV.mem(i, cs2), SK.Constraint.sides(es, k), SV.csides.go(es, t, cs1, 1n+i), SV.csides.go(es, t, cs2, 1n+i),
        a => mem_sub(i, cs1, cs2, hsub, a), sides_mono(es, t, cs1, cs2, 1n+i, hsub))

# U among T: c with U stands for fewer equations and sides than c with T
def supp_mono_e(+sk: SK.Sketch, +c: Nat, +U: List<&2, Nat>, +T: List<&2, Nat>, h: {SV.sub(U, T) == True{} : Bool}) -> SubE(CO.supp.es(sk, c, U), CO.supp.es(sk, c, T)):
  eqs_mono(SK.Sketch.eqs(sk), SV.owners(sk), Con{c, U}, Con{c, T}, 0n, sub_ct(c, U, T, h))

def supp_mono_s(sk: SK.Sketch, +c: Nat, +U: List<&2, Nat>, +T: List<&2, Nat>, h: {SV.sub(U, T) == True{} : Bool}) -> SubS(CO.supp.ss(sk, c, U), CO.supp.ss(sk, c, T)):
  match sk:
    case SK.Sketch{+vs, +es, +rs}:
      subs_cats_l(SV.csides.go(es, rs, Con{c, U}, 0n), SV.csides.go(es, rs, Con{c, T}, 0n), SV.esides(SK.Sketch{vs, es, rs}),
        sides_mono(es, rs, Con{c, U}, Con{c, T}, 0n, sub_ct(c, U, T, h)))

# The member left out
# -------------------

def su.c(b: Bool, +x: Nat, +r: Nat, +U: List<&2, Nat>, +y: Nat, +t: List<&2, Nat>, e: {r == y : Nat}, ih: {SV.sub(U, t) == True{} : Bool})
  -> {SV.sub(SV.unmark.go(b, r, U), Con{y, t}) == True{} : Bool}:
  match b:
    case True{}:
      sub_cons(U, y, t, ih)
    case False{}:
      LI.band_i(SV.mem(r, Con{y, t}), SV.sub(U, Con{y, t}),
        (%Equal.sym(Nat, r, y, e) : {SV.mem(_, Con{y, t}) == True{} : Bool}
          LI.mem_hd(y, t)),
        sub_cons(U, y, t, ih))

# R a sublist of t: R without x is among t
def sub_unmark_subn(+x: Nat, R: List<&2, Nat>, t: List<&2, Nat>, h: SubN(R, t)) -> {SV.sub(SV.unmark(x, R), t) == True{} : Bool}:
  match R t:
    case Nil{} t:
      {==}
    case Con{r, rt} Nil{}:
      absurd({SV.sub(SV.unmark(x, Con{r, rt}), Nil{}) == True{} : Bool}, h)
    case Con{+r, +rt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          su.c(SV.eq(r, x), x, r, SV.unmark(x, rt), y, yt, LX.both_l({r == y : Nat}, SubN(rt, yt), p), sub_unmark_subn(x, rt, yt, LX.both_r({r == y : Nat}, SubN(rt, yt), p)))
        case Inr{q}:
          sub_cons(SV.unmark(x, Con{r, rt}), y, yt, sub_unmark_subn(x, Con{r, rt}, yt, q))

def su2.c(b: Bool, +a: Nat, +U: List<&2, Nat>, +V: List<&2, Nat>, ih: {SV.sub(U, V) == True{} : Bool}) -> {SV.sub(SV.unmark.go(b, a, U), Con{a, V}) == True{} : Bool}:
  match b:
    case True{}:
      sub_cons(U, a, V, ih)
    case False{}:
      sub_ct(a, U, V, ih)

def sub_unmark_cat(+x: Nat, keep: List<&2, Nat>, +B: List<&2, Nat>, +B2: List<&2, Nat>, h: {SV.sub(SV.unmark(x, B), B2) == True{} : Bool})
  -> {SV.sub(SV.unmark(x, CO.lcat(keep, B)), CO.lcat(keep, B2)) == True{} : Bool}:
  match keep:
    case Nil{}:
      h
    case Con{+a, +kt}:
      su2.c(SV.eq(a, x), a, SV.unmark(x, CO.lcat(kt, B)), CO.lcat(kt, B2), sub_unmark_cat(x, kt, B, B2, h))

# the support but x is among what was tested when x was kept
def sub_unmark(+x: Nat, +keep: List<&2, Nat>, +R: List<&2, Nat>, +t: List<&2, Nat>, h: SubN(R, t)) -> {SV.sub(SV.unmark(x, CO.lcat(keep, Con{x, R})), CO.lcat(keep, t)) == True{} : Bool}:
  sub_unmark_cat(x, keep, Con{x, R}, t,
    (%Equal.sym(Bool, SV.eq(x, x), True{}, LI.eq_refl(x)) : {SV.sub(SV.unmark.go(_, x, SV.unmark(x, R)), t) == True{} : Bool}
      sub_unmark_subn(x, R, t, h)))

# Without any one member, no refutation
# -------------------------------------

def none_of(m: Maybe<&2, RF.Cert>, h: {CO.issome(m) == False{} : Bool}) -> {m == None{} : Maybe<&2, RF.Cert>}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      absurd({Some{c} == None{} : Maybe<&2, RF.Cert>}, KA.tf(h))


# x was kept: c with the others then tested had no refutation, so a point
# (in lib/lqfield.bend's ordered field: the point is used only here, and
# that field checks far faster than qfield's)
def fi.x(+x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, +R: List<&2, Nat>, hb: {False{} == CO.refutable(sk, c, CO.lcat(keep, t)) : Bool}, hR: SubN(R, t))
  -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R})))):
  +hs = sub_unmark(x, keep, R, t, hR)
  ST.pt_noref(~LQF.lqfield(), CO.supp.es(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R}))),
    pt_sub(~LQF.lqfield(), CO.supp.es(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R}))), CO.supp.es(sk, c, CO.lcat(keep, t)), CO.supp.ss(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, CO.lcat(keep, t)), supp_mono_e(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R})), CO.lcat(keep, t), hs), supp_mono_s(sk, c, SV.unmark(x, CO.lcat(keep, Con{x, R})), CO.lcat(keep, t), hs),
      ST.pt_of_none(~LQF.lqfield(), CO.supp.es(sk, c, CO.lcat(keep, t)), CO.supp.ss(sk, c, CO.lcat(keep, t)),
        none_of(RF.refute(CO.supp.es(sk, c, CO.lcat(keep, t)), CO.supp.ss(sk, c, CO.lcat(keep, t))), Equal.sym(Bool, False{}, CO.refutable(sk, c, CO.lcat(keep, t)), hb)))))

def fi.m(bm: Bool, +m: Nat, +x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, +R: List<&2, Nat>, hbm: {bm == SV.eq(m, x) : Bool},
  hm: {SV.bor(SV.eq(m, x), SV.mem(m, R)) == True{} : Bool}, hb: {False{} == CO.refutable(sk, c, CO.lcat(keep, t)) : Bool}, hR: SubN(R, t),
  ih: @m2: Nat -> {SV.mem(m2, R) == True{} : Bool} -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m2, CO.lcat(CO.lsnoc(keep, x), R))), CO.supp.ss(sk, c, SV.unmark(m2, CO.lcat(CO.lsnoc(keep, x), R)))))
  -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, Con{x, R})))):
  match bm:
    case True{}:
      %Equal.sym(Nat, m, x, eq_nat(m, x, Equal.sym(Bool, True{}, SV.eq(m, x), hbm))) : ST.NoRef(CO.supp.es(sk, c, SV.unmark(_, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, SV.unmark(_, CO.lcat(keep, Con{x, R}))))
      fi.x(x, t, sk, c, keep, R, hb, hR)
    case False{}:
      (%lcat_snoc(keep, x, R) : ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, _)), CO.supp.ss(sk, c, SV.unmark(m, _)))
        ih(m, LI.bor_rf(SV.eq(m, x), SV.mem(m, R), hm, Equal.sym(Bool, False{}, SV.eq(m, x), hbm))))

def fi.f(+m: Nat, +x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, +R: List<&2, Nat>, hm: {SV.mem(m, Con{x, R}) == True{} : Bool}, hb: {False{} == CO.refutable(sk, c, CO.lcat(keep, t)) : Bool}, hR: SubN(R, t),
  ih: @m2: Nat -> {SV.mem(m2, R) == True{} : Bool} -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m2, CO.lcat(CO.lsnoc(keep, x), R))), CO.supp.ss(sk, c, SV.unmark(m2, CO.lcat(CO.lsnoc(keep, x), R)))))
  -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, Con{x, R}))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, Con{x, R})))):
  fi.m(SV.eq(m, x), m, x, t, sk, c, keep, R, {==}, hm, hb, hR, ih)


def fi.c(b: Bool, +x: Nat, +t: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, hb: {b == CO.refutable(sk, c, CO.lcat(keep, t)) : Bool},
  ihs: @k: List<&2, Nat> -> SubN(CO.filt(t, sk, c, k), t), ih: @k: List<&2, Nat> -> @m: Nat -> {SV.mem(m, CO.filt(t, sk, c, k)) == True{} : Bool} -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(k, CO.filt(t, sk, c, k)))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(k, CO.filt(t, sk, c, k))))))
  -> @m: Nat -> {SV.mem(m, CO.fcons(b, x, CO.filt(t, sk, c, CO.kpick(b, keep, x)))) == True{} : Bool} -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, CO.fcons(b, x, CO.filt(t, sk, c, CO.kpick(b, keep, x)))))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, CO.fcons(b, x, CO.filt(t, sk, c, CO.kpick(b, keep, x))))))):
  match b:
    case True{}:
      ih(keep)
    case False{}:
      m => hm => fi.f(m, x, t, sk, c, keep, CO.filt(t, sk, c, CO.lsnoc(keep, x)), hm, hb, ihs(CO.lsnoc(keep, x)), ih(CO.lsnoc(keep, x)))

def fi.nil(+m: Nat, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>, hm: {SV.mem(m, Nil{}) == True{} : Bool}) -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, Nil{}))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, Nil{})))):
  absurd(ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, Nil{}))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, Nil{})))), LI.mem_nil(m, hm))

# every member the filter kept is needed
def filt_irr(rest: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>)
  -> @m: Nat -> {SV.mem(m, CO.filt(rest, sk, c, keep)) == True{} : Bool} -> ST.NoRef(CO.supp.es(sk, c, SV.unmark(m, CO.lcat(keep, CO.filt(rest, sk, c, keep)))), CO.supp.ss(sk, c, SV.unmark(m, CO.lcat(keep, CO.filt(rest, sk, c, keep))))):
  match rest:
    case Nil{}:
      m => hm => fi.nil(m, sk, c, keep, hm)
    case Con{+x, +t}:
      fi.c(CO.refutable(sk, c, CO.lcat(keep, t)), x, t, sk, c, keep, {==}, k => filt_sub(t, sk, c, k), k => filt_irr(t, sk, c, k))

# What a sublist keeps
# --------------------

def bnot_t(b: Bool, h: {SV.bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

def nmem.go(b: Bool, +v: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, hb: {b == SV.mem(v, xs) : Bool}, h: SubN(xs, ys), hn: {SV.mem(v, ys) == False{} : Bool}) -> {SV.mem(v, xs) == False{} : Bool}:
  match b:
    case True{}:
      absurd({SV.mem(v, xs) == False{} : Bool}, KA.ft((%hn : {_ == True{} : Bool}
        mem_subn(v, xs, ys, h, Equal.sym(Bool, True{}, SV.mem(v, xs), hb)))))
    case False{}:
      Equal.sym(Bool, False{}, SV.mem(v, xs), hb)

def nmem_sub(+v: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, h: SubN(xs, ys), hn: {SV.mem(v, ys) == False{} : Bool}) -> {SV.mem(v, xs) == False{} : Bool}:
  nmem.go(SV.mem(v, xs), v, xs, ys, {==}, h, hn)

def distinct_sub(xs: List<&2, Nat>, ys: List<&2, Nat>, h: SubN(xs, ys), hd: {SV.distinct(ys) == True{} : Bool}) -> {SV.distinct(xs) == True{} : Bool}:
  match xs ys:
    case Nil{} ys:
      {==}
    case Con{x, xt} Nil{}:
      absurd({SV.distinct(Con{x, xt}) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          +hd2 = hd
          LI.band_i(SV.bnot(SV.mem(x, xt)), SV.distinct(xt),
            (%Equal.sym(Bool, SV.mem(x, xt), False{}, nmem_sub(x, xt, yt, LX.both_r({x == y : Nat}, SubN(xt, yt), p),
                 (%Equal.sym(Nat, x, y, LX.both_l({x == y : Nat}, SubN(xt, yt), p)) : {SV.mem(_, yt) == False{} : Bool}
                   bnot_t(SV.mem(y, yt), LI.band_l(SV.bnot(SV.mem(y, yt)), SV.distinct(yt), hd2))))) : {SV.bnot(_) == True{} : Bool}
              {==}),
            distinct_sub(xt, yt, LX.both_r({x == y : Nat}, SubN(xt, yt), p), LI.band_r(SV.bnot(SV.mem(y, yt)), SV.distinct(yt), hd2)))
        case Inr{q}:
          distinct_sub(Con{x, xt}, yt, q, LI.band_r(SV.bnot(SV.mem(y, yt)), SV.distinct(yt), hd))

def below_sub(xs: List<&2, Nat>, ys: List<&2, Nat>, +n: Nat, h: SubN(xs, ys), hd: {SV.below(ys, n) == True{} : Bool}) -> {SV.below(xs, n) == True{} : Bool}:
  match xs ys:
    case Nil{} ys:
      {==}
    case Con{x, xt} Nil{}:
      absurd({SV.below(Con{x, xt}, n) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          +hd2 = hd
          LI.band_i(SV.lt(x, n), SV.below(xt, n),
            (%Equal.sym(Nat, x, y, LX.both_l({x == y : Nat}, SubN(xt, yt), p)) : {SV.lt(_, n) == True{} : Bool}
              LI.band_l(SV.lt(y, n), SV.below(yt, n), hd2)),
            below_sub(xt, yt, n, LX.both_r({x == y : Nat}, SubN(xt, yt), p), LI.band_r(SV.lt(y, n), SV.below(yt, n), hd2)))
        case Inr{q}:
          below_sub(Con{x, xt}, yt, n, q, LI.band_r(SV.lt(y, n), SV.below(yt, n), hd))

def drv_sub(+sk: SK.Sketch, xs: List<&2, Nat>, ys: List<&2, Nat>, h: SubN(xs, ys), hd: {SV.all_driving(sk, ys) == True{} : Bool}) -> {SV.all_driving(sk, xs) == True{} : Bool}:
  match xs ys:
    case Nil{} ys:
      {==}
    case Con{x, xt} Nil{}:
      absurd({SV.all_driving(sk, Con{x, xt}) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          +hd2 = hd
          LI.band_i(SV.driving(sk, x), SV.all_driving(sk, xt),
            (%Equal.sym(Nat, x, y, LX.both_l({x == y : Nat}, SubN(xt, yt), p)) : {SV.driving(sk, _) == True{} : Bool}
              LI.band_l(SV.driving(sk, y), SV.all_driving(sk, yt), hd2)),
            drv_sub(sk, xt, yt, LX.both_r({x == y : Nat}, SubN(xt, yt), p), LI.band_r(SV.driving(sk, y), SV.all_driving(sk, yt), hd2)))
        case Inr{q}:
          drv_sub(sk, Con{x, xt}, yt, q, LI.band_r(SV.driving(sk, y), SV.all_driving(sk, yt), hd))

def nin_sub(xs: List<&2, Nat>, ys: List<&2, Nat>, +red: List<&2, Nat>, h: SubN(xs, ys), hd: {SV.none_in(ys, red) == True{} : Bool}) -> {SV.none_in(xs, red) == True{} : Bool}:
  match xs ys:
    case Nil{} ys:
      {==}
    case Con{x, xt} Nil{}:
      absurd({SV.none_in(Con{x, xt}, red) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      match h:
        case Inl{+p}:
          +hd2 = hd
          LI.band_i(SV.bnot(SV.mem(x, red)), SV.none_in(xt, red),
            (%Equal.sym(Nat, x, y, LX.both_l({x == y : Nat}, SubN(xt, yt), p)) : {SV.bnot(SV.mem(_, red)) == True{} : Bool}
              LI.band_l(SV.bnot(SV.mem(y, red)), SV.none_in(yt, red), hd2)),
            nin_sub(xt, yt, red, LX.both_r({x == y : Nat}, SubN(xt, yt), p), LI.band_r(SV.bnot(SV.mem(y, red)), SV.none_in(yt, red), hd2)))
        case Inr{q}:
          nin_sub(Con{x, xt}, yt, red, q, LI.band_r(SV.bnot(SV.mem(y, red)), SV.none_in(yt, red), hd))

# The theorem
# -----------

def rw.go(mc: Maybe<&2, RF.Cert>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, h: {CO.issome(mc) == True{} : Bool}, ok: ST.RefOk(es, ss, mc))
  -> &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(es, ss, ls, ms, k):
  match mc:
    case None{}:
      absurd(&ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(es, ss, ls, ms, k), KA.ft(h))
    case Some{RF.Cert{+ls, +ms, +k}}:
      (ls, (ms, (k, ok)))


# candidates that are distinct, before c, driving and not red, with which c
# refutes: the filter's support is a conflict's (the spec's ConflictOk)
def conflict_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +cand: List<&2, Nat>, +hc: {SV.band(SV.distinct(cand), SV.band(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red)))) == True{} : Bool}, hr: {CO.refutable(sk, c, cand) == True{} : Bool})
  -> SV.ConflictOk(sk, red, c, CO.support(sk, c, cand)):
  +hs = filt_sub(cand, sk, c, Nil{})
  +h2 = LI.band_r(SV.distinct(cand), SV.band(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red))), hc)
  +h3 = LI.band_r(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red)), h2)
  (LI.band_i(SV.distinct(CO.support(sk, c, cand)), SV.band(SV.below(CO.support(sk, c, cand), c), SV.band(SV.all_driving(sk, CO.support(sk, c, cand)), SV.none_in(CO.support(sk, c, cand), red))),
     distinct_sub(CO.support(sk, c, cand), cand, hs, LI.band_l(SV.distinct(cand), SV.band(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red))), hc)),
     LI.band_i(SV.below(CO.support(sk, c, cand), c), SV.band(SV.all_driving(sk, CO.support(sk, c, cand)), SV.none_in(CO.support(sk, c, cand), red)),
       below_sub(CO.support(sk, c, cand), cand, c, hs, LI.band_l(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red)), h2)),
       LI.band_i(SV.all_driving(sk, CO.support(sk, c, cand)), SV.none_in(CO.support(sk, c, cand), red),
         drv_sub(sk, CO.support(sk, c, cand), cand, hs, LI.band_l(SV.all_driving(sk, cand), SV.none_in(cand, red), h3)),
         nin_sub(CO.support(sk, c, cand), cand, red, hs, LI.band_r(SV.all_driving(sk, cand), SV.none_in(cand, red), h3))))),
   (rw.go(RF.refute(CO.supp.es(sk, c, CO.support(sk, c, cand)), CO.supp.ss(sk, c, CO.support(sk, c, cand))), CO.supp.es(sk, c, CO.support(sk, c, cand)), CO.supp.ss(sk, c, CO.support(sk, c, cand)), filt_ref(cand, sk, c, Nil{}, hr), ST.refute_ok(CO.supp.es(sk, c, CO.support(sk, c, cand)), CO.supp.ss(sk, c, CO.support(sk, c, cand)))),
    filt_irr(cand, sk, c, Nil{})))
