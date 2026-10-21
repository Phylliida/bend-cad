# bend-cad: the pass's three uses of refute (PLAN-sk13a S4). Proofs only.
# kb is the kept constraints before c (lib/kbpf.bend: kb_next makes it
# kept_before), and refute decides (lib/satpf.bend: refute_ok):
# - c with kb not refutable: NoRefute. refute found a point for c's and
#   kb's equations and sides in the filter's order (c first, the entities'
#   sides last); it is a point for them in the spec's order too.
# - refutable: the deletion filter's support is ConflictOk
#   (lib/conflictpf.bend).
# - each of c's sides, its negation refuted with the premises or not:
#   Implied or NotImplied (lib/pass.bend: srefs).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./lqfield.bend as LQF
import ./listpf.bend as LI
import ./refute.bend as RF
import ./satpf.bend as ST
import ./conflict.bend as CO
import ./conflictpf.bend as CP
import ./pass.bend as PA
import ./kbpf.bend as KB

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Points, whatever the order
# --------------------------

def allk_l(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, h: ST.AllK(~F, ms, cs, SK.cat(xs, ys))) -> ST.AllK(~F, ms, cs, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, xt}:
      (h1, h2) = h
      (h1, allk_l(~F, ms, cs, xt, ys, h2))

def allk_r(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, h: ST.AllK(~F, ms, cs, SK.cat(xs, ys))) -> ST.AllK(~F, ms, cs, ys):
  match xs:
    case Nil{}:
      h
    case Con{x, xt}:
      (h1, h2) = h
      allk_r(~F, ms, cs, xt, ys, h2)

def allk_cat(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, h1: ST.AllK(~F, ms, cs, xs), h2: ST.AllK(~F, ms, cs, ys)) -> ST.AllK(~F, ms, cs, SK.cat(xs, ys)):
  match xs:
    case Nil{}:
      h2
    case Con{x, xt}:
      (a, b) = h1
      (a, allk_cat(~F, ms, cs, xt, ys, b, h2))

def alls_l(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, xs: List<&2, SK.Side>, +ys: List<&2, SK.Side>, h: ST.AllS(~F, ms, c0, c1, SK.cats(xs, ys))) -> ST.AllS(~F, ms, c0, c1, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, xt}:
      (h1, h2) = h
      (h1, alls_l(~F, ms, c0, c1, xt, ys, h2))

def alls_r(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, xs: List<&2, SK.Side>, +ys: List<&2, SK.Side>, h: ST.AllS(~F, ms, c0, c1, SK.cats(xs, ys))) -> ST.AllS(~F, ms, c0, c1, ys):
  match xs:
    case Nil{}:
      h
    case Con{x, xt}:
      (h1, h2) = h
      alls_r(~F, ms, c0, c1, xt, ys, h2)

def alls_cat(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, xs: List<&2, SK.Side>, +ys: List<&2, SK.Side>, h1: ST.AllS(~F, ms, c0, c1, xs), h2: ST.AllS(~F, ms, c0, c1, ys)) -> ST.AllS(~F, ms, c0, c1, SK.cats(xs, ys)):
  match xs:
    case Nil{}:
      h2
    case Con{x, xt}:
      (a, b) = h1
      (a, alls_cat(~F, ms, c0, c1, xt, ys, b, h2))

def sub_refl(xs: List<&2, Nat>) -> {SV.sub(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      CP.sub_ct(x, t, t, sub_refl(t))

def sides_sub(sk: SK.Sketch, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {SV.sub(xs, ys) == True{} : Bool}) -> CP.SubS(SV.csides(sk, xs), SV.csides(sk, ys)):
  match sk:
    case SK.Sketch{vs, +es, +rs}:
      CP.sides_mono(es, rs, xs, ys, 0n, h)

# a point for c and kb in the filter's order is one in the spec's
def pt_reord(~F: O.OField, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, p: ST.Point(~F, CO.supp.es(sk, c, kb), CO.supp.ss(sk, c, kb)))
  -> ST.Point(~F, SK.cat(SV.eqs_of(sk, kb), SV.eqs_of(sk, [c])), SK.cats(SK.cats(SV.csides(sk, kb), SV.esides(sk)), SV.csides(sk, [c]))):
  (+ms, p1) = p
  (+c0, p2) = p1
  (+c1, p3) = p2
  (+k0, q1) = p3
  (+k1, q2) = q1
  (+s, q3) = q2
  +A = SV.eqs_of(sk, kb)
  +B = SV.eqs_of(sk, [c])
  +ES = SV.eqs_of(sk, Con{c, kb})
  +he1 = CP.eqs_mono(SK.Sketch.eqs(sk), SV.owners(sk), kb, Con{c, kb}, 0n, CP.sub_cons(kb, c, kb, sub_refl(kb)))
  +he2 = CP.eqs_mono(SK.Sketch.eqs(sk), SV.owners(sk), [c], Con{c, kb}, 0n, CP.sub_ct(c, Nil{}, kb, {==}))
  +SC = SV.csides(sk, Con{c, kb})
  +sc = alls_l(~F, ms, c0, c1, SC, SV.esides(sk), s)
  +s1 = CP.alls_sub(~F, ms, c0, c1, SV.csides(sk, kb), SC, sides_sub(sk, kb, Con{c, kb}, CP.sub_cons(kb, c, kb, sub_refl(kb))), sc)
  +s2 = CP.alls_sub(~F, ms, c0, c1, SV.csides(sk, [c]), SC, sides_sub(sk, [c], Con{c, kb}, CP.sub_ct(c, Nil{}, kb, {==})), sc)
  +se = alls_r(~F, ms, c0, c1, SC, SV.esides(sk), s)
  (ms, (c0, (c1, (allk_cat(~F, ms, c0, A, B, CP.allk_sub(~F, ms, c0, A, ES, he1, k0), CP.allk_sub(~F, ms, c0, B, ES, he2, k0)),
    (allk_cat(~F, ms, c1, A, B, CP.allk_sub(~F, ms, c1, A, ES, he1, k1), CP.allk_sub(~F, ms, c1, B, ES, he2, k1)),
    (alls_cat(~F, ms, c0, c1, SK.cats(SV.csides(sk, kb), SV.esides(sk)), SV.csides(sk, [c]), alls_cat(~F, ms, c0, c1, SV.csides(sk, kb), SV.esides(sk), s1, se), s2), q3))))))

# NoRefute
# --------

# c with kb not refutable: no refutation of them in the spec's order (the
# point is read in lib/lqfield.bend's ordered field, which checks far faster
# than qfield's)
def no_refute(+sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, h: {CO.refutable(sk, c, kb) == False{} : Bool})
  -> ST.NoRef(SK.cat(SV.eqs_of(sk, kb), SV.eqs_of(sk, [c])), SK.cats(SK.cats(SV.csides(sk, kb), SV.esides(sk)), SV.csides(sk, [c]))):
  ST.pt_noref(~LQF.lqfield(), SK.cat(SV.eqs_of(sk, kb), SV.eqs_of(sk, [c])), SK.cats(SK.cats(SV.csides(sk, kb), SV.esides(sk)), SV.csides(sk, [c])),
    pt_reord(~LQF.lqfield(), sk, c, kb, ST.pt_of_none(~LQF.lqfield(), CO.supp.es(sk, c, kb), CO.supp.ss(sk, c, kb), CP.none_of(RF.refute(CO.supp.es(sk, c, kb), CO.supp.ss(sk, c, kb)), h))))

# the same, as the spec says it, kb being kept_before
def norefute(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, h: {CO.refutable(sk, c, SV.kept_before(sk, R, c)) == False{} : Bool}) -> SV.NoRefute(sk, R, c):
  no_refute(sk, c, SV.kept_before(sk, R, c), h)

# ConflictOk
# ----------

def conflict(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +kb: List<&2, Nat>, hk: KB.KBP(sk, R, kb, c), hr: {CO.refutable(sk, c, kb) == True{} : Bool}) -> SV.ConflictOk(sk, R, c, CO.support(sk, c, kb)):
  CP.conflict_ok(sk, R, c, kb, KB.kbp_bool(sk, R, kb, c, hk), hr)

# Implied, NotImplied
# -------------------

# c's j-th side is implied by kb (and the entities' sides)
def ImpK(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +j: Nat) -> Type:
  &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, j), ls, ms, k)

def imp_of(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, h: {RF.refute(es, ss) == Some{RF.Cert{ls, ms, k}} : Maybe<&2, RF.Cert>})
  -> &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(es, ss, ls, ms, k):
  (ls, (ms, (k, (%h : ST.RefOk(es, ss, _)
    ST.refute_ok(es, ss)))))

def noimp_of(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, h: {RF.refute(es, ss) == None{} : Maybe<&2, RF.Cert>}) -> ST.NoRef(es, ss):
  %h : ST.RefOk(es, ss, _)
  ST.refute_ok(es, ss)

def lt_zero(j: Nat, h: {SV.lt(j, 0n) == True{} : Bool}) -> Empty:
  match j:
    case 0n:
      KA.ft(h)
    case 1n+i:
      KA.ft(h)

def ImpK.zero(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, h: ImpK(sk, kb, c, i)) -> ImpK(sk, kb, c, Nat.add(i, 0n)):
  %LN.add_zero(i) : ImpK(sk, kb, c, _)
  h

def isnone(m: Maybe<&2, List<&2, SV.Ref>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def srefs_some.c(m: Maybe<&2, RF.Cert>, r: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, +t: List<&2, SK.Side>, +rs: List<&2, SV.Ref>,
  em: {RF.refute(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i)) == m : Maybe<&2, RF.Cert>}, er: {PA.srefs(t, sk, kb, c, 1n+i) == r : Maybe<&2, List<&2, SV.Ref>>},
  h: {PA.srefs.c(m, r) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>}, j: Nat, hj: {SV.lt(j, 1n+SV.slen(t)) == True{} : Bool},
  ih: @rs2: List<&2, SV.Ref> -> {PA.srefs(t, sk, kb, c, 1n+i) == Some{rs2} : Maybe<&2, List<&2, SV.Ref>>} -> @j2: Nat -> {SV.lt(j2, SV.slen(t)) == True{} : Bool} -> ImpK(sk, kb, c, Nat.add(1n+i, j2)))
  -> ImpK(sk, kb, c, Nat.add(i, j)):
  match m r:
    case None{} r:
      absurd(ImpK(sk, kb, c, Nat.add(i, j)), KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, x => isnone(x), None{}, Some{rs}, h)))
    case Some{RF.Cert{ls, ms, k}} None{}:
      absurd(ImpK(sk, kb, c, Nat.add(i, j)), KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, x => isnone(x), None{}, Some{rs}, h)))
    case Some{RF.Cert{+ls, +ms, +k}} Some{rs2}:
      match j:
        case 0n:
          ImpK.zero(sk, kb, c, i, imp_of(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i), ls, ms, k, em))
        case 1n+j2:
          %LN.add_succ(i, j2) : ImpK(sk, kb, c, _)
          ih(rs2, er, j2, hj)

# every side from the i-th (ss, refuted by srefs) is implied
def srefs_some(ss: List<&2, SK.Side>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, +rs: List<&2, SV.Ref>, h: {PA.srefs(ss, sk, kb, c, i) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>},
  j: Nat, hj: {SV.lt(j, SV.slen(ss)) == True{} : Bool}) -> ImpK(sk, kb, c, Nat.add(i, j)):
  match ss:
    case Nil{}:
      absurd(ImpK(sk, kb, c, Nat.add(i, j)), lt_zero(j, hj))
    case Con{s, +t}:
      srefs_some.c(RF.refute(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i)), PA.srefs(t, sk, kb, c, 1n+i), sk, kb, c, i, t, rs, {==}, {==}, h, j, hj,
        rs2 => h2 => j2 => hj2 => srefs_some(t, sk, kb, c, 1n+i, rs2, h2, j2, hj2))

def NotK(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, +n: Nat) -> Type:
  &j: Nat -> ({SV.lt(j, n) == True{} : Bool} & ST.NoRef(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, Nat.add(i, j))))

def notk_up(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, +n: Nat, p: NotK(sk, kb, c, 1n+i, n)) -> NotK(sk, kb, c, i, 1n+n):
  (+j2, pr) = p
  (hj2, nr) = pr
  (1n+j2, (hj2, (%LN.add_succ(i, j2) : ST.NoRef(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, _))
    nr)))

def srefs_none.c(m: Maybe<&2, RF.Cert>, r: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, +t: List<&2, SK.Side>,
  em: {RF.refute(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i)) == m : Maybe<&2, RF.Cert>}, er: {PA.srefs(t, sk, kb, c, 1n+i) == r : Maybe<&2, List<&2, SV.Ref>>},
  h: {PA.srefs.c(m, r) == None{} : Maybe<&2, List<&2, SV.Ref>>}, ih: {PA.srefs(t, sk, kb, c, 1n+i) == None{} : Maybe<&2, List<&2, SV.Ref>>} -> NotK(sk, kb, c, 1n+i, SV.slen(t)))
  -> NotK(sk, kb, c, i, 1n+SV.slen(t)):
  match m r:
    case None{} r:
      (0n, ({==}, (%LN.add_zero(i) : ST.NoRef(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, _))
        noimp_of(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i), em))))
    case Some{RF.Cert{ls, ms, k}} None{}:
      notk_up(sk, kb, c, i, SV.slen(t), ih(er))
    case Some{RF.Cert{ls, ms, k}} Some{rs2}:
      absurd(NotK(sk, kb, c, i, 1n+SV.slen(t)), KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, x => isnone(x), None{}, Some{Con{SV.Ref{ls, ms, k}, rs2}}, Equal.sym(Maybe<&2, List<&2, SV.Ref>>, Some{Con{SV.Ref{ls, ms, k}, rs2}}, None{}, h))))

# some side from the i-th (ss, not all refuted) is not implied
def srefs_none(ss: List<&2, SK.Side>, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +i: Nat, h: {PA.srefs(ss, sk, kb, c, i) == None{} : Maybe<&2, List<&2, SV.Ref>>}) -> NotK(sk, kb, c, i, SV.slen(ss)):
  match ss:
    case Nil{}:
      absurd(NotK(sk, kb, c, i, 0n), KA.tf(Equal.cong(Maybe<&2, List<&2, SV.Ref>>, Bool, x => isnone(x), None{}, Some{Nil{}}, Equal.sym(Maybe<&2, List<&2, SV.Ref>>, Some{Nil{}}, None{}, h))))
    case Con{s, +t}:
      srefs_none.c(RF.refute(SV.eqs_of(sk, kb), PA.neg_kb(sk, kb, c, i)), PA.srefs(t, sk, kb, c, 1n+i), sk, kb, c, i, t, {==}, {==}, h,
        h2 => srefs_none(t, sk, kb, c, 1n+i, h2))
