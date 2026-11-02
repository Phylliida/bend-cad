# bend-cad: law 3, solve_blame (PLAN-sk13a S5): every conflict's support
# holds at some geometry. Proofs only.
#
# A True verdict gives a geometry meaning the sketch less its red
# constraints (lib/solvepf.bend: exists_of). A support has no red member
# (the classes are honest, lib/totalpf.bend: solve_honest; ConflictOk says
# so), so enforcing only the support asks for less, and the same geometry
# means it. solve_honest wants the sketch well formed and covered by its
# variables; the verdict checked both for the sketch with its red
# constraints made driven, and neither check reads the driven flags
# (lib/solvepf.bend: wf_of, cov_of).
#
# Generated from tools/drafts/blamepf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./kinst.bend as KI
import ./listpf.bend as L
import ./nat.bend as LN
import ./plan.bend as PL
import ./cert.bend as CK
import ./wfdec.bend as WF
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./passpf.bend as PS
import ./solve.bend as SO
import ./solvepf.bend as SPF
import ./totalpf.bend as TP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# A support has no red member
# ---------------------------

def hon_len(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls)) -> {SV.clsn(cls) == SV.ncons(sk) : Nat}:
  match h:
    case (a, b):
      a

def hon_go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls)) -> SV.Honest.go(sk, cls, SV.ncons(sk), 0n):
  match h:
    case (a, b):
      b

def go_hd(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +m: Nat, +c0: Nat, h: SV.Honest.go(sk, cls, 1n+m, c0)) -> SV.Fate(sk, cls, c0):
  match h:
    case (a, b):
      a

def go_tl(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +m: Nat, +c0: Nat, h: SV.Honest.go(sk, cls, 1n+m, c0)) -> SV.Honest.go(sk, cls, m, 1n+c0):
  match h:
    case (a, b):
      b

# the k-th fate from c0 on
def fate_at(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c0: Nat, k: Nat, h: SV.Honest.go(sk, cls, n, c0), hk: {KA.natle(1n+k, n) == True{} : Bool}) -> SV.Fate(sk, cls, Nat.add(k, c0)):
  match n k:
    case 0n k:
      absurd(SV.Fate(sk, cls, Nat.add(k, c0)), KA.ft(hk))
    case 1n++m 0n:
      go_hd(sk, cls, m, c0, h)
    case 1n++m 1n++j:
      (%Equal.sym(Nat, 1n+Nat.add(j, c0), Nat.add(j, 1n+c0), LN.add_succ(j, c0)) : SV.Fate(sk, cls, _)
        fate_at(sk, cls, m, 1n+c0, j, go_tl(sk, cls, m, c0, h), hk))

def nin_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, h: SV.ConflictOk(sk, red, c, s)) -> {SV.none_in(s, red) == True{} : Bool}:
  match h:
    case (h1, h2):
      L.band_r(SV.all_driving(sk, s), SV.none_in(s, red), L.band_r(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red)), L.band_r(SV.distinct(s), SV.band(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red))), h1)))

def nin_c(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +cns: List<&2, Nat>, b: Bool, h: SV.Fate.pick(sk, red, ds, c, b, SV.Conflict{s, cns})) -> {SV.none_in(s, red) == True{} : Bool}:
  match b:
    case True{}:
      absurd({SV.none_in(s, red) == True{} : Bool}, h)
    case False{}:
      nin_ok(sk, red, c, s, h)

# a constraint's fate: a conflict, if driving, has a support with no red
# member; the other classes have none
def nin_fate(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, k: SV.Class, b: Bool, h: SV.Fate.pick(sk, red, ds, c, b, k)) -> {SV.none_in(SV.support.of(k), red) == True{} : Bool}:
  match k:
    case SV.Kept{d}:
      {==}
    case SV.Amber{d, r}:
      {==}
    case SV.Over{j, s, w}:
      {==}
    case SV.Conflict{+s, +cns}:
      nin_c(sk, red, ds, c, s, cns, b, h)

# past the last constraint the class is Kept, with no support
def nin_past(cls: List<&2, SV.Class>, c: Nat, +red: List<&2, Nat>, h: {SV.lt(c, SV.clsn(cls)) == False{} : Bool}) -> {SV.none_in(SV.support(cls, c), red) == True{} : Bool}:
  match cls c:
    case Nil{} c:
      {==}
    case Con{y, t} 0n:
      absurd({SV.none_in(SV.support(Con{y, t}, 0n), red) == True{} : Bool}, KA.tf(h))
    case Con{y, t} 1n+m:
      nin_past(t, m, red, h)

def sn.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, b: Bool, e: {SV.lt(c, SV.ncons(sk)) == b : Bool}, H: SV.Honest(sk, cls)) -> {SV.none_in(SV.support(cls, c), SV.reds(cls)) == True{} : Bool}:
  match b:
    case True{}:
      +hk = Equal.trans(Bool, KA.natle(1n+c, SV.ncons(sk)), SV.lt(c, SV.ncons(sk)), True{}, Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), KA.natle(1n+c, SV.ncons(sk)), L.lt_sv(c, SV.ncons(sk))), e)
      nin_fate(sk, SV.reds(cls), SV.dropped(cls), c, SV.class_at(cls, c), SV.driven(sk, c), (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : SV.Fate(sk, cls, _)
        fate_at(sk, cls, SV.ncons(sk), 0n, c, hon_go(sk, cls, H), hk)))
    case False{}:
      nin_past(cls, c, SV.reds(cls), (%Equal.sym(Nat, SV.clsn(cls), SV.ncons(sk), hon_len(sk, cls, H)) : {SV.lt(c, _) == False{} : Bool}
        e))

# an honest classification: no support has a red member
def supp_nin(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, H: SV.Honest(sk, cls)) -> {SV.none_in(SV.support(cls, c), SV.reds(cls)) == True{} : Bool}:
  sn.go(sk, cls, c, SV.lt(c, SV.ncons(sk)), {==}, H)

# Enforcing less
# --------------
# only(S, sk) drives every constraint not in S, mark(R, sk) every one in R:
# with S and R disjoint, the first enforces a part of what the second does


def mo.snd(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, h: SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, False{}, k}, SV.mark.cons(R, t, 1n+i)}), ih: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, t, 1n+i)) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i))) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i)):
  match h:
    case (a, b):
      ih(b)

def mo.tl(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, bR: Bool, h: SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, bR, k}, SV.mark.cons(R, t, 1n+i)}), ih: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, t, 1n+i)) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i))) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i)):
  match bR:
    case True{}:
      ih(h)
    case False{}:
      mo.snd(~F, env, es, S, R, id, k, t, i, h, ih)

def mo.both(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, h: SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, False{}, k}, SV.mark.cons(R, t, 1n+i)}), ih: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, t, 1n+i)) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i))) -> SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, False{}, k}, SV.only.cons(S, t, 1n+i)}):
  match h:
    case (a, b):
      (a, ih(b))

def mo.f(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +hn: {SV.none_in(S, R) == True{} : Bool}, bS: Bool, eS: {SV.mem(i, S) == bS : Bool}, h: SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, SV.mem(i, R), k}, SV.mark.cons(R, t, 1n+i)}), ih: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, t, 1n+i)) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i))) -> SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, SV.bnot(bS), k}, SV.only.cons(S, t, 1n+i)}):
  match bS:
    case False{}:
      mo.tl(~F, env, es, S, R, id, k, t, i, SV.mem(i, R), h, ih)
    case True{}:
      mo.both(~F, env, es, S, R, id, k, t, i, (%PS.nonein_mem(S, R, i, hn, eS) : SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, _, k}, SV.mark.cons(R, t, 1n+i)})
        h), ih)

def mo.rec(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +hn: {SV.none_in(S, R) == True{} : Bool}, dr: Bool, h: SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, SV.bor(dr, SV.mem(i, R)), k}, SV.mark.cons(R, t, 1n+i)}), ih: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, t, 1n+i)) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, t, 1n+i))) -> SK.Sketch.means.cons(~F, env, es, Con{SK.Rec{id, SV.bor(dr, SV.bnot(SV.mem(i, S))), k}, SV.only.cons(S, t, 1n+i)}):
  match dr:
    case True{}:
      ih(h)
    case False{}:
      mo.f(~F, env, es, S, R, id, k, t, i, hn, SV.mem(i, S), {==}, h, ih)

def mo.cons(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +S: List<&2, Nat>, +R: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat, +hn: {SV.none_in(S, R) == True{} : Bool}, h: SK.Sketch.means.cons(~F, env, es, SV.mark.cons(R, cs, i))) -> SK.Sketch.means.cons(~F, env, es, SV.only.cons(S, cs, i)):
  match cs:
    case Nil{}:
      h
    case Con{SK.Rec{+id, dr, +k}, +t}:
      mo.rec(~F, env, es, S, R, id, k, t, i, hn, dr, h, h2 => mo.cons(~F, env, es, S, R, t, 1n+i, hn, h2))

def mo.sk(~F: O.OField, +env: List<&2, O.C(F)>, +S: List<&2, Nat>, +R: List<&2, Nat>, +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +cs: List<&2, SK.Rec>, +hn: {SV.none_in(S, R) == True{} : Bool}, h: SK.Sketch.means(~F, env, SV.mark(R, SK.Sketch{vs, es, cs}))) -> SK.Sketch.means(~F, env, SV.only(S, SK.Sketch{vs, es, cs})):
  match h:
    case (a, b):
      (a, mo.cons(~F, env, es, S, R, cs, 0n, hn, b))

# a geometry meaning the sketch less R means it with only S enforced
def mo(~F: O.OField, +env: List<&2, O.C(F)>, +S: List<&2, Nat>, +R: List<&2, Nat>, sk: SK.Sketch, +hn: {SV.none_in(S, R) == True{} : Bool}, h: SK.Sketch.means(~F, env, SV.mark(R, sk))) -> SK.Sketch.means(~F, env, SV.only(S, sk)):
  match sk:
    case SK.Sketch{+vs, +es, +cs}:
      mo.sk(~F, env, S, R, vs, es, cs, hn, h)

# The law
# -------


def blame_pair(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +c: Nat, +hn: {SV.none_in(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l)))) == True{} : Bool}, s: &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)))) -> &y: M.Vec(~F) -> SK.Sketch.means(~F, y, SV.only(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), sk)):
  match s:
    case (+y, p):
      match p:
        case (hin, hm):
          (y, mo(~F, y, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk, hn, hm))

def solve_blame(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +c: Nat) -> (&x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), sk))):
  +X = SO.solve_l(sk, g0, l)
  +v = SPF.verdict(sk, g0, l, ok)
  hon = TP.solve_honest(sk, SPF.wf_of(sk, g0, X, v), SPF.cov_of(sk, g0, X, v), g0, l)
  blame_pair(~F, ~H, sk, g0, l, c, supp_nin(sk, SO.Out.cls(SO.solve_l(sk, g0, l)), c, hon), SPF.solve_exists(~F, ~R, ~H, sk, g0, l, ok))
