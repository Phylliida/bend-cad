# bend-cad: law 3, solve_blame (PLAN-sk13a S5): every conflict's support
# holds at some geometry. Proofs only.
#
# Since the sk-13b switch (2026-11-02), what this file proved about
# sk-13a's pass, Honest or solver is proven in lib/dsolvepf.bend; what
# is left here is what that proof reuses, and the description below is
# of the sk-13a proof.
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

def absurd(-A: Type, x: Empty) -> A:
  match x:

# A support has no red member
# ---------------------------

# past the last constraint the class is Kept, with no support
def nin_past(cls: List<&2, SV.Class>, c: Nat, +red: List<&2, Nat>, h: {SV.lt(c, SV.clsn(cls)) == False{} : Bool}) -> {SV.none_in(SV.support(cls, c), red) == True{} : Bool}:
  match cls c:
    case Nil{} c:
      {==}
    case Con{y, t} 0n:
      absurd({SV.none_in(SV.support(Con{y, t}, 0n), red) == True{} : Bool}, KA.tf(h))
    case Con{y, t} 1n+m:
      nin_past(t, m, red, h)

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

