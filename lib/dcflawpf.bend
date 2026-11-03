# bend-cad: a conflicting constraint and its support cannot all hold where
# the conflict's nd segments have nonzero length (PLAN-sk13b B6, the draft
# solve_conflict over any honest classification). Proofs only.
#
# The honest class of a driving conflict c with support s has a refutation
# (SV.ConflictOk). A geometry meaning the sketch with only c and s
# enforced satisfies exactly their equations and sides (as
# lib/conflawpf.bend reads only's sketch):
# - a degree-0 refutation has no point (lib/conflawpf.bend: cf_m);
# - a direction refutation's facts are c's and s's equations with their
#   direction statements and no nd (rfacts), so they hold there, and each
#   derivation's conclusion holds where its nd segments are long
#   (lib/dirpf.bend: sound). The refutation's nd is within the conflict's
#   and the segments of the Angles among c and s, which their sides make
#   long (an Angle's dot > 0 is 0 when either segment has length 0). Then:
#   - a Motzkin refutation's K facts are zeros with the sides, which have
#     no point (lib/vsdpf.bend: refute_at);
#   - a collapse makes a long segment's squared length 0;
#   - an Angle's collapsed segment makes its side dot > 0 equal 0.
#
# Generated from tools/drafts/dcflawpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./fring.bend as FR
import ./ford.bend as FO
import ./dirpf.bend as DP
import ./meaning.bend as MN
import ./vsdpf.bend as VS
import ./ckpf.bend as CKP
import ./conflictpf.bend as CFP
import ./conflawpf.bend as CF
import ./dfactpf.bend as DFC


def absurd(-A: Type, x: Empty) -> A:
  match x:

# The Fate at c
# -------------

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

def hon_len(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls)) -> {SV.clsn(cls) == SV.ncons(sk) : Nat}:
  match h:
    case (a, b):
      a

def hon_go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls)) -> SV.Honest.go(sk, cls, SV.ncons(sk), 0n):
  match h:
    case (a, b):
      b

# The facts of c and s hold
# -------------------------

# an equation of one of cs holds as a fact with no nd, its constraint's
# direction statement holding with it
def rf_ok.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cs: List<&2, Nat>, +e: E.QExpr, +t: List<&2, E.QExpr>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +hz: SK.Zeros(~F, x, SV.solved.pick(b, e, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k))),
  ih: SK.Zeros(~F, x, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k)) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(t, SV.owners(sk), cs, sk, Nil{}, False{}, 1n+k)))
  -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.pick(b, DR.Fact{e, SV.fnd.pick(False{}, Nil{}, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))}, SV.facts.go(t, SV.owners(sk), cs, sk, Nil{}, False{}, 1n+k))):
  match b:
    case True{}:
      +ze = DP.fst({O.eval(~F, x, e) == O.zero(F) : O.C(F)}, SK.Zeros(~F, x, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k)), hz)
      (Inr{(ze, DFC.stat_at(~F, x, sk, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq)) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        ze)))}, ih(DP.snd({O.eval(~F, x, e) == O.zero(F) : O.C(F)}, SK.Zeros(~F, x, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k)), hz)))
    case False{}:
      ih(hz)

def rf_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cs: List<&2, Nat>, es: List<&2, E.QExpr>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}, hz: SK.Zeros(~F, x, SV.eqs_of.go(es, SV.owners(sk), cs, k))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(es, SV.owners(sk), cs, sk, Nil{}, False{}, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      rf_ok.c(~F, SV.mem(SV.nth(SV.owners(sk), k), cs), x, sk, cs, e, t, k, hq, hz, z => rf_ok(~F, x, sk, cs, t, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), z))

# where the equations of cs hold, so do their facts
def rf_all(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cs: List<&2, Nat>, hz: SK.Zeros(~F, x, SV.eqs_of(sk, cs))) -> DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, cs)):
  rf_ok(~F, x, sk, cs, SK.Sketch.eqs(sk), 0n, {==}, hz)

# An Angle's side
# ---------------


# the side's dot is 0 where the first segment has length 0
def dot0_a(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, h1: {DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))) == O.zero(F) : O.C(F)}, h2: {DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))) == O.zero(F) : O.C(F)}) -> {DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra)))), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a)))), DP.rev_x(~F, env, SK.seg(es, a), ra)) : {O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), _), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), _), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))))) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a)))), DP.rev_y(~F, env, SK.seg(es, a), ra)) : {O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, DP.ev(~F, env, s), _)), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, DP.ev(~F, env, c), _)), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))))) == O.zero(F) : O.C(F)}
  FO.cert2(~F, O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, DP.ev(~F, env, s), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a)))))), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))))), O.mul(F, DP.ev(~F, env, c), O.mul(F, DP.rsign(~F, ra), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a)))))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))))),
    O.mul(F, DP.rsign(~F, ra), O.add(F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb))))))), DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))), O.mul(F, DP.rsign(~F, ra), O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb))))))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))),
    FR.fring_eq(~F, [DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))), DP.ev(~F, env, c), DP.ev(~F, env, s), DP.rsign(~F, ra)],
      E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{6n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{6n}, E.ZVar{1n}}}}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{6n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{6n}, E.ZVar{1n}}}}, E.ZVar{3n}}},
      E.ZAdd{E.ZMul{E.ZMul{E.ZVar{6n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZVar{5n}, E.ZVar{3n}}}}, E.ZVar{0n}}, E.ZMul{E.ZMul{E.ZVar{6n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{2n}}}}, E.ZVar{1n}}}, {==}),
    h1, h2)

# and where the second has length 0
def dot0_b(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, h1: {DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))) == O.zero(F) : O.C(F)}, h2: {DP.ev(~F, env, SK.VE.y(DR.zseg(es, b))) == O.zero(F) : O.C(F)}) -> {DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, b, rb)))), O.mul(F, DP.rsign(~F, rb), DP.ev(~F, env, SK.VE.x(DR.zseg(es, b)))), DP.rev_x(~F, env, SK.seg(es, b), rb)) : {O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), _), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))))) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, b, rb)))), O.mul(F, DP.rsign(~F, rb), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b)))), DP.rev_y(~F, env, SK.seg(es, b), rb)) : {O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), O.mul(F, DP.rsign(~F, rb), DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), _)) == O.zero(F) : O.C(F)}
  FO.cert2(~F, O.add(F, O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), O.mul(F, DP.rsign(~F, rb), DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), O.mul(F, DP.rsign(~F, rb), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b)))))), O.mul(F, O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.rsign(~F, rb)), DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))), O.mul(F, O.add(F, O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.rsign(~F, rb)), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b))),
    FR.fring_eq(~F, [DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b))), O.sub(~F, O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), O.add(F, O.mul(F, DP.ev(~F, env, s), DP.ev(~F, env, SK.VE.x(SK.Seg.dir(SK.dseg(es, a, ra))))), O.mul(F, DP.ev(~F, env, c), DP.ev(~F, env, SK.VE.y(SK.Seg.dir(SK.dseg(es, a, ra)))))), DP.rsign(~F, rb)],
      E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZMul{E.ZVar{4n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}},
      E.ZAdd{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZVar{0n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{1n}}}, {==}),
    h1, h2)

# a^2 + b^2 = 0 gives b = 0
def sumsq_zero2(~F: O.OField, +a: O.C(F), +b: O.C(F), +h: {O.add(F, O.mul(F, a, a), O.mul(F, b, b)) == O.zero(F) : O.C(F)}) -> {b == O.zero(F) : O.C(F)}:
  FO.sumsq_zero(~F, b, a, Equal.trans(O.C(F), O.add(F, O.mul(F, b, b), O.mul(F, a, a)), O.add(F, O.mul(F, a, a), O.mul(F, b, b)), O.zero(F),
    FR.fring_eq(~F, [a, b], E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{0n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, {==}), h))

def long_a.c(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, hp: O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb))))), d: DP.DOr(DR.Long(~F, env, es, a), {DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, a))) == O.zero(F) : O.C(F)})) -> DR.Long(~F, env, es, a):
  match d:
    case Inl{l}:
      l
    case Inr{+e}:
      absurd(DR.Long(~F, env, es, a), FO.ne_of_lt(~F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), hp, Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), O.zero(F), dot0_a(~F, env, es, a, ra, b, rb, c, s, FO.sumsq_zero(~F, DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))), e), sumsq_zero2(~F, DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))), e)))))

def long_b.c(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, hp: O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb))))), d: DP.DOr(DR.Long(~F, env, es, b), {DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, b))) == O.zero(F) : O.C(F)})) -> DR.Long(~F, env, es, b):
  match d:
    case Inl{l}:
      l
    case Inr{+e}:
      absurd(DR.Long(~F, env, es, b), FO.ne_of_lt(~F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), hp, Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), O.zero(F), dot0_b(~F, env, es, a, ra, b, rb, c, s, FO.sumsq_zero(~F, DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b))), e), sumsq_zero2(~F, DP.ev(~F, env, SK.VE.x(DR.zseg(es, b))), DP.ev(~F, env, SK.VE.y(DR.zseg(es, b))), e)))))

# the side makes both segments long
def long_ab(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, +hp: O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))))) -> DR.Longs(~F, env, es, [a, b]):
  (long_a.c(~F, env, es, a, ra, b, rb, c, s, hp, DFC.ls_seg(~F, env, es, a)), (long_b.c(~F, env, es, a, ra, b, rb, c, s, hp, DFC.ls_seg(~F, env, es, b)), Unit{}))

# The sides of a constraint among c and s
# ---------------------------------------

# the sides of the constraint m, if any
def KSides(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, SK.Constraint>) -> Data:
  match m:
    case Some{+k}:
      SK.Sides(~F, env, SK.Constraint.sides(es, k))
    case None{}:
      Unit

def sp_l(~F: O.OField, b: Bool, +env: List<&2, O.C(F)>, xs: List<&2, SK.Side>, +rest: List<&2, SK.Side>, eb: {b == True{} : Bool}, +h: SK.Sides(~F, env, SV.csides.pick(b, xs, rest))) -> SK.Sides(~F, env, xs):
  match b:
    case True{}:
      MN.sides_l(~F, env, xs, rest, h)
    case False{}:
      absurd(SK.Sides(~F, env, xs), KA.ft(eb))

def sp_r(~F: O.OField, b: Bool, +env: List<&2, O.C(F)>, xs: List<&2, SK.Side>, +rest: List<&2, SK.Side>, +h: SK.Sides(~F, env, SV.csides.pick(b, xs, rest))) -> SK.Sides(~F, env, rest):
  match b:
    case True{}:
      MN.sides_r(~F, env, xs, rest, h)
    case False{}:
      h

def sides_hd(~F: O.OField, dr: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +cs: List<&2, Nat>, +i: Nat, hd: {dr == False{} : Bool}, hm: {SV.mem(i, cs) == True{} : Bool}, +hs: SK.Sides(~F, env, SV.csides.go(es, Con{SK.Rec{id, dr, k}, t}, cs, i)))
  -> SK.Sides(~F, env, SK.Constraint.sides(es, k)):
  match dr:
    case True{}:
      absurd(SK.Sides(~F, env, SK.Constraint.sides(es, k)), KA.tf(hd))
    case False{}:
      sp_l(~F, SV.mem(i, cs), env, SK.Constraint.sides(es, k), SV.csides.go(es, t, cs, 1n+i), hm, hs)

def sides_tl(~F: O.OField, dr: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +cs: List<&2, Nat>, +i: Nat, +hs: SK.Sides(~F, env, SV.csides.go(es, Con{SK.Rec{id, dr, k}, t}, cs, i)))
  -> SK.Sides(~F, env, SV.csides.go(es, t, cs, 1n+i)):
  match dr:
    case True{}:
      hs
    case False{}:
      sp_r(~F, SV.mem(i, cs), env, SK.Constraint.sides(es, k), SV.csides.go(es, t, cs, 1n+i), hs)

# the driving record m of rs (from position i), one of cs: its sides are
# among cs's
def sides_at(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, rs: List<&2, SK.Rec>, +cs: List<&2, Nat>, +i: Nat, m: Nat, hm: {SV.mem(Nat.add(m, i), cs) == True{} : Bool}, hd: {SV.driven.at(rs, m) == False{} : Bool}, +hs: SK.Sides(~F, env, SV.csides.go(es, rs, cs, i)))
  -> KSides(~F, env, es, SV.rec_at(rs, m)):
  match rs m:
    case Nil{} m:
      absurd(KSides(~F, env, es, None{}), KA.tf(hd))
    case Con{SK.Rec{+id, dr, +k}, +t} 0n:
      sides_hd(~F, dr, env, es, id, k, t, cs, i, hd, hm, hs)
    case Con{SK.Rec{+id, dr, +k}, +t} 1n++q:
      sides_at(~F, env, es, t, cs, 1n+i, q, (%LN.add_succ(q, i) : {SV.mem(_, cs) == True{} : Bool}
        hm), hd, sides_tl(~F, dr, env, es, id, k, t, cs, i, hs))

def sides_of(~F: O.OField, +x: M.Vec(~F), sk: SK.Sketch, +cs: List<&2, Nat>, +p: Nat, hm: {SV.mem(p, cs) == True{} : Bool}, hd: {SV.driven(sk, p) == False{} : Bool}, +hs: SK.Sides(~F, x, SV.csides(sk, cs))) -> KSides(~F, x, SV.ents(sk), SV.kind_at(sk, p)):
  match sk:
    case SK.Sketch{+vs, +es, +rs}:
      sides_at(~F, x, es, rs, cs, 0n, p, (%LN.add_zero(p) : {SV.mem(_, cs) == True{} : Bool}
        hm), hd, hs)

# a driving constraint is not driven
def drv_f(+sk: SK.Sketch, +p: Nat, h: {SV.driving(sk, p) == True{} : Bool}) -> {SV.driven(sk, p) == False{} : Bool}:
  LI.bnot_f(SV.driven(sk, p), LI.band_r(SV.lt(p, SV.ncons(sk)), SV.bnot(SV.driven(sk, p)), h))

def drv_mem.c(b: Bool, +sk: SK.Sketch, +p: Nat, +q: Nat, +t: List<&2, Nat>, eb: {SV.eq(p, q) == b : Bool}, +had: {SV.all_driving(sk, Con{q, t}) == True{} : Bool}, hm: {SV.bor(b, SV.mem(p, t)) == True{} : Bool},
  ih: {SV.mem(p, t) == True{} : Bool} -> {SV.driven(sk, p) == False{} : Bool}) -> {SV.driven(sk, p) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, p, q, LI.eq_ok(p, q, eb)) : {SV.driven(sk, _) == False{} : Bool}
      drv_f(sk, q, LI.band_l(SV.driving(sk, q), SV.all_driving(sk, t), had))
    case False{}:
      ih(hm)

# a member of all driving constraints is driving
def drv_mem(+sk: SK.Sketch, +p: Nat, cs: List<&2, Nat>, +had: {SV.all_driving(sk, cs) == True{} : Bool}, hm: {SV.mem(p, cs) == True{} : Bool}) -> {SV.driven(sk, p) == False{} : Bool}:
  match cs:
    case Nil{}:
      absurd({SV.driven(sk, p) == False{} : Bool}, KA.ft(hm))
    case Con{+q, +t}:
      drv_mem.c(SV.eq(p, q), sk, p, q, t, {==}, had, hm, h => drv_mem(sk, p, t, LI.band_r(SV.driving(sk, q), SV.all_driving(sk, t), had), h))

# The Angles' segments are long
# -----------------------------

def aa_of.k(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, +hs: SK.Sides(~F, env, SK.Constraint.sides(es, k))) -> DR.Longs(~F, env, es, SV.angle_args.of(Some{k})):
  match k:
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      long_ab(~F, env, es, a, ra, b, rb, c, s, DP.fst(O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb))))), Unit, hs))
    case SK.Coincident{x1, x2}:
      Unit{}
    case SK.Horizontal{x1, x2}:
      Unit{}
    case SK.Vertical{x1, x2}:
      Unit{}
    case SK.Concentric{x1, x2}:
      Unit{}
    case SK.EqualRadius{x1, x2}:
      Unit{}
    case SK.Fix{x1, x2}:
      Unit{}
    case SK.Distance{x1, x2, x3}:
      Unit{}
    case SK.HDistance{x1, x2, x3}:
      Unit{}
    case SK.VDistance{x1, x2, x3}:
      Unit{}
    case SK.Radius{x1, x2}:
      Unit{}
    case SK.Diameter{x1, x2}:
      Unit{}
    case SK.LineDistance{x1, x2, x3, x4, x5}:
      Unit{}
    case SK.EqualLength{x1, x2}:
      Unit{}
    case SK.Perpendicular{x1, x2}:
      Unit{}
    case SK.Parallel{x1, x2}:
      Unit{}
    case SK.OnLine{x1, x2}:
      Unit{}
    case SK.OnCircle{x1, x2}:
      Unit{}
    case SK.Midpoint{x1, x2}:
      Unit{}
    case SK.Symmetric{x1, x2, x3}:
      Unit{}

def aa_of(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, SK.Constraint>, +hs: KSides(~F, env, es, m)) -> DR.Longs(~F, env, es, SV.angle_args.of(m)):
  match m:
    case Some{+k}:
      aa_of.k(~F, env, es, k, hs)
    case None{}:
      Unit{}

def longs_join(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, xs: List<&2, Nat>, +ys: List<&2, Nat>, +ha: DR.Longs(~F, env, es, xs), +hb: DR.Longs(~F, env, es, ys)) -> DR.Longs(~F, env, es, SV.cat(xs, ys)):
  match xs:
    case Nil{}:
      hb
    case Con{+p, +t}:
      (DP.fst(DR.Long(~F, env, es, p), DR.Longs(~F, env, es, t), ha), longs_join(~F, env, es, t, ys, DP.snd(DR.Long(~F, env, es, p), DR.Longs(~F, env, es, t), ha), hb))

# the segments of the Angles among cs (within S, whose sides hold) are long
def aa_longs(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +S: List<&2, Nat>, cs: List<&2, Nat>, +hsub: {SV.sub(cs, S) == True{} : Bool}, +had: {SV.all_driving(sk, cs) == True{} : Bool}, +hs: SK.Sides(~F, x, SV.csides(sk, S))) -> DR.Longs(~F, x, SV.ents(sk), SV.angle_args(sk, cs)):
  match cs:
    case Nil{}:
      Unit{}
    case Con{+p, +t}:
      longs_join(~F, x, SV.ents(sk), SV.angle_args.of(SV.kind_at(sk, p)), SV.angle_args(sk, t),
        aa_of(~F, x, SV.ents(sk), SV.kind_at(sk, p), sides_of(~F, x, sk, S, p, LI.band_l(SV.mem(p, S), SV.sub(t, S), hsub), drv_f(sk, p, LI.band_l(SV.driving(sk, p), SV.all_driving(sk, t), had)), hs)),
        aa_longs(~F, x, sk, S, t, LI.band_r(SV.mem(p, S), SV.sub(t, S), hsub), LI.band_r(SV.driving(sk, p), SV.all_driving(sk, t), had), hs))

# The three direction refutations have no point
# ---------------------------------------------


def kz(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, env, es, fs), +d: DR.Der, hv: DR.Valid(es, fs, ctx, d), k: DR.IsK(DR.concl(es, fs, d)), +hl: DR.Longs(~F, env, es, DR.nd(es, fs, d))) -> {DP.ev(~F, env, DR.Jd.e(DR.concl(es, fs, d))) == O.zero(F) : O.C(F)}:
  DP.kval(~F, env, es, DR.concl(es, fs, d), k, DP.sound(~F, env, es, fs, ctx, af, d, hv, hl))

# a Motzkin refutation's K facts are zeros where their nd is long
def mz_zeros(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, env, es, fs), ds: List<&2, DR.Der>, hv: DR.AllValidK(es, fs, ctx, ds), +hl: DR.Longs(~F, env, es, DR.nds(es, fs, ds))) -> SK.Zeros(~F, env, DR.dconcls(es, fs, ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +t}:
      (v, q) = hv
      (k, r) = q
      +lc = DP.longs_cat(~F, env, es, DR.nd(es, fs, d), DR.nds(es, fs, t), hl)
      (kz(~F, env, es, fs, ctx, af, d, v, k, DP.fst(DR.Longs(~F, env, es, DR.nd(es, fs, d)), DR.Longs(~F, env, es, DR.nds(es, fs, t)), lc)), mz_zeros(~F, env, es, fs, ctx, af, t, r, DP.snd(DR.Longs(~F, env, es, DR.nd(es, fs, d)), DR.Longs(~F, env, es, DR.nds(es, fs, t)), lc)))


# a collapse makes a long segment's squared length 0
def coll(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, env, es, fs), +dr: DR.Der, +di: DR.Der, +s: Nat, hr: DR.RefColl(es, fs, ctx, dr, di, s), +hl: DR.Longs(~F, env, es, Con{s, DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di))})) -> Empty:
  (v1, q1) = hr
  (v2, q2) = q1
  (k1, q3) = q2
  (k2, q4) = q3
  (sr, q5) = q4
  (si, op) = q5
  +lc = DP.longs_cat(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), DP.snd(DR.Long(~F, env, es, s), DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di))), hl))
  +zx = DP.k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zseg(es, s)), sr, kz(~F, env, es, fs, ctx, af, dr, v1, k1, DP.fst(DR.Longs(~F, env, es, DR.nd(es, fs, dr)), DR.Longs(~F, env, es, DR.nd(es, fs, di)), lc)))
  +zy = DP.k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zseg(es, s)), si, kz(~F, env, es, fs, ctx, af, di, v2, k2, DP.snd(DR.Longs(~F, env, es, DR.nd(es, fs, dr)), DR.Longs(~F, env, es, DR.nd(es, fs, di)), lc)))
  +x1 = DP.ev(~F, env, SK.VE.x(DR.zseg(es, s)))
  +y1 = DP.ev(~F, env, SK.VE.y(DR.zseg(es, s)))
  FO.ne_of_lt(~F, O.zero(F), DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))), DP.fst(DR.Long(~F, env, es, s), DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di))), hl), Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))), O.zero(F), FO.cert2(~F, DP.ev(~F, env, SK.VE.norm2(DR.zseg(es, s))), x1, x1, y1, y1, {==}, zx, zy)))

# a collapsed Angle segment's direction is 0
def AZ(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, m: Maybe<&2, Nat>) -> Data:
  match m:
    case Some{+a}:
      SK.Both({DP.ev(~F, env, SK.VE.x(DR.zseg(es, a))) == O.zero(F) : O.C(F)}, {DP.ev(~F, env, SK.VE.y(DR.zseg(es, a))) == O.zero(F) : O.C(F)})
    case None{}:
      {False{} == True{} : Bool}

def az_of(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +dr: DR.Der, +di: DR.Der, m: Maybe<&2, Nat>, ac: DR.AngleColl(es, fs, dr, di, m), +zr: {DP.ev(~F, env, DR.Jd.e(DR.concl(es, fs, dr))) == O.zero(F) : O.C(F)}, +zi: {DP.ev(~F, env, DR.Jd.e(DR.concl(es, fs, di))) == O.zero(F) : O.C(F)}) -> AZ(~F, env, es, m):
  match m:
    case Some{+a}:
      (sr, si) = ac
      (DP.k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, dr)), SK.VE.x(DR.zseg(es, a)), sr, zr), DP.k_tr(~F, env, DR.Jd.e(DR.concl(es, fs, di)), SK.VE.y(DR.zseg(es, a)), si, zi))
    case None{}:
      absurd(AZ(~F, env, es, None{}), ac)

def ang_f(~F: O.OField, fst: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, +c: E.QExpr, +s: E.QExpr, hz: AZ(~F, env, es, DR.angle_seg(SK.Angle{a, ra, b, rb, c, s}, fst)), +hp: O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))))) -> Empty:
  match fst:
    case True{}:
      (z1, z2) = hz
      FO.ne_of_lt(~F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), hp, Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), O.zero(F), dot0_a(~F, env, es, a, ra, b, rb, c, s, z1, z2)))
    case False{}:
      (z1, z2) = hz
      FO.ne_of_lt(~F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), hp, Equal.sym(O.C(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb)))), O.zero(F), dot0_b(~F, env, es, a, ra, b, rb, c, s, z1, z2)))

# a collapsed segment of an Angle makes its side's dot 0
def ang_k(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, +fst: Bool, hz: AZ(~F, env, es, DR.angle_seg(k, fst)), +hs: SK.Sides(~F, env, SK.Constraint.sides(es, k))) -> Empty:
  match k:
    case SK.Angle{+a, +ra, +b, +rb, +c, +s}:
      ang_f(~F, fst, env, es, a, ra, b, rb, c, s, hz, DP.fst(O.lt(F, O.zero(F), DP.ev(~F, env, SK.VE.dot(SK.VE.rot(c, s, SK.Seg.dir(SK.dseg(es, a, ra))), SK.Seg.dir(SK.dseg(es, b, rb))))), Unit, hs))
    case SK.Coincident{x1, x2}:
      KA.ft(hz)
    case SK.Horizontal{x1, x2}:
      KA.ft(hz)
    case SK.Vertical{x1, x2}:
      KA.ft(hz)
    case SK.Concentric{x1, x2}:
      KA.ft(hz)
    case SK.EqualRadius{x1, x2}:
      KA.ft(hz)
    case SK.Fix{x1, x2}:
      KA.ft(hz)
    case SK.Distance{x1, x2, x3}:
      KA.ft(hz)
    case SK.HDistance{x1, x2, x3}:
      KA.ft(hz)
    case SK.VDistance{x1, x2, x3}:
      KA.ft(hz)
    case SK.Radius{x1, x2}:
      KA.ft(hz)
    case SK.Diameter{x1, x2}:
      KA.ft(hz)
    case SK.LineDistance{x1, x2, x3, x4, x5}:
      KA.ft(hz)
    case SK.EqualLength{x1, x2}:
      KA.ft(hz)
    case SK.Perpendicular{x1, x2}:
      KA.ft(hz)
    case SK.Parallel{x1, x2}:
      KA.ft(hz)
    case SK.OnLine{x1, x2}:
      KA.ft(hz)
    case SK.OnCircle{x1, x2}:
      KA.ft(hz)
    case SK.Midpoint{x1, x2}:
      KA.ft(hz)
    case SK.Symmetric{x1, x2, x3}:
      KA.ft(hz)

def ang_ref(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, env, es, fs), +dr: DR.Der, +di: DR.Der, +k: SK.Constraint, +fst: Bool, hr: DR.RefAngle(es, fs, ctx, dr, di, k, fst), +hs: SK.Sides(~F, env, SK.Constraint.sides(es, k)), +hl: DR.Longs(~F, env, es, DR.ncat(DR.nd(es, fs, dr), DR.nd(es, fs, di)))) -> Empty:
  (v1, q1) = hr
  (v2, q2) = q1
  (k1, q3) = q2
  (k2, ac) = q3
  ang_k(~F, env, es, k, fst, az_of(~F, env, es, fs, dr, di, DR.angle_seg(k, fst), ac, kz(~F, env, es, fs, ctx, af, dr, v1, k1, DP.fst(DR.Longs(~F, env, es, DR.nd(es, fs, dr)), DR.Longs(~F, env, es, DR.nd(es, fs, di)), DP.longs_cat(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), hl))), kz(~F, env, es, fs, ctx, af, di, v2, k2, DP.snd(DR.Longs(~F, env, es, DR.nd(es, fs, dr)), DR.Longs(~F, env, es, DR.nd(es, fs, di)), DP.longs_cat(~F, env, es, DR.nd(es, fs, dr), DR.nd(es, fs, di), hl)))), hs)

# The conflict's direction refutation
# -----------------------------------


def ang_m(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, +dr: DR.Der, +di: DR.Der, m: Maybe<&2, SK.Constraint>, +fst: Bool, ra: SV.RefAngle.at(sk, c, s, cx, dr, di, m, fst), +hks: KSides(~F, x, SV.ents(sk), m), +hl: DR.Longs(~F, x, SV.ents(sk), DR.ncat(DR.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), dr), DR.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), di)))) -> Empty:
  match m:
    case Some{+k}:
      ang_ref(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s}), cx, af, dr, di, k, fst, ra, hks, hl)
    case None{}:
      ra

def ang_p(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, +dr: DR.Der, +di: DR.Der, +p: Nat, +fst: Bool, ro: {SV.mem(p, Con{c, s}) == True{} : Bool} & SV.RefAngle.at(sk, c, s, cx, dr, di, SV.kind_at(sk, p), fst), +hl: DR.Longs(~F, x, SV.ents(sk), DR.ncat(DR.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), dr), DR.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), di)))) -> Empty:
  match ro:
    case (+hm, ra):
      ang_m(~F, x, sk, c, s, cx, af, hss, hcs, had, dr, di, SV.kind_at(sk, p), fst, ra, sides_of(~F, x, sk, Con{c, s}, p, hm, drv_mem(sk, p, Con{c, s}, had, hm), hcs), hl)

def motz(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, +ds: List<&2, DR.Der>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, hr: DR.AllValidK(SV.ents(sk), SV.rfacts(sk, Con{c, s}), cx, ds) & SV.Refutes0(DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, s}), ds), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), ls, ms, k), +hl: DR.Longs(~F, x, SV.ents(sk), DR.nds(SV.ents(sk), SV.rfacts(sk, Con{c, s}), ds))) -> Empty:
  (hv, hz) = hr
  VS.refute_at(~F, x, DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, s}), ds), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), SV.Ref{ls, ms, k}, CKP.ref_of(DR.dconcls(SV.ents(sk), SV.rfacts(sk, Con{c, s}), ds), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), ls, ms, k, hz), mz_zeros(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s}), cx, af, ds, hv, hl), hss)

# a direction refutation of c and s has no point where its nd is long
def ref_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, r: DR.DRef, ro: SV.RefOk(sk, c, s, cx, r), +hl: DR.Longs(~F, x, SV.ents(sk), DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r))) -> Empty:
  match r:
    case DR.RMotz{+ds, +ls, +ms, +k}:
      motz(~F, x, sk, c, s, cx, af, hss, hcs, had, ds, ls, ms, k, ro, hl)
    case DR.RColl{+dr, +di, +sg}:
      coll(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s}), cx, af, dr, di, sg, ro, hl)
    case DR.RAngle{+dr, +di, +p, +fst}:
      ang_p(~F, x, sk, c, s, cx, af, hss, hcs, had, dr, di, p, fst, ro, hl)


def dref.r(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, +nd: List<&2, Nat>, +r: DR.DRef, q: SV.RefOk(sk, c, s, cx, r) & ({SV.sub(DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r), SV.cat(nd, SV.angle_args(sk, Con{c, s}))) == True{} : Bool} & {SV.sub(nd, DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r)) == True{} : Bool}), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  match q:
    case (ro, hn):
      (+hsub, hin) = hn
      ref_ok(~F, x, sk, c, s, cx, af, hss, hcs, had, r, ro, DFC.longs_sub(~F, x, SV.ents(sk), DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r), SV.cat(nd, SV.angle_args(sk, Con{c, s})), hsub, longs_join(~F, x, SV.ents(sk), nd, SV.angle_args(sk, Con{c, s}), hl, aa_longs(~F, x, sk, Con{c, s}, Con{c, s}, CFP.sub_refl(Con{c, s}), had, hcs))))

def dref(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.rfacts(sk, Con{c, s})), +hss: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk))), +hcs: SK.Sides(~F, x, SV.csides(sk, Con{c, s})), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, +nd: List<&2, Nat>, h: SV.DirRefutes(sk, c, s, cx, nd), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  match h:
    case (+r, q):
      dref.r(~F, x, sk, c, s, cx, af, hss, hcs, had, nd, r, q, hl)

# The conflict law
# ----------------

# c, driving, and its support are all driving
def ad_cs(+sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +hlt: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}, +edr: {SV.driven(sk, c) == False{} : Bool}, +hads: {SV.all_driving(sk, s) == True{} : Bool}) -> {SV.all_driving(sk, Con{c, s}) == True{} : Bool}:
  %Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), True{}, hlt) : {SV.band(SV.band(_, SV.bnot(SV.driven(sk, c))), SV.all_driving(sk, s)) == True{} : Bool}
  %Equal.sym(Bool, SV.driven(sk, c), False{}, edr) : {SV.band(SV.band(True{}, SV.bnot(_)), SV.all_driving(sk, s)) == True{} : Bool}
  %Equal.sym(Bool, SV.all_driving(sk, s), True{}, hads) : {SV.band(SV.band(True{}, SV.bnot(False{})), _) == True{} : Bool}
  {==}

# x meets c's and s's equations and sides: no direction refutation
def cl_dir(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +nd: List<&2, Nat>, h: SV.DirRefutes(sk, c, s, cx, nd), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk)), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  match m:
    case (hz, hs):
      +ho = CF.os_sides(~F, x, sk, Con{c, s}, hs)
      +hss = MN.sides_cat(~F, x, SV.csides(sk, Con{c, s}), SV.esides(sk), MN.sides_r(~F, x, SK.Sketch.sides.ents(SV.ents(sk)), SV.csides(sk, Con{c, s}), ho),
        CF.esides_of(~F, x, sk, MN.sides_l(~F, x, SK.Sketch.sides.ents(SV.ents(sk)), SV.csides(sk, Con{c, s}), ho)))
      dref(~F, x, sk, c, s, cx, rf_all(~F, x, sk, Con{c, s}, (%CF.only_eqs(sk, Con{c, s}) : SK.Zeros(~F, x, _)
        hz)), hss, MN.sides_l(~F, x, SV.csides(sk, Con{c, s}), SV.esides(sk), hss), had, nd, h, hl)

def cl_or(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>, +nd: List<&2, Nat>, h: Or(SV.Ref0(sk, c, s) & {nd == Nil{} : List<&2, Nat>}, SV.DirRefutes(sk, c, s, cx, nd)), +had: {SV.all_driving(sk, Con{c, s}) == True{} : Bool}, m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk)), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  match h:
    case Inl{q}:
      (r0, hn) = q
      CF.cf_m(~F, x, sk, c, s, r0, m)
    case Inr{rd}:
      cl_dir(~F, x, sk, c, s, cx, nd, rd, had, m, hl)

def cl_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, h: SV.ConflictOk(sk, red, c, s, nd), +hlt: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}, +edr: {SV.driven(sk, c) == False{} : Bool}, m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk)), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  (h1, h2) = h
  (hor, hmin) = h2
  cl_or(~F, x, sk, c, s, SV.ctx(sk, red, c), nd, hor, ad_cs(sk, c, s, hlt, edr, LI.band_l(SV.all_driving(sk, s), SV.none_in(s, red), LI.band_r(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red)), LI.band_r(SV.distinct(s), SV.band(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red))), h1)))), m, hl)

def cl_b(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +eb: {SV.driven(sk, c) == b : Bool}, +hlt: {SV.lt(c, SV.ncons(sk)) == True{} : Bool}, f: SV.Fate.pick(sk, cls, SV.reds(cls), SV.dropped(cls), c, b, SV.Conflict{s, nd}), m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk)), +hl: DR.Longs(~F, x, SV.ents(sk), nd)) -> Empty:
  match b:
    case True{}:
      f
    case False{}:
      cl_ok(~F, x, sk, SV.reds(cls), c, s, nd, f, hlt, eb, m, hl)

# c's fate, c a conflict
def cl_k(~F: O.OField, k: SV.Class, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, f: SV.Fate.pick(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.driven(sk, c), k), hc: {SV.is_conflict(k) == True{} : Bool}, +hlt: {SV.lt(c, SV.ncons(sk)) == True{} : Bool},
  m: SK.Sketch.holds(~F, x, SV.only(Con{c, SV.support.of(k)}, sk)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd.of(k))) -> Empty:
  match k:
    case SV.Kept{d}:
      KA.ft(hc)
    case SV.Amber{d, r}:
      KA.ft(hc)
    case SV.Over{j, s, w}:
      KA.ft(hc)
    case SV.Conflict{+s, +nd}:
      cl_b(~F, SV.driven(sk, c), x, sk, cls, c, s, nd, {==}, hlt, f, m, hl)

def cl_go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, b: Bool, +e: {SV.lt(c, SV.ncons(sk)) == b : Bool}, H: SV.Honest(sk, cls), hc: {SV.is_conflict(SV.class_at(cls, c)) == True{} : Bool},
  m: SK.Sketch.holds(~F, x, SV.only(Con{c, SV.support(cls, c)}, sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(cls, c))) -> Empty:
  match b:
    case True{}:
      +hk = Equal.trans(Bool, KA.natle(1n+c, SV.ncons(sk)), SV.lt(c, SV.ncons(sk)), True{}, Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), KA.natle(1n+c, SV.ncons(sk)), LI.lt_sv(c, SV.ncons(sk))), e)
      cl_k(~F, SV.class_at(cls, c), x, sk, cls, c, (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : SV.Fate(sk, cls, _)
        fate_at(sk, cls, SV.ncons(sk), 0n, c, hon_go(sk, cls, H), hk)), hc, e, m, hl)
    case False{}:
      CF.cf_past(cls, c, (%Equal.sym(Nat, SV.clsn(cls), SV.ncons(sk), hon_len(sk, cls, H)) : {SV.lt(c, _) == False{} : Bool}
        e), hc)

# THE DRAFT LAW (solve_conflict over the extended Honest): in every
# ordered field, a conflicting constraint and its support cannot all hold
# where the conflict's nd segments have nonzero length
def conflict_law(~F: O.OField, +sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls), +c: Nat, hc: {SV.is_conflict(SV.class_at(cls, c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(cls, c)}, sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(cls, c))) -> Empty:
  cl_go(~F, x, sk, cls, c, SV.lt(c, SV.ncons(sk)), {==}, h, hc, MN.sketch_complete(~F, x, SV.only(Con{c, SV.support(cls, c)}, sk), m), hl)
