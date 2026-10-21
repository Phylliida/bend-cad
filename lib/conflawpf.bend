# bend-cad: law 8, solve_conflict (PLAN-sk13a S6): in every ordered field,
# a conflicting constraint and its support cannot all hold. Proofs only.
#
# The classes are honest (lib/totalpf.bend: solve_honest), so a driving
# conflict c with support s has a degree-0 refutation of the equations of
# c and s with their side conditions and the entities' (ConflictOk). A
# geometry meaning the sketch with only c and s enforced satisfies exactly
# those equations and sides (eqs_of, csides: the spec's lists, read off
# only's sketch below), and a refutation has no point in any ordered field
# (lib/vsdpf.bend: refute_at).
#
# Generated from tools/drafts/conflawpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./listpf.bend as L
import ./nat.bend as LN
import ./meaning.bend as MN
import ./vsdpf.bend as VS
import ./ckpf.bend as CKP
import ./solve.bend as SO
import ./totalpf.bend as TP
import ./blamepf.bend as BLM

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The equations of some constraints, without an index
# --------------------------------------------------

# the equations xs (owners os, 0 past their end) whose owner is in S
def selq(xs: List<&2, E.QExpr>, os: List<&2, Nat>, +S: List<&2, Nat>) -> List<&2, E.QExpr>:
  match xs os:
    case Nil{} os:
      Nil{}
    case Con{e, et} Nil{}:
      SV.solved.pick(SV.mem(0n, S), e, selq(et, Nil{}, S))
    case Con{e, et} Con{o, ot}:
      SV.solved.pick(SV.mem(o, S), e, selq(et, ot, S))

def eo_shift(xs: List<&2, E.QExpr>, +o: Nat, +os: List<&2, Nat>, +S: List<&2, Nat>, +k: Nat) -> {SV.eqs_of.go(xs, Con{o, os}, S, 1n+k) == SV.eqs_of.go(xs, os, S, k) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(List<&2, E.QExpr>, SV.eqs_of.go(t, Con{o, os}, S, 1n+(1n+k)), SV.eqs_of.go(t, os, S, 1n+k), eo_shift(t, o, os, S, 1n+k)) : {SV.solved.pick(SV.mem(SV.nth(os, k), S), e, _) == SV.solved.pick(SV.mem(SV.nth(os, k), S), e, SV.eqs_of.go(t, os, S, 1n+k)) : List<&2, E.QExpr>}
      {==}

def eo_nil(xs: List<&2, E.QExpr>, +S: List<&2, Nat>, +k: Nat) -> {SV.eqs_of.go(xs, Nil{}, S, k) == selq(xs, Nil{}, S) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(List<&2, E.QExpr>, SV.eqs_of.go(t, Nil{}, S, 1n+k), selq(t, Nil{}, S), eo_nil(t, S, 1n+k)) : {SV.solved.pick(SV.mem(0n, S), e, _) == SV.solved.pick(SV.mem(0n, S), e, selq(t, Nil{}, S)) : List<&2, E.QExpr>}
      {==}

# eqs_of's indexed walk is selq
def eo_selq(xs: List<&2, E.QExpr>, os: List<&2, Nat>, +S: List<&2, Nat>) -> {SV.eqs_of.go(xs, os, S, 0n) == selq(xs, os, S) : List<&2, E.QExpr>}:
  match xs os:
    case Nil{} os:
      {==}
    case Con{+e, +t} Nil{}:
      eo_nil(Con{e, t}, S, 0n)
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(List<&2, E.QExpr>, SV.eqs_of.go(t, Con{o, ot}, S, 1n), SV.eqs_of.go(t, ot, S, 0n), eo_shift(t, o, ot, S, 0n)) : {SV.solved.pick(SV.mem(o, S), e, _) == SV.solved.pick(SV.mem(o, S), e, selq(t, ot, S)) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.eqs_of.go(t, ot, S, 0n), selq(t, ot, S), eo_selq(t, ot, S)) : {SV.solved.pick(SV.mem(o, S), e, _) == SV.solved.pick(SV.mem(o, S), e, selq(t, ot, S)) : List<&2, E.QExpr>}
      {==}

def sq_drop(c: List<&2, E.QExpr>, +re: List<&2, E.QExpr>, +ro: List<&2, Nat>, +i: Nat, +S: List<&2, Nat>, +h: {SV.mem(i, S) == False{} : Bool}) -> {selq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), S) == selq(re, ro, S) : List<&2, E.QExpr>}:
  match c:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Bool, SV.mem(i, S), False{}, h) : {SV.solved.pick(_, e, selq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), S)) == selq(re, ro, S) : List<&2, E.QExpr>}
      sq_drop(t, re, ro, i, S, h)

def sq_keep(c: List<&2, E.QExpr>, +re: List<&2, E.QExpr>, +ro: List<&2, Nat>, +i: Nat, +S: List<&2, Nat>, +h: {SV.mem(i, S) == True{} : Bool}) -> {selq(SK.cat(c, re), SV.cat(SV.reps(SV.neqs(c), i), ro), S) == SK.cat(c, selq(re, ro, S)) : List<&2, E.QExpr>}:
  match c:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Bool, SV.mem(i, S), True{}, h) : {SV.solved.pick(_, e, selq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), S)) == Con{e, SK.cat(t, selq(re, ro, S))} : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, selq(SK.cat(t, re), SV.cat(SV.reps(SV.neqs(t), i), ro), S), SK.cat(t, selq(re, ro, S)), sq_keep(t, re, ro, i, S, h)) : {Con{e, _} == Con{e, SK.cat(t, selq(re, ro, S))} : List<&2, E.QExpr>}
      {==}


def only_go(+es: List<&2, SK.Ent>, +id: Nat, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +S: List<&2, Nat>, b: Bool, +e: {SV.mem(i, S) == b : Bool}, ih: {SK.Sketch.eqs.go(es, SV.only.cons(S, t, 1n+i)) == selq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), S) : List<&2, E.QExpr>}) -> {SK.Sketch.eqs.go(es, Con{SK.Rec{id, SV.bnot(b), kd}, SV.only.cons(S, t, 1n+i)}) == selq(SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t)), SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, kd)), i), SV.owners.go(es, t, 1n+i)), S) : List<&2, E.QExpr>}:
  match b:
    case False{}:
      %Equal.sym(List<&2, E.QExpr>, selq(SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t)), SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, kd)), i), SV.owners.go(es, t, 1n+i)), S), selq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), S), sq_drop(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), i, S, e)) : {SK.Sketch.eqs.go(es, SV.only.cons(S, t, 1n+i)) == _ : List<&2, E.QExpr>}
      ih
    case True{}:
      %Equal.sym(List<&2, E.QExpr>, selq(SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t)), SV.cat(SV.reps(SV.neqs(SK.Constraint.eqs(es, kd)), i), SV.owners.go(es, t, 1n+i)), S), SK.cat(SK.Constraint.eqs(es, kd), selq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), S)), sq_keep(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), i, S, e)) : {SK.cat(SK.Constraint.eqs(es, kd), SK.Sketch.eqs.go(es, SV.only.cons(S, t, 1n+i))) == _ : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SK.Sketch.eqs.go(es, SV.only.cons(S, t, 1n+i)), selq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), S), ih) : {SK.cat(SK.Constraint.eqs(es, kd), _) == SK.cat(SK.Constraint.eqs(es, kd), selq(SK.Sketch.eqs.go(es, t), SV.owners.go(es, t, 1n+i), S)) : List<&2, E.QExpr>}
      {==}

# enforcing only S keeps the equations owned by S
def only_eq(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +S: List<&2, Nat>) -> {SK.Sketch.eqs.go(es, SV.only.cons(S, cs, i)) == selq(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, i), S) : List<&2, E.QExpr>}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +kd}, +t}:
      only_eq(es, t, 1n+i, S)
    case Con{SK.Rec{+id, False{}, +kd}, +t}:
      only_go(es, id, kd, t, i, S, SV.mem(i, S), {==}, only_eq(es, t, 1n+i, S))

def only_eqs(sk: SK.Sketch, +S: List<&2, Nat>) -> {SK.Sketch.eqs(SV.only(S, sk)) == SV.eqs_of(sk, S) : List<&2, E.QExpr>}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      %Equal.sym(List<&2, E.QExpr>, SV.eqs_of.go(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), S, 0n), selq(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), S), eo_selq(SK.Sketch.eqs.go(es, cs), SV.owners.go(es, cs, 0n), S)) : {SK.Sketch.eqs.go(es, SV.only.cons(S, cs, 0n)) == _ : List<&2, E.QExpr>}
      only_eq(es, cs, 0n, S)

# The side conditions of some constraints
# ---------------------------------------

def os_go(+es: List<&2, SK.Ent>, +kd: SK.Constraint, +t: List<&2, SK.Rec>, +i: Nat, +S: List<&2, Nat>, b: Bool, +id: Nat, ih: {SK.Sketch.sides.cons(es, SV.only.cons(S, t, 1n+i)) == SV.csides.go(es, t, S, 1n+i) : List<&2, SK.Side>}) -> {SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.bnot(b), kd}, SV.only.cons(S, t, 1n+i)}) == SV.csides.pick(b, SK.Constraint.sides(es, kd), SV.csides.go(es, t, S, 1n+i)) : List<&2, SK.Side>}:
  match b:
    case False{}:
      ih
    case True{}:
      %Equal.sym(List<&2, SK.Side>, SK.Sketch.sides.cons(es, SV.only.cons(S, t, 1n+i)), SV.csides.go(es, t, S, 1n+i), ih) : {SK.cats(SK.Constraint.sides(es, kd), _) == SK.cats(SK.Constraint.sides(es, kd), SV.csides.go(es, t, S, 1n+i)) : List<&2, SK.Side>}
      {==}

def only_sides.cons(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat, +S: List<&2, Nat>) -> {SK.Sketch.sides.cons(es, SV.only.cons(S, cs, i)) == SV.csides.go(es, cs, S, i) : List<&2, SK.Side>}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +kd}, +t}:
      only_sides.cons(es, t, 1n+i, S)
    case Con{SK.Rec{+id, False{}, +kd}, +t}:
      os_go(es, kd, t, i, S, SV.mem(i, S), id, only_sides.cons(es, t, 1n+i, S))

def only_sides(sk: SK.Sketch, +S: List<&2, Nat>) -> {SK.Sketch.sides(SV.only(S, sk)) == SK.cats(SV.esides(sk), SV.csides(sk, S)) : List<&2, SK.Side>}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      %Equal.sym(List<&2, SK.Side>, SK.Sketch.sides.cons(es, SV.only.cons(S, cs, 0n)), SV.csides.go(es, cs, S, 0n), only_sides.cons(es, cs, 0n, S)) : {SK.cats(SK.Sketch.sides.ents(es), _) == SK.cats(SK.Sketch.sides.ents(es), SV.csides.go(es, cs, S, 0n)) : List<&2, SK.Side>}
      {==}

# The law
# -------

def sides_swap(~F: O.OField, +x: M.Vec(~F), +a: List<&2, SK.Side>, +b: List<&2, SK.Side>, +h: SK.Sides(~F, x, SK.cats(a, b))) -> SK.Sides(~F, x, SK.cats(b, a)):
  MN.sides_cat(~F, x, b, a, MN.sides_r(~F, x, a, b, h), MN.sides_l(~F, x, a, b, h))


# the refutation has no point, and x is one
def cf_r(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, hr: &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(SV.eqs_of(sk, Con{c, s}), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), ls, ms, k), +hz: SK.Zeros(~F, x, SV.eqs_of(sk, Con{c, s})), +hs: SK.Sides(~F, x, SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)))) -> Empty:
  match hr:
    case (+ls, r1):
      match r1:
        case (+ms, r2):
          match r2:
            case (+k, r):
              VS.refute_at(~F, x, SV.eqs_of(sk, Con{c, s}), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), SV.Ref{ls, ms, k}, CKP.ref_of(SV.eqs_of(sk, Con{c, s}), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), ls, ms, k, r), hz, hs)

# x meets c's and s's equations and sides, and the entities'
def cf_m(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, hr: &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> SV.Refutes0(SV.eqs_of(sk, Con{c, s}), SK.cats(SV.csides(sk, Con{c, s}), SV.esides(sk)), ls, ms, k), h: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk))) -> Empty:
  match h:
    case (hz, hs):
      cf_r(~F, x, sk, c, s, hr, (%only_eqs(sk, Con{c, s}) : SK.Zeros(~F, x, _)
        hz), sides_swap(~F, x, SV.esides(sk), SV.csides(sk, Con{c, s}), (%only_sides(sk, Con{c, s}) : SK.Sides(~F, x, _)
        hs)))

def cf_ok(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, h: SV.ConflictOk(sk, red, c, s), m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk))) -> Empty:
  match h:
    case (h1, h2):
      match h2:
        case (hr, hmin):
          cf_m(~F, x, sk, c, s, hr, m)

def cf_c(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, b: Bool, h: SV.Fate.pick(sk, red, ds, c, b, SV.Conflict{s}), m: SK.Sketch.holds(~F, x, SV.only(Con{c, s}, sk))) -> Empty:
  match b:
    case True{}:
      h
    case False{}:
      cf_ok(~F, x, sk, red, c, s, h, m)

# c's fate, c a conflict
def cf_k(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, k: SV.Class, b: Bool, h: SV.Fate.pick(sk, red, ds, c, b, k), hc: {SV.is_conflict(k) == True{} : Bool}, m: SK.Sketch.holds(~F, x, SV.only(Con{c, SV.support.of(k)}, sk))) -> Empty:
  match k:
    case SV.Kept{d}:
      KA.ft(hc)
    case SV.Amber{d, r}:
      KA.ft(hc)
    case SV.Over{j, s, w}:
      KA.ft(hc)
    case SV.Conflict{+s}:
      cf_c(~F, x, sk, red, ds, c, s, b, h, m)

# past the last constraint the class is Kept
def cf_past(cls: List<&2, SV.Class>, c: Nat, h: {SV.lt(c, SV.clsn(cls)) == False{} : Bool}, hc: {SV.is_conflict(SV.class_at(cls, c)) == True{} : Bool}) -> Empty:
  match cls c:
    case Nil{} c:
      KA.ft(hc)
    case Con{y, t} 0n:
      KA.tf(h)
    case Con{y, t} 1n+m:
      cf_past(t, m, h, hc)

def cf.go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, b: Bool, e: {SV.lt(c, SV.ncons(sk)) == b : Bool}, H: SV.Honest(sk, cls), hc: {SV.is_conflict(SV.class_at(cls, c)) == True{} : Bool}, m: SK.Sketch.holds(~F, x, SV.only(Con{c, SV.support(cls, c)}, sk))) -> Empty:
  match b:
    case True{}:
      +hk = Equal.trans(Bool, KA.natle(1n+c, SV.ncons(sk)), SV.lt(c, SV.ncons(sk)), True{}, Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), KA.natle(1n+c, SV.ncons(sk)), L.lt_sv(c, SV.ncons(sk))), e)
      cf_k(~F, x, sk, SV.reds(cls), SV.dropped(cls), c, SV.class_at(cls, c), SV.driven(sk, c), (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : SV.Fate(sk, cls, _)
        BLM.fate_at(sk, cls, SV.ncons(sk), 0n, c, BLM.hon_go(sk, cls, H), hk)), hc, m)
    case False{}:
      cf_past(cls, c, (%Equal.sym(Nat, SV.clsn(cls), SV.ncons(sk), BLM.hon_len(sk, cls, H)) : {SV.lt(c, _) == False{} : Bool}
        e), hc)


# LAW 8 (ROADMAP solve_conflict): in every ordered field, a conflicting
# constraint and its support cannot all hold
def solve_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +c: Nat, hc: {SV.is_conflict(SV.class_at(SO.Out.cls(SO.solve_l(sk, g0, l)), c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c)}, sk))) -> Empty:
  cf.go(~F, x, sk, SO.Out.cls(SO.solve_l(sk, g0, l)), c, SV.lt(c, SV.ncons(sk)), {==}, TP.solve_honest(sk, w, cov, g0, l), hc, MN.sketch_complete(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c)}, sk), m))
