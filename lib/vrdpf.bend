# bend-cad: what the verdict's drop checks say (lib/verdict.bend: dck;
# PLAN-sk13a S5). Proofs only.
#
# At a point x where the system solved holds (spec/solve.bend: solved,
# with the red constraints R and the dropped equations D):
# - zat: every equation of the system solved is 0 there, read by its
#   position;
# - dropped_zero: a dropped equation whose combination passes is 0
#   there (h is 1, every multiplier is on an equation of the system
#   solved, and g minus the combination normalizes to 0);
# - zeros_mark: so, when D is the classes' dropped equations and every
#   class's combinations pass, every equation of the sketch less its red
#   constraints is 0 there;
# - zeros_solved: and back, the system solved is part of that system.
#
# Generated from tools/drafts/vrdpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./flaws.bend as FL
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qnorm.bend as QN
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./keptpf.bend as KP
import ./verdict.bend as VD

def absurd(-A: Type, x: Empty) -> A:
  match x:


# The system solved, read by position
# -----------------------------------

def ztail(~F: O.OField, +x: M.Vec(~F), b: Bool, +e: E.QExpr, +rest: List<&2, E.QExpr>, hz: SK.Zeros(~F, x, SV.solved.pick(b, e, rest))) -> SK.Zeros(~F, x, rest):
  match b:
    case True{}:
      (h1, h2) = hz
      h2
    case False{}:
      hz

def zhead(~F: O.OField, +x: M.Vec(~F), b: Bool, +e: E.QExpr, +rest: List<&2, E.QExpr>, eb: {b == True{} : Bool}, hz: SK.Zeros(~F, x, SV.solved.pick(b, e, rest))) -> {O.eval(~F, x, e) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      (h1, h2) = hz
      h1
    case False{}:
      absurd({O.eval(~F, x, e) == O.zero(F) : O.C(F)}, KA.ft(eb))

# the system solved from position k: the equation j places on is 0 when
# it is in the system solved
def zat.go(~F: O.OField, +x: M.Vec(~F), es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +k: Nat, hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, k)), j: Nat, hs: {VD.solved_at(own, R, D, Nat.add(j, k)) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, j)) == O.zero(F) : O.C(F)}:
  match es j:
    case Nil{} j:
      QE.ofq_zero(~F)
    case Con{+e, +t} 0n:
      zhead(~F, x, VD.solved_at(own, R, D, k), e, SV.solved.go(t, own, R, D, 1n+k), hs, hz)
    case Con{+e, +t} 1n++i:
      zat.go(~F, x, t, own, R, D, 1n+k, ztail(~F, x, VD.solved_at(own, R, D, k), e, SV.solved.go(t, own, R, D, 1n+k), hz), i,
        (%LN.add_succ(i, k) : {VD.solved_at(own, R, D, _) == True{} : Bool}
          hs))

def zat(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), +i: Nat, hs: {VD.solved_at(own, R, D, i) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, i)) == O.zero(F) : O.C(F)}:
  zat.go(~F, x, es, own, R, D, 0n, hz, i,
    (%LN.add_zero(i) : {VD.solved_at(own, R, D, _) == True{} : Bool}
      hs))

# Dropped equations
# -----------------


# a combination of equations of the system solved is 0
def comb_zero(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), qs: List<&2, SV.Mul>, +h: {VD.comb.solved(own, R, D, qs) == True{} : Bool}) -> {O.eval(~F, x, VD.comb.rhs(es, qs)) == O.zero(F) : O.C(F)}:
  match qs:
    case Nil{}:
      QE.ofq_zero(~F)
    case Con{SV.Mul{+i, +q}, +t}:
      +h1 = L.band_l(VD.solved_at(own, R, D, i), VD.comb.solved(own, R, D, t), h)
      +h2 = L.band_r(VD.solved_at(own, R, D, i), VD.comb.solved(own, R, D, t), h)
      +a = O.eval(~F, x, q)
      %Equal.sym(O.C(F), O.eval(~F, x, VD.comb.rhs(es, t)), O.zero(F), comb_zero(~F, x, es, own, R, D, hz, t, h2)) : {O.add(F, O.mul(F, a, O.eval(~F, x, SV.eqat(es, i))), _) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.eval(~F, x, SV.eqat(es, i)), O.zero(F), zat(~F, x, es, own, R, D, hz, i, h1)) : {O.add(F, O.mul(F, a, _), O.zero(F)) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, a) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      O.add_zero(F)(O.zero(F))

# a dropped equation whose combination passes
def drop_zero(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), +j: Nat, +hh: E.QExpr, +qs: List<&2, SV.Mul>, +h: {VD.drop.ok(es, own, R, D, SV.Drop{j, SV.Comb{hh, qs}}) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, j)) == O.zero(F) : O.C(F)}:
  +b1 = QN.qzero(E.QSub{hh, E.QCst{VD.qone()}})
  +b2 = VD.comb.solved(own, R, D, qs)
  +b3 = QN.qzero(E.QSub{SV.eqat(es, j), VD.comb.rhs(es, qs)})
  +h23 = L.band_r(b1, SV.band(b2, b3), h)
  Equal.trans(O.C(F), O.eval(~F, x, SV.eqat(es, j)), O.eval(~F, x, VD.comb.rhs(es, qs)), O.zero(F),
    FO.eq_of_sub(~F, O.eval(~F, x, SV.eqat(es, j)), O.eval(~F, x, VD.comb.rhs(es, qs)), QN.qzero_ok(~F, x, E.QSub{SV.eqat(es, j), VD.comb.rhs(es, qs)}, L.band_r(b2, b3, h23))),
    comb_zero(~F, x, es, own, R, D, hz, qs, L.band_l(b2, b3, h23)))

def drops_zero.c(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), +k: Nat, +j: Nat, +hh: E.QExpr, +qs: List<&2, SV.Mul>, +t: List<&2, SV.Drop>, b: Bool, eb: {SV.eq(k, j) == b : Bool}, hm: {SV.bor(b, SV.mem(k, SV.drops(t))) == True{} : Bool},
  +h1: {VD.drop.ok(es, own, R, D, SV.Drop{j, SV.Comb{hh, qs}}) == True{} : Bool}, ih: {SV.mem(k, SV.drops(t)) == True{} : Bool} -> {O.eval(~F, x, SV.eqat(es, k)) == O.zero(F) : O.C(F)}) -> {O.eval(~F, x, SV.eqat(es, k)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, k, j, L.eq_ok(k, j, eb)) : {O.eval(~F, x, SV.eqat(es, _)) == O.zero(F) : O.C(F)}
      drop_zero(~F, x, es, own, R, D, hz, j, hh, qs, h1)
    case False{}:
      ih(hm)

def drops_zero(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), dd: List<&2, SV.Drop>, +k: Nat, hm: {SV.mem(k, SV.drops(dd)) == True{} : Bool}, +h: {VD.drops.ok(es, own, R, D, dd) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, k)) == O.zero(F) : O.C(F)}:
  match dd:
    case Nil{}:
      absurd({O.eval(~F, x, SV.eqat(es, k)) == O.zero(F) : O.C(F)}, KA.ft(hm))
    case Con{SV.Drop{+j, SV.Comb{+hh, +qs}}, +t}:
      +h1 = L.band_l(VD.drop.ok(es, own, R, D, SV.Drop{j, SV.Comb{hh, qs}}), VD.drops.ok(es, own, R, D, t), h)
      +h2 = L.band_r(VD.drop.ok(es, own, R, D, SV.Drop{j, SV.Comb{hh, qs}}), VD.drops.ok(es, own, R, D, t), h)
      drops_zero.c(~F, x, es, own, R, D, hz, k, j, hh, qs, t, SV.eq(k, j), {==}, hm, h1, hm2 => drops_zero(~F, x, es, own, R, D, hz, t, k, hm2, h2))

def kdrops_zero(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), kc: SV.Class, +p: Nat, hm: {SV.mem(p, SV.kdrops(kc)) == True{} : Bool}, +h: {VD.kdrops.ok(es, own, R, D, kc) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}:
  match kc:
    case SV.Kept{+dd}:
      drops_zero(~F, x, es, own, R, D, hz, dd, p, hm, h)
    case SV.Amber{+dd, rs}:
      drops_zero(~F, x, es, own, R, D, hz, dd, p, hm, h)
    case SV.Over{j, s, w}:
      absurd({O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}, KA.ft(hm))
    case SV.Conflict{s}:
      absurd({O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}, KA.ft(hm))

def dropped_zero.c(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), +kc: SV.Class, +t: List<&2, SV.Class>, +p: Nat, a: Bool, ea: {SV.mem(p, SV.kdrops(kc)) == a : Bool}, hm: {SV.bor(a, SV.mem(p, SV.dropped(t))) == True{} : Bool},
  +h1: {VD.kdrops.ok(es, own, R, D, kc) == True{} : Bool}, ih: {SV.mem(p, SV.dropped(t)) == True{} : Bool} -> {O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}) -> {O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}:
  match a:
    case True{}:
      kdrops_zero(~F, x, es, own, R, D, hz, kc, p, ea, h1)
    case False{}:
      ih(hm)

# an equation the classes drop is 0, when every class's combinations pass
def dropped_zero(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), cls: List<&2, SV.Class>, +p: Nat, hm: {SV.mem(p, SV.dropped(cls)) == True{} : Bool}, +h: {VD.dck(es, own, R, D, cls) == True{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}:
  match cls:
    case Nil{}:
      absurd({O.eval(~F, x, SV.eqat(es, p)) == O.zero(F) : O.C(F)}, KA.ft(hm))
    case Con{+kc, +t}:
      +h1 = L.band_l(VD.kdrops.ok(es, own, R, D, kc), VD.dck(es, own, R, D, t), h)
      +h2 = L.band_r(VD.kdrops.ok(es, own, R, D, kc), VD.dck(es, own, R, D, t), h)
      dropped_zero.c(~F, x, es, own, R, D, hz, kc, t, p, SV.mem(p, SV.kdrops(kc)), {==},
        (%SP.mem_cat(p, SV.kdrops(kc), SV.dropped(t)) : {_ == True{} : Bool}
          hm),
        h1, hm2 => dropped_zero(~F, x, es, own, R, D, hz, t, p, hm2, h2))

# Every equation of a constraint that is not red
# ----------------------------------------------

def sa_of(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +i: Nat, hr: {SV.mem(SV.nth(own, i), R) == False{} : Bool}, hd: {SV.mem(i, D) == False{} : Bool}) -> {VD.solved_at(own, R, D, i) == True{} : Bool}:
  %Equal.sym(Bool, SV.mem(SV.nth(own, i), R), False{}, hr) : {SV.band(SV.bnot(_), SV.bnot(SV.mem(i, D))) == True{} : Bool}
  %Equal.sym(Bool, SV.mem(i, D), False{}, hd) : {SV.band(SV.bnot(False{}), SV.bnot(_)) == True{} : Bool}
  {==}


def pz.c(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(es, own, R, SV.dropped(cls), cls) == True{} : Bool}, +i: Nat, +hr: {SV.mem(SV.nth(own, i), R) == False{} : Bool}, b: Bool, eb: {SV.mem(i, SV.dropped(cls)) == b : Bool}) -> {O.eval(~F, x, SV.eqat(es, i)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      dropped_zero(~F, x, es, own, R, SV.dropped(cls), hz, cls, i, eb, hd)
    case False{}:
      zat(~F, x, es, own, R, SV.dropped(cls), hz, i, sa_of(own, R, SV.dropped(cls), i, hr, eb))

# the equation at position i, its constraint not red, is 0
def pz(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(es, own, R, SV.dropped(cls), cls) == True{} : Bool}, +i: Nat, +hr: {SV.mem(SV.nth(own, i), R) == False{} : Bool}) -> {O.eval(~F, x, SV.eqat(es, i)) == O.zero(F) : O.C(F)}:
  pz.c(~F, x, es, own, R, cls, hz, hd, i, hr, SV.mem(i, SV.dropped(cls)), {==})

# The sketch less its red constraints
# -----------------------------------

def zm.c(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(es, own, R, SV.dropped(cls), cls) == True{} : Bool}, +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +hq: {OW.qdrop(k, es) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, own) == Con{o, ot} : List<&2, Nat>}, b: Bool, eb: {SV.mem(o, R) == b : Bool}, ih: SK.Zeros(~F, x, KP.keepq(t, ot, R)))
  -> SK.Zeros(~F, x, KP.keepq.go(b, e, KP.keepq(t, ot, R))):
  match b:
    case True{}:
      ih
    case False{}:
      ((%OW.eqat_of(es, k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        pz(~F, x, es, own, R, cls, hz, hd, k, (%Equal.sym(Nat, SV.nth(own, k), o, OW.nth_of(own, k, o, ot, ho)) : {SV.mem(_, R) == False{} : Bool}
          eb))), ih)

# the equations ys (owners os) from position k, those whose constraint is
# not red: each is 0
def zm.go(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, SV.dropped(cls), 0n)), +hd: {VD.dck(es, own, R, SV.dropped(cls), cls) == True{} : Bool}, ys: List<&2, E.QExpr>, os: List<&2, Nat>, +k: Nat, +hq: {OW.qdrop(k, es) == ys : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, own) == os : List<&2, Nat>}) -> SK.Zeros(~F, x, KP.keepq(ys, os, R)):
  match ys os:
    case Nil{} os:
      Unit{}
    case Con{e, t} Nil{}:
      Unit{}
    case Con{+e, +t} Con{+o, +ot}:
      zm.c(~F, x, es, own, R, cls, hz, hd, k, e, t, o, ot, hq, ho, SV.mem(o, R), {==}, zm.go(~F, x, es, own, R, cls, hz, hd, t, ot, 1n+k, OW.qdrop_step(k, es, e, t, hq), OW.ndrop_step(k, own, o, ot, ho)))

# where the system solved holds and every class's combinations pass,
# every equation of the sketch less its red constraints holds
def zeros_mark(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hd: {VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool})
  -> SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.reds(cls), sk))):
  %Equal.sym(List<&2, E.QExpr>, SK.Sketch.eqs(SV.mark(SV.reds(cls), sk)), KP.keepq(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls)), KP.kept_keepq(sk, SV.reds(cls))) : SK.Zeros(~F, x, _)
  zm.go(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), cls, hz, hd, SK.Sketch.eqs(sk), SV.owners(sk), 0n, {==}, {==})

# And back: the system solved is part of it
# -----------------------------------------

def zs.d(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +t: List<&2, E.QExpr>, +ot: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +k: Nat, c: Bool, hk: SK.Zeros(~F, x, Con{e, KP.keepq(t, ot, R)}),
  ih: SK.Zeros(~F, x, KP.keepq(t, ot, R)) -> SK.Zeros(~F, x, SV.solved.go(t, own, R, D, 1n+k))) -> SK.Zeros(~F, x, SV.solved.pick(SV.bnot(c), e, SV.solved.go(t, own, R, D, 1n+k))):
  match c:
    case True{}:
      (h1, h2) = hk
      ih(h2)
    case False{}:
      (h1, h2) = hk
      (h1, ih(h2))

def zs.c(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +t: List<&2, E.QExpr>, +ot: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +k: Nat, b: Bool, hk: SK.Zeros(~F, x, KP.keepq.go(b, e, KP.keepq(t, ot, R))),
  ih: SK.Zeros(~F, x, KP.keepq(t, ot, R)) -> SK.Zeros(~F, x, SV.solved.go(t, own, R, D, 1n+k))) -> SK.Zeros(~F, x, SV.solved.pick(SV.band(SV.bnot(b), SV.bnot(SV.mem(k, D))), e, SV.solved.go(t, own, R, D, 1n+k))):
  match b:
    case True{}:
      ih(hk)
    case False{}:
      zs.d(~F, x, e, t, ot, own, R, D, k, SV.mem(k, D), hk, ih)

def zs.go(~F: O.OField, +x: M.Vec(~F), ys: List<&2, E.QExpr>, os: List<&2, Nat>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +k: Nat, +ho: {OW.ndrop(k, own) == os : List<&2, Nat>}, +hl: {SV.len(os) == SV.neqs(ys) : Nat}, hk: SK.Zeros(~F, x, KP.keepq(ys, os, R)))
  -> SK.Zeros(~F, x, SV.solved.go(ys, own, R, D, k)):
  match ys os:
    case Nil{} os:
      Unit{}
    case Con{+e, +t} Nil{}:
      absurd(SK.Zeros(~F, x, SV.solved.go(Con{e, t}, own, R, D, k)), SP.len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(Nat, SV.nth(own, k), o, OW.nth_of(own, k, o, ot, ho)) : SK.Zeros(~F, x, SV.solved.pick(SV.band(SV.bnot(SV.mem(_, R)), SV.bnot(SV.mem(k, D))), e, SV.solved.go(t, own, R, D, 1n+k)))
      zs.c(~F, x, e, t, ot, own, R, D, k, SV.mem(o, R), hk, hk2 => zs.go(~F, x, t, ot, own, R, D, 1n+k, OW.ndrop_step(k, own, o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), hk2))

# wherever the sketch less its red constraints holds, the system solved
# holds (whatever is dropped)
def zeros_solved(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, hk: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(R, sk)))) -> SK.Zeros(~F, x, SV.solved(sk, R, D)):
  zs.go(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), R, D, 0n, {==}, KP.owners_len(sk),
    (%KP.kept_keepq(sk, R) : SK.Zeros(~F, x, _)
      hk))
