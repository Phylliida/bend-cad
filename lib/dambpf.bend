# bend-cad: deleting every amber constraint changes no solution where the
# amber drops' nd segments have nonzero length (PLAN-sk13b B6, the draft
# solve_amber over any honest classification). Proofs only.
#
# At a geometry meaning the sketch less its red and amber constraints:
# - the system solved holds there (an amber constraint drops every one of
#   its equations, so the ambers own none of it: lib/amberlawpf.bend's
#   se.go, from the Honest read once for that, ap_rb);
# - so every fact of a kept constraint holds (lib/dfactpf.bend:
#   facts_hold), and an amber constraint's equations, all dropped, hold
#   where their nd segments are long (amber_nd's);
# - so every equation of the sketch less its reds holds (pz2);
# - an amber constraint's sides follow from its Implied refutations (one
#   per side, SV.AllImplied, handed on by facts_hold), its premises
#   holding by then: along the order, as lib/vsdpf.bend's sides_mark.
#
# Generated from tools/drafts/dambpf.draft by tools/expand.py; edit the
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
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./hreadpf.bend as HR
import ./dirpf.bend as DP
import ./dfactpf.bend as DFC
import ./amberlawpf.bend as AL
import ./vrdpf.bend as VR
import ./vsdpf.bend as VS
import ./keptpf.bend as KP
import ./ckpf.bend as CKP
import ./verdict.bend as VD
import ./meaning.bend as MN
import ./wfdec.bend as WF
import ./wfcpf.bend as WC


def absurd(-A: Type, x: Empty) -> A:
  match x:

# The ambers drop all their equations, read once
# ----------------------------------------------

def ab_d(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, nr: SV.NoRefute2(sk, R, c), dok: SV.DropsOk(sk, cls, R, D, c, SV.drops(dd)), dnd: SV.DropsNd(sk, cls, R, D, c, dd),
  q: ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} & SV.AllImplied(sk, R, c))) -> ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} & SV.AmberOk(sk, cls, R, D, c, dd)):
  match q:
    case (+ha, all):
      (ha, (nr, (dok, (dnd, (ha, all)))))

def ab_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, h: SV.AmberOk(sk, cls, R, D, c, dd)) -> ({SV.is_amberable(sk, c, SV.drops(dd)) == True{} : Bool} & SV.AmberOk(sk, cls, R, D, c, dd)):
  (nr, q1) = h
  (dok, q2) = q1
  (dnd, q3) = q2
  ab_d(sk, cls, R, D, c, dd, nr, dok, dnd, q3)

def pcb_rb(b: Bool, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, +rs: List<&2, SV.Ref>, h: SV.Fate.pick(sk, cls, R, D, c, b, SV.Amber{dd, rs}))
  -> ({SV.alldrop.go(SV.owners(sk), SV.drops(dd), c, 0n) == True{} : Bool} & SV.Fate.pick(sk, cls, R, D, c, b, SV.Amber{dd, rs})):
  match b:
    case True{}:
      absurd(({SV.alldrop.go(SV.owners(sk), SV.drops(dd), c, 0n) == True{} : Bool} & Empty), h)
    case False{}:
      ab_rb(sk, cls, R, D, c, dd, h)

def pck_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, k: SV.Class, b: Bool, h: SV.Fate.pick(sk, cls, R, D, c, b, k))
  -> ({SV.bor(SV.bnot(SV.is_amber(k)), SV.alldrop.go(SV.owners(sk), SV.kdrops(k), c, 0n)) == True{} : Bool} & SV.Fate.pick(sk, cls, R, D, c, b, k)):
  match k:
    case SV.Kept{+d}:
      ({==}, h)
    case SV.Amber{+dd, +rs}:
      pcb_rb(b, sk, cls, R, D, c, dd, rs, h)
    case SV.Over{+j, +s, +w}:
      ({==}, h)
    case SV.Conflict{+s, +nd}:
      ({==}, h)

def apc(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +m: Nat, +c: Nat, p: ({AL.pc(sk, cls, c) == True{} : Bool} & SV.Fate(sk, cls, c)), q: ({AL.allP(sk, cls, m, 1n+c) == True{} : Bool} & SV.Honest.go(sk, cls, m, 1n+c)))
  -> ({AL.allP(sk, cls, 1n+m, c) == True{} : Bool} & SV.Honest.go(sk, cls, 1n+m, c)):
  match p:
    case (+hp, f2):
      match q:
        case (+hP, r2):
          (LI.band_i(AL.pc(sk, cls, c), AL.allP(sk, cls, m, 1n+c), hp, hP), (f2, r2))

def ap_go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c: Nat, h: SV.Honest.go(sk, cls, n, c)) -> ({AL.allP(sk, cls, n, c) == True{} : Bool} & SV.Honest.go(sk, cls, n, c)):
  match n:
    case 0n:
      ({==}, h)
    case 1n++m:
      match h:
        case (f, r):
          apc(sk, cls, m, c, pck_rb(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.class_at(cls, c), SV.driven(sk, c), f), ap_go(sk, cls, m, 1n+c, r))

def ap_cmb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +hn: {SV.clsn(cls) == SV.ncons(sk) : Nat}, q: ({AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool} & SV.Honest.go(sk, cls, SV.ncons(sk), 0n))) -> ({AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool} & SV.Honest(sk, cls)):
  match q:
    case (+hP, g2):
      (hP, (hn, g2))

# every amber constraint drops all of its equations, read out of an
# honest classification, given back
def ap_rb(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls)) -> ({AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool} & SV.Honest(sk, cls)):
  match h:
    case (+hn, g):
      ap_cmb(sk, cls, hn, ap_go(sk, cls, SV.ncons(sk), 0n, g))

# The system solved, at a geometry meaning the sketch less its reds and
# ambers
# ----------------------------------------------------------------------


def solved_eq2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +hlen: {SV.clsn(cls) == SV.ncons(sk) : Nat}) -> {SV.solved(sk, SV.reds(cls), SV.dropped(cls)) == SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), SV.dropped(cls)) : List<&2, E.QExpr>}:
  AL.se.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.ambers(cls), SV.dropped(cls), 0n, SV.owners(sk), {==}, KP.owners_len(sk), AL.aq.go(sk, cls, hP, hlen, SV.owners(sk), 0n, {==}))

def zs_amb2(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +hlen: {SV.clsn(cls) == SV.ncons(sk) : Nat}, hz: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)))) -> SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))):
  %Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), SV.dropped(cls)), solved_eq2(sk, cls, hP, hlen)) : SK.Zeros(~F, x, _)
  VR.zeros_solved(~F, x, sk, SV.cat(SV.reds(cls), SV.ambers(cls)), SV.dropped(cls), hz)

# Long segments
# -------------

def longs_l(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, a: List<&2, Nat>, +b: List<&2, Nat>, +h: DR.Longs(~F, env, es, SV.cat(a, b))) -> DR.Longs(~F, env, es, a):
  match a:
    case Nil{}:
      Unit{}
    case Con{+s, +t}:
      (DP.fst(DR.Long(~F, env, es, s), DR.Longs(~F, env, es, SV.cat(t, b)), h), longs_l(~F, env, es, t, b, DP.snd(DR.Long(~F, env, es, s), DR.Longs(~F, env, es, SV.cat(t, b)), h)))

def longs_r(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, a: List<&2, Nat>, +b: List<&2, Nat>, +h: DR.Longs(~F, env, es, SV.cat(a, b))) -> DR.Longs(~F, env, es, b):
  match a:
    case Nil{}:
      h
    case Con{+s, +t}:
      longs_r(~F, env, es, t, b, DP.snd(DR.Long(~F, env, es, s), DR.Longs(~F, env, es, SV.cat(t, b)), h))

def dds_c(~F: O.OField, b: Bool, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +nd: List<&2, Nat>, +rest: List<&2, Nat>, ha: DR.Longs(~F, env, es, nd), hb: DR.Longs(~F, env, es, rest)) -> DR.Longs(~F, env, es, SV.dnd.pick(b, nd, rest)):
  match b:
    case True{}:
      ha
    case False{}:
      hb

# a drop's nd is part of its class's drops' nds
def dds_longs(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, dd: List<&2, SV.Drop>, +j: Nat, +h: DR.Longs(~F, env, es, SV.dds_nd(dd))) -> DR.Longs(~F, env, es, SV.dnd.go(dd, j)):
  match dd:
    case Nil{}:
      Unit{}
    case Con{SV.Drop{+i, +nd, w}, +t}:
      dds_c(~F, SV.eq(i, j), env, es, nd, SV.dnd.go(t, j), longs_l(~F, env, es, nd, SV.dds_nd(t), h), dds_longs(~F, env, es, t, j, longs_r(~F, env, es, nd, SV.dds_nd(t), h)))

# the amber nds include those of the class at o
def an_at(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, cls: List<&2, SV.Class>, o: Nat, +h: DR.Longs(~F, env, es, SV.amber_nd(cls))) -> DR.Longs(~F, env, es, SV.amber_nd.of(SV.class_at(cls, o))):
  match cls o:
    case Nil{} o:
      Unit{}
    case Con{+k, +t} 0n:
      longs_l(~F, env, es, SV.amber_nd.of(k), SV.amber_nd(t), h)
    case Con{+k, +t} 1n+q:
      an_at(~F, env, es, t, q, longs_r(~F, env, es, SV.amber_nd.of(k), SV.amber_nd(t), h))

def an_kdd(k: SV.Class, ha: {SV.is_amber(k) == True{} : Bool}) -> {SV.amber_nd.of(k) == SV.dds_nd(SV.kdd(k)) : List<&2, Nat>}:
  match k:
    case SV.Kept{dd}:
      absurd({Nil{} == SV.dds_nd(dd) : List<&2, Nat>}, KA.ft(ha))
    case SV.Amber{dd, rs}:
      {==}
    case SV.Over{j, s, w}:
      absurd({Nil{} == Nil{} : List<&2, Nat>}, KA.ft(ha))
    case SV.Conflict{s, nd}:
      absurd({Nil{} == Nil{} : List<&2, Nat>}, KA.ft(ha))

# Every equation of a constraint that is not red
# ----------------------------------------------


def lt_nl(a: Nat, n: Nat, h: {SV.lt(a, n) == True{} : Bool}) -> {KA.natle(1n+a, n) == True{} : Bool}:
  match a n:
    case 0n 0n:
      absurd({KA.natle(1n, 0n) == True{} : Bool}, KA.ft(h))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({KA.natle(1n+1n+i, 0n) == True{} : Bool}, KA.ft(h))
    case 1n+i 1n+j:
      lt_nl(i, j, h)

# an equation of an amber constraint is among its drops
def amk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +eb: {SV.is_amber(SV.class_at(cls, SV.nth(SV.owners(sk), k))) == True{} : Bool}) -> {SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool}:
  +hok = DFC.nth_lt(SV.owners(sk), k, SV.ncons(sk), OW.below_ncons(sk), DFC.jl_of(sk, k, hk))
  +had = AL.amb_ad(sk, cls, SV.nth(SV.owners(sk), k), hP, lt_nl(SV.nth(SV.owners(sk), k), SV.ncons(sk), hok), eb)
  %Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : {SV.mem(_, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool}
  AL.ad_at(SV.owners(sk), SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k))), SV.nth(SV.owners(sk), k), 0n, k, had, DFC.jl_of(sk, k, hk), LI.eq_refl(SV.nth(SV.owners(sk), k)))

# its fact's nd is among the amber nds
def lk_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +k: Nat, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hmk: {SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool}, +eb: {SV.is_amber(SV.class_at(cls, SV.nth(SV.owners(sk), k))) == True{} : Bool})
  -> DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, k)):
  %Equal.sym(List<&2, Nat>, SV.dnd_at(cls, k), SV.dnd.go(SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k), DFC.dnd_own(sk, cls, k, hf, hmk)) : DR.Longs(~F, x, SV.ents(sk), _)
  dds_longs(~F, x, SV.ents(sk), SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k, (%an_kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k)), eb) : DR.Longs(~F, x, SV.ents(sk), _)
    an_at(~F, x, SV.ents(sk), cls, SV.nth(SV.owners(sk), k), hl)))

# a constraint neither red nor amber
def nra(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +o: Nat, +hr: {SV.mem(o, SV.reds(cls)) == False{} : Bool}, +ea: {SV.is_amber(SV.class_at(cls, o)) == False{} : Bool}) -> {SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))) == False{} : Bool}:
  Equal.trans(Bool, SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))), SV.bor(SV.mem(o, SV.reds(cls)), SV.mem(o, SV.ambers(cls))), False{}, SP.mem_cat(o, SV.reds(cls), SV.ambers(cls)),
    LI.bor_f(SV.mem(o, SV.reds(cls)), SV.mem(o, SV.ambers(cls)), hr, Equal.trans(Bool, SV.mem(o, SV.ambers(cls)), SV.is_amber(SV.class_at(cls, o)), False{}, VS.mem_ambers(cls, o), ea)))

def pz2.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hr: {SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls)) == False{} : Bool}, +eb: {SV.is_amber(SV.class_at(cls, SV.nth(SV.owners(sk), k))) == b : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      +hmk = amk(sk, cls, k, hk, hP, eb)
      +hmD = Equal.trans(Bool, SV.mem(k, SV.dropped(cls)), SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))), True{}, HR.mem_dropped(sk, cls, k, hf), hmk)
      DP.fst({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))), DP.fact_ok(~F, x, SV.ents(sk), SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k))), DFC.fh_at(~F, x, sk, cls, k, hk, DFC.dkb(sk, cls, hf, k, hmD, hk), af), lk_of(~F, x, sk, cls, k, hf, hl, hmk, eb)))
    case False{}:
      VR.zat(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{}, hzN, k, VR.sa_of(SV.owners(sk), SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{}, k, nra(sk, cls, SV.nth(SV.owners(sk), k), hr, eb), {==}))

# the sketch's equation k, its constraint not red, holds at x
def pz2(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hr: {SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls)) == False{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}:
  pz2.c(~F, SV.is_amber(SV.class_at(cls, SV.nth(SV.owners(sk), k))), x, sk, cls, hf, hP, af, hl, hzN, k, hk, hr, {==})

def zm2.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>}, +eb: {SV.mem(o, SV.reds(cls)) == b : Bool}, ih: SK.Zeros(~F, x, KP.keepq(t, ot, SV.reds(cls))))
  -> SK.Zeros(~F, x, KP.keepq.go(b, e, KP.keepq(t, ot, SV.reds(cls)))):
  match b:
    case True{}:
      ih
    case False{}:
      ((%OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        pz2(~F, x, sk, cls, hf, hP, af, hl, hzN, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), (%Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho)) : {SV.mem(_, SV.reds(cls)) == False{} : Bool}
          eb))), ih)

def zm2.go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), ys: List<&2, E.QExpr>, os: List<&2, Nat>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == ys : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == os : List<&2, Nat>}) -> SK.Zeros(~F, x, KP.keepq(ys, os, SV.reds(cls))):
  match ys os:
    case Nil{} os:
      Unit{}
    case Con{e, t} Nil{}:
      Unit{}
    case Con{+e, +t} Con{+o, +ot}:
      zm2.c(~F, SV.mem(o, SV.reds(cls)), x, sk, cls, hf, hP, af, hl, hzN, k, e, t, o, ot, hq, ho, {==}, zm2.go(~F, x, sk, cls, hf, hP, af, hl, hzN, t, ot, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), OW.ndrop_step(k, SV.owners(sk), o, ot, ho)))

# every equation of the sketch less its red constraints holds at x
def zr_mark(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{}))) -> SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.reds(cls), sk))):
  %Equal.sym(List<&2, E.QExpr>, SK.Sketch.eqs(SV.mark(SV.reds(cls), sk)), KP.keepq(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls)), KP.kept_keepq(sk, SV.reds(cls))) : SK.Zeros(~F, x, _)
  zm2.go(~F, x, sk, cls, hf, hP, af, hl, hzN, SK.Sketch.eqs(sk), SV.owners(sk), 0n, {==}, {==})

def zof2.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +cs: List<&2, Nat>, +hn: {SV.none_in(cs, SV.reds(cls)) == True{} : Bool}, +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +eb: {SV.mem(SV.nth(SV.owners(sk), k), cs) == b : Bool}, ih: SK.Zeros(~F, x, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k)))
  -> SK.Zeros(~F, x, SV.solved.pick(b, e, SV.eqs_of.go(t, SV.owners(sk), cs, 1n+k))):
  match b:
    case True{}:
      ((%OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        pz2(~F, x, sk, cls, hf, hP, af, hl, hzN, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), VS.ni_mem(SV.nth(SV.owners(sk), k), cs, SV.reds(cls), hn, eb))), ih)
    case False{}:
      ih

# the equations of constraints cs, none red, hold at x
def zof2.go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), ys: List<&2, E.QExpr>, +cs: List<&2, Nat>, +hn: {SV.none_in(cs, SV.reds(cls)) == True{} : Bool}, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == ys : List<&2, E.QExpr>}) -> SK.Zeros(~F, x, SV.eqs_of.go(ys, SV.owners(sk), cs, k)):
  match ys:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      zof2.c(~F, SV.mem(SV.nth(SV.owners(sk), k), cs), x, sk, cls, hf, hP, af, hl, hzN, cs, hn, k, e, t, hq, {==}, zof2.go(~F, x, sk, cls, hf, hP, af, hl, hzN, t, cs, hn, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq)))

# An amber constraint's sides
# ---------------------------


def imp_one(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +i: Nat, +s: SK.Side, +t: List<&2, SK.Side>, +hd: {VS.sdrop(i, SV.csides(sk, [c])) == Con{s, t} : List<&2, SK.Side>}, hi: SV.Implied(sk, R, c, i), +hz: SK.Zeros(~F, x, SV.pre_eqs(sk, R, c)), +hs: SK.Sides(~F, x, SV.pre_sides(sk, R, c))) -> SK.Sides(~F, x, [s]):
  match hi:
    case (+ls, r1):
      match r1:
        case (+ms, r2):
          match r2:
            case (+k, r):
              VS.side_of_ref(~F, x, SV.pre_eqs(sk, R, c), SV.pre_sides(sk, R, c), s, SV.Ref{ls, ms, k}, (%VS.side_at_of(SV.csides(sk, [c]), i, s, t, hd) : {VD.ref.ok(SV.pre_eqs(sk, R, c), SK.cats(SV.pre_sides(sk, R, c), [SV.negate(_)]), SV.Ref{ls, ms, k}) == True{} : Bool}
                CKP.ref_of(SV.pre_eqs(sk, R, c), SV.neg_pre(sk, R, c, i), ls, ms, k, r)), hz, hs)

# c's sides from the i-th (ss), each implied: they hold where the premises
# do
def imp_go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, ss: List<&2, SK.Side>, +i: Nat, +hd: {VS.sdrop(i, SV.csides(sk, [c])) == ss : List<&2, SK.Side>}, hi: SV.implied.go(sk, R, c, ss, i), +hz: SK.Zeros(~F, x, SV.pre_eqs(sk, R, c)), +hs: SK.Sides(~F, x, SV.pre_sides(sk, R, c))) -> SK.Sides(~F, x, ss):
  match ss:
    case Nil{}:
      Unit{}
    case Con{+s, +t}:
      (h1, h2) = hi
      VS.sides_join(~F, x, [s], t, imp_one(~F, x, sk, R, c, i, s, t, hd, h1, hz, hs), imp_go(~F, x, sk, R, c, t, 1n+i, VS.sdrop_step(i, SV.csides(sk, [c]), s, t, hd), h2, hz, hs))

def amb_gk(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, k: SV.Class, h: DFC.AmbS.k(sk, R, i, k), ha: {SV.is_amber(k) == True{} : Bool}) -> SV.AllImplied(sk, R, i):
  match k:
    case SV.Kept{dd}:
      absurd(SV.AllImplied(sk, R, i), KA.ft(ha))
    case SV.Amber{dd, rs}:
      h
    case SV.Over{j, s, w}:
      absurd(SV.AllImplied(sk, R, i), KA.ft(ha))
    case SV.Conflict{s, nd}:
      absurd(SV.AllImplied(sk, R, i), KA.ft(ha))

# a driving amber constraint's Fate's sides part
def amb_get(+sk: SK.Sketch, +R: List<&2, Nat>, +i: Nat, +k: SV.Class, b: Bool, h: DFC.AmbS.pick(sk, R, i, b, k), hb: {b == False{} : Bool}, ha: {SV.is_amber(k) == True{} : Bool}) -> SV.AllImplied(sk, R, i):
  match b:
    case True{}:
      absurd(SV.AllImplied(sk, R, i), KA.tf(hb))
    case False{}:
      amb_gk(sk, R, i, k, h, ha)

# The sides along the order
# -------------------------


# a driving amber constraint: its sides from its Implied refutations, its
# premises holding
def amb_sides2(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(SK.Sketch{vs, es, rs}, cls) == True{} : Bool}, +hP: {AL.allP(SK.Sketch{vs, es, rs}, cls, SV.ncons(SK.Sketch{vs, es, rs}), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.facts.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.ncons(SK.Sketch{vs, es, rs})), SK.Sketch{vs, es, rs}, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(SK.Sketch{vs, es, rs}, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hrd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, +eb: {SV.mem(i, SV.ambers(cls)) == True{} : Bool},
  +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), am: DFC.AmbS(SK.Sketch{vs, es, rs}, cls, i)) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, [i])):
  imp_go(~F, x, SK.Sketch{vs, es, rs}, SV.reds(cls), i, SV.csides(SK.Sketch{vs, es, rs}, [i]), 0n, {==},
    amb_get(SK.Sketch{vs, es, rs}, SV.reds(cls), i, SV.class_at(cls, i), SV.driven(SK.Sketch{vs, es, rs}, i), am, VS.drv_at(vs, es, rs, i, SK.Rec{id, False{}, k}, t, hrd),
      Equal.trans(Bool, SV.is_amber(SV.class_at(cls, i)), SV.mem(i, SV.ambers(cls)), True{}, Equal.sym(Bool, SV.mem(i, SV.ambers(cls)), SV.is_amber(SV.class_at(cls, i)), VS.mem_ambers(cls, i)), eb)),
    zof2.go(~F, x, SK.Sketch{vs, es, rs}, cls, hf, hP, af, hl, hzN, SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i),
      LI.band_r(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls)), LI.band_r(SV.below(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), SV.band(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls))), LI.band_r(SV.distinct(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.band(SV.below(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), SV.band(SV.all_driving(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SV.none_in(SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), SV.reds(cls)))), KB.kbp_bool(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i, hK)))),
      0n, {==}),
    VS.sides_join(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i)), SK.Sketch.sides.ents(es), hS, hen))

def sm2.a(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(SK.Sketch{vs, es, rs}, cls) == True{} : Bool}, +hP: {AL.allP(SK.Sketch{vs, es, rs}, cls, SV.ncons(SK.Sketch{vs, es, rs}), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.facts.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.ncons(SK.Sketch{vs, es, rs})), SK.Sketch{vs, es, rs}, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(SK.Sketch{vs, es, rs}, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hrd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, +ea: {SV.mem(i, SV.reds(cls)) == False{} : Bool}, b: Bool, +eb: {SV.mem(i, SV.ambers(cls)) == b : Bool},
  hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, b, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)})), +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), am: DFC.AmbS(SK.Sketch{vs, es, rs}, cls, i), ih: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i))) -> KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i), 1n+i) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i))))
  -> SK.Sides(~F, x, SK.cats(SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)))):
  match b:
    case False{}:
      +hc = hck
      +hsk = VS.sides_l(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)), hc)
      VS.sides_join(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)), hsk,
        ih(VS.sides_r(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)), hc),
          VS.snext.t(~F, x, vs, es, rs, SV.reds(cls), i, VS.dc_kept(vs, es, rs, SV.reds(cls), i, id, k, t, hrd, ea), hS,
            (%Equal.sym(List<&2, SK.Side>, SV.csides(SK.Sketch{vs, es, rs}, [i]), SK.Constraint.sides(es, k), VS.csides_one(vs, es, rs, i, id, k, t, hrd)) : SK.Sides(~F, x, _)
              hsk)),
          VS.knext(vs, es, rs, SV.reds(cls), i, hK)))
    case True{}:
      +hone = amb_sides2(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, i, id, k, t, hrd, eb, hS, hK, am)
      VS.sides_join(~F, x, SK.Constraint.sides(es, k), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i)),
        (%VS.csides_one(vs, es, rs, i, id, k, t, hrd) : SK.Sides(~F, x, _)
          hone),
        ih(hck, VS.snext.t(~F, x, vs, es, rs, SV.reds(cls), i, VS.dc_kept(vs, es, rs, SV.reds(cls), i, id, k, t, hrd, ea), hS, hone), VS.knext(vs, es, rs, SV.reds(cls), i, hK)))

def sm2.k(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(SK.Sketch{vs, es, rs}, cls) == True{} : Bool}, +hP: {AL.allP(SK.Sketch{vs, es, rs}, cls, SV.ncons(SK.Sketch{vs, es, rs}), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.facts.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.ncons(SK.Sketch{vs, es, rs})), SK.Sketch{vs, es, rs}, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(SK.Sketch{vs, es, rs}, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), +i: Nat, +id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +hrd: {KB.rdrop(i, rs) == Con{SK.Rec{id, False{}, k}, t} : List<&2, SK.Rec>}, a: Bool, +ea: {SV.mem(i, SV.reds(cls)) == a : Bool},
  hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.mem(i, SV.cat(SV.reds(cls), SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)})), +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), am: DFC.AmbS(SK.Sketch{vs, es, rs}, cls, i), ih: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i))) -> SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i))) -> KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 1n+i), 1n+i) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), t, 1n+i))))
  -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, a, k}, SV.mark.cons(SV.reds(cls), t, 1n+i)})):
  match a:
    case True{}:
      ih((%ea : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.bor(_, SV.mem(i, SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
          (%SP.mem_cat(i, SV.reds(cls), SV.ambers(cls)) : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, _, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
            hck)),
        VS.snext.f(~F, x, vs, es, rs, SV.reds(cls), i, VS.dc_red(SK.Sketch{vs, es, rs}, SV.reds(cls), i, ea), hS), VS.knext(vs, es, rs, SV.reds(cls), i, hK))
    case False{}:
      sm2.a(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, i, id, k, t, hrd, ea, SV.mem(i, SV.ambers(cls)), {==},
        (%ea : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, SV.bor(_, SV.mem(i, SV.ambers(cls))), k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
          (%SP.mem_cat(i, SV.reds(cls), SV.ambers(cls)) : SK.Sides(~F, x, SK.Sketch.sides.cons(es, Con{SK.Rec{id, _, k}, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), t, 1n+i)}))
            hck)),
        hS, hK, am, ih)

# the records rt from position i: the side conditions of those not red
# hold, given those of the kept constraints before i
def sm2.go(~F: O.OField, +x: M.Vec(~F), +vs: List<&2, SK.VKind>, +es: List<&2, SK.Ent>, +rs: List<&2, SK.Rec>, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(SK.Sketch{vs, es, rs}, cls) == True{} : Bool}, +hP: {AL.allP(SK.Sketch{vs, es, rs}, cls, SV.ncons(SK.Sketch{vs, es, rs}), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.facts.go(SK.Sketch.eqs(SK.Sketch{vs, es, rs}), SV.owners(SK.Sketch{vs, es, rs}), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.ncons(SK.Sketch{vs, es, rs})), SK.Sketch{vs, es, rs}, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(SK.Sketch{vs, es, rs}), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(SK.Sketch{vs, es, rs}, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hen: SK.Sides(~F, x, SK.Sketch.sides.ents(es)), rt: List<&2, SK.Rec>, +i: Nat, +hrd: {KB.rdrop(i, rs) == rt : List<&2, SK.Rec>}, hck: SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rt, i))),
  +hS: SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i))), +hK: KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), i), i), amb: DFC.Amb.go(SK.Sketch{vs, es, rs}, cls, SV.clen(rt), i)) -> SK.Sides(~F, x, SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), rt, i))):
  match rt:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      (am, amb2) = amb
      sm2.go(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, t, 1n+i, KB.rdrop_step(i, rs, SK.Rec{id, True{}, k}, t, hrd), hck, VS.snext.f(~F, x, vs, es, rs, SV.reds(cls), i, VS.dc_dr(vs, es, rs, SV.reds(cls), i, id, k, t, hrd), hS), VS.knext(vs, es, rs, SV.reds(cls), i, hK), amb2)
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      (am, amb2) = amb
      sm2.k(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, i, id, k, t, hrd, SV.mem(i, SV.reds(cls)), {==}, hck, hS, hK, am, h1 => h2 => h3 => sm2.go(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, t, 1n+i, KB.rdrop_step(i, rs, SK.Rec{id, False{}, k}, t, hrd), h1, h2, h3, amb2))


# every side condition of the sketch less its red constraints holds
def sides_mark2(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hsc: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))), amb: DFC.Amb.go(sk, cls, SV.ncons(sk), 0n)) -> SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.reds(cls), sk))):
  match sk:
    case SK.Sketch{+vs, +es, +rs}:
      +hen = VS.sides_l(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rs, 0n)), hsc)
      VS.sides_join(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.reds(cls), rs, 0n)), hen,
        sm2.go(~F, x, vs, es, rs, cls, hf, hP, af, hl, hzN, hen, rs, 0n, {==}, VS.sides_r(~F, x, SK.Sketch.sides.ents(es), SK.Sketch.sides.cons(es, SV.mark.cons(SV.cat(SV.reds(cls), SV.ambers(cls)), rs, 0n)), hsc),
          (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 0n), Nil{}, KB.kb_zero(SK.Sketch{vs, es, rs}, SV.reds(cls))) : SK.Sides(~F, x, SV.csides(SK.Sketch{vs, es, rs}, _))
            (%Equal.sym(List<&2, SK.Side>, SV.csides.go(es, rs, Nil{}, 0n), Nil{}, VS.csn0(es, rs, 0n)) : SK.Sides(~F, x, _)
              Unit{})),
          (%Equal.sym(List<&2, Nat>, SV.kept_before(SK.Sketch{vs, es, rs}, SV.reds(cls), 0n), Nil{}, KB.kb_zero(SK.Sketch{vs, es, rs}, SV.reds(cls))) : KB.KBP(SK.Sketch{vs, es, rs}, SV.reds(cls), _, 0n)
            KB.kbp_zero(SK.Sketch{vs, es, rs}, SV.reds(cls))), amb))

# The law
# -------


def amb_fin(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hzN: SK.Zeros(~F, x, SV.solved(sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{})), +hsm: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))), amb: DFC.Amb.go(sk, cls, SV.ncons(sk), 0n)) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  MN.sketch_sound(~F, x, SV.mark(SV.reds(cls), sk), WF.wf_ok(SV.mark(SV.reds(cls), sk), WC.wf_mark(SV.reds(cls), sk, WC.wf_dec_ok(sk, w))), (zr_mark(~F, x, sk, cls, hf, hP, af, hl, hzN), sides_mark2(~F, x, sk, cls, hf, hP, af, hl, hzN, hsm, amb)))

def am5(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +hzm: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))), +hsm: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))),
  +hf: {HR.hfacts(sk, cls) == True{} : Bool}, q: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & DFC.Amb.go(sk, cls, SV.ncons(sk), 0n)) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  match q:
    case (+af, amb):
      amb_fin(~F, x, sk, w, cls, hf, hP, af, hl, VR.zeros_solved(~F, x, sk, SV.cat(SV.reds(cls), SV.ambers(cls)), Nil{}, hzm), hsm, amb)

def am4(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, +hzm: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))), +hsm: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))),
  q: ({HR.hfacts(sk, cls) == True{} : Bool} & (DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)) & DFC.Amb.go(sk, cls, SV.ncons(sk), 0n)))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  match q:
    case (+hf, q2):
      am5(~F, x, sk, w, cls, hl, hP, hzm, hsm, hf, q2)

def am3(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, h2: SV.Honest(sk, cls), +hzm: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))), +hsm: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))))
  -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  match h2:
    case (+hn, g):
      am4(~F, x, sk, w, cls, hl, hP, hzm, hsm, DFC.facts_hold(~F, x, sk, cls, (hn, g), zs_amb2(~F, x, sk, cls, hP, hn, hzm)))

def am2(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), +hP: {AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool}, h2: SV.Honest(sk, cls), hm: SK.Sketch.holds(~F, x, SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  match hm:
    case (hzm, hsm):
      am3(~F, x, sk, w, cls, hl, hP, h2, hzm, hsm)

def am1(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), p: ({AL.allP(sk, cls, SV.ncons(sk), 0n) == True{} : Bool} & SV.Honest(sk, cls)), hm: SK.Sketch.holds(~F, x, SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  match p:
    case (+hP, h2):
      am2(~F, x, sk, w, cls, hl, hP, h2, hm)

# DRAFT LAW (PLAN-sk13b B6, solve_amber): for an honest classification,
# in every ordered field, a geometry meaning the sketch less its red and
# amber constraints, at which the amber drops' nd segments have nonzero
# length, means it less its red ones: deleting every amber constraint
# changes no such solution
def amber_law(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls), +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  am1(~F, x, sk, w, cls, hl, ap_rb(sk, cls, h), MN.sketch_complete(~F, x, SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk), m))
