# bend-cad: the draft solver's laws (PLAN-sk13b B5.3): lib/dsolve.bend,
# over the pass with the direction layer, satisfies sk-13a's verdict laws
# (solve_exists, solve_unique, solve_pins, solve_regular, solve_blame)
# with their statements unchanged, and the extended Honest's laws at the
# solver level. Proofs only.
#
# A True ok is a True final2 (the loop, as lib/solvepf.bend's), and final2
# includes sk-13a's final, so every lemma proven for an answer whose final
# passes applies: solvepf's for the pins and uniqueness, regpf's for
# regularity. Existence is new: the old proof read every drop as a
# degree-0 combination, which a direction drop is not. At the box's point
# y where the system solved holds:
# - final2's nd check makes every live drop's nd segments long at y;
# - so each dropped equation of a constraint that is not red holds at y
#   (its fact, lib/dfactpf.bend: facts_hold), and y means the sketch less
#   its red and amber constraints (the box's sides);
# - so y means the sketch less its red ones (lib/dambpf.bend: amber_law).
# The draft Honest is the new pass's (lib/dpasspf.bend: pass2_honest), a
# definition, so it is given once per use.
#
# Generated from tools/drafts/dsolvepf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./kinst.bend as KI
import ./nat.bend as LN
import ./listpf.bend as L
import ./plan.bend as PL
import ./planpf.bend as PP
import ./meaning.bend as MN
import ./wfdec.bend as WF
import ./wfcpf.bend as WC
import ./vrdpf.bend as VR
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./keptpf.bend as KP
import ./hreadpf.bend as HR
import ./struct.bend as ST
import ./numer.bend as NU
import ./solve.bend as SO
import ./solvepf.bend as SPF
import ./regpf.bend as REG
import ./blamepf.bend as BLM
import ./dirpf.bend as DP
import ./dpass.bend as DPS
import ./dpasspf.bend as DPP
import ./dfactpf.bend as DFC
import ./dambpf.bend as DAM
import ./dcflawpf.bend as DCL
import ./dsolve.bend as DSO

def absurd(-A: Type, x: Empty) -> A:
  match x:


# The verdict the search keeps
# ----------------------------
# As lib/solvepf.bend's, over final2.

def loop_ok2(ps: List<&2, Nat>, ok: Bool, +cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel, h: {ok == DSO.accept2(cur, sk, g0, cls, pins) : Bool})
  -> {SO.run.ok(DSO.ploop2(ps, ok, cur, sk, g0, cls, pins, es, nv, skel)) == DSO.accept2(SO.run.m(DSO.ploop2(ps, ok, cur, sk, g0, cls, pins, es, nv, skel)), sk, g0, cls, pins) : Bool}:
  match ps ok:
    case Nil{} ok:
      h
    case Con{p, t} True{}:
      h
    case Con{+p, t} False{}:
      loop_ok2(t, DSO.accept2(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel, {==})

def start_ok2(ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel)
  -> {SO.run.ok(DSO.ploop2.start(ps, sk, g0, cls, pins, es, nv, skel)) == DSO.accept2(SO.run.m(DSO.ploop2.start(ps, sk, g0, cls, pins, es, nv, skel)), sk, g0, cls, pins) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, t}:
      loop_ok2(t, DSO.accept2(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel, {==})

def run_final2(r: SO.Run, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, hs: {SO.run.ok(r) == DSO.accept2(SO.run.m(r), sk, g0, cls, pins) : Bool}, ok: {SO.run.ok(r) == True{} : Bool})
  -> {DSO.final2(sk, g0, SO.answer(cls, pins, r)) == True{} : Bool}:
  match r:
    case SO.Run{b, m}:
      match b:
        case True{}:
          match m:
            case NU.POk{+y}:
              Equal.sym(Bool, True{}, DSO.accept2(NU.POk{y}, sk, g0, cls, pins), hs)
            case NU.PRetry{}:
              absurd({DSO.final2(sk, g0, SO.answer(cls, pins, SO.Run{True{}, NU.PRetry{}})) == True{} : Bool}, KA.tf(hs))
            case NU.PStop{}:
              absurd({DSO.final2(sk, g0, SO.answer(cls, pins, SO.Run{True{}, NU.PStop{}})) == True{} : Bool}, KA.tf(hs))
        case False{}:
          absurd({DSO.final2(sk, g0, SO.answer(cls, pins, SO.Run{False{}, m})) == True{} : Bool}, KA.ft(ok))


# a True ok is a True final2 on the draft solver's answer
def verdict2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}) -> {DSO.final2(sk, g0, DSO.solve_l2(sk, g0, l)) == True{} : Bool}:
  run_final2(DSO.ploop2.start(SO.precisions(l, 7n), sk, g0, DSO.cls_of2(sk), DSO.pins_of2(sk), DSO.kept2(sk), SO.nvars(sk), DSO.skel_of2(sk)), sk, g0, DSO.cls_of2(sk), DSO.pins_of2(sk),
    start_ok2(SO.precisions(l, 7n), sk, g0, DSO.cls_of2(sk), DSO.pins_of2(sk), DSO.kept2(sk), SO.nvars(sk), DSO.skel_of2(sk)), ok)

# final2 is the nd check and sk-13a's final
def fin_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}) -> {SO.checks(sk, g0, x) == True{} : Bool}:
  KA.band_r(DSO.ndok(sk, x), SO.checks(sk, g0, x), h)

def nd_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}) -> {DSO.ndok(sk, x) == True{} : Bool}:
  KA.band_l(DSO.ndok(sk, x), SO.checks(sk, g0, x), h)


# the draft Honest for the draft solver's classes
def hon2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}) -> DH.Honest(sk, SO.Out.cls(DSO.solve_l2(sk, g0, l))):
  DPP.pass2_honest(sk, SPF.wf_of(sk, g0, DSO.solve_l2(sk, g0, l), fin_of(sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok))), SPF.cov_of(sk, g0, DSO.solve_l2(sk, g0, l), fin_of(sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok))))

# Every equation of a constraint neither red nor amber holds
# ----------------------------------------------------------


# the live drops' nd: a class's own part
def ln_at(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, cls: List<&2, SV.Class>, o: Nat, +h: DR.Longs(~F, env, es, SV.live_nd(cls))) -> DR.Longs(~F, env, es, SV.live_nd.of(SV.class_at(cls, o))):
  match cls o:
    case Nil{} o:
      Unit{}
    case Con{+k, +t} 0n:
      DAM.longs_l(~F, env, es, SV.live_nd.of(k), SV.live_nd(t), h)
    case Con{+k, +t} 1n+m:
      ln_at(~F, env, es, t, m, DAM.longs_r(~F, env, es, SV.live_nd.of(k), SV.live_nd(t), h))

def ln_kdd(k: SV.Class) -> {SV.live_nd.of(k) == SV.dds_nd(SV.kdd(k)) : List<&2, Nat>}:
  match k:
    case SV.Kept{dd}:
      {==}
    case SV.Amber{dd, rs}:
      {==}
    case SV.Over{j, s, w}:
      {==}
    case SV.Conflict{s, nd}:
      {==}

# a drop's fact's nd is among the live ones
def ld_of(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +k: Nat, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hmk: {SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))) == True{} : Bool})
  -> DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, k)):
  %Equal.sym(List<&2, Nat>, SV.dnd_at(cls, k), SV.dnd.go(SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k), DFC.dnd_own(sk, cls, k, hf, hmk)) : DR.Longs(~F, x, SV.ents(sk), _)
  DAM.dds_longs(~F, x, SV.ents(sk), SV.kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))), k, (%ln_kdd(SV.class_at(cls, SV.nth(SV.owners(sk), k))) : DR.Longs(~F, x, SV.ents(sk), _)
    ln_at(~F, x, SV.ents(sk), cls, SV.nth(SV.owners(sk), k), hl)))


def pz3.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hr: {SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls)) == False{} : Bool}, +eb: {SV.mem(k, SV.dropped(cls)) == b : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      +hmk = Equal.trans(Bool, SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))), SV.mem(k, SV.dropped(cls)), True{}, Equal.sym(Bool, SV.mem(k, SV.dropped(cls)), SV.mem(k, SV.kdrops(SV.class_at(cls, SV.nth(SV.owners(sk), k)))), HR.mem_dropped(sk, cls, k, hf)), eb)
      DP.fst({O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}, DP.StatHolds(~F, x, SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k)))), DP.fact_ok(~F, x, SV.ents(sk), SV.eqat(SK.Sketch.eqs(sk), k), SV.dnd_at(cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(SV.owners(sk), k))), DFC.fh_at(~F, x, sk, cls, k, hk, DFC.dkb(sk, cls, hf, k, eb, hk), af), ld_of(~F, x, sk, cls, k, hf, hl, hmk)))
    case False{}:
      VR.zat(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), hz, k, VR.sa_of(SV.owners(sk), SV.reds(cls), SV.dropped(cls), k, hr, eb))

# the sketch's equation k, its constraint not red, holds where the system
# solved does and the live drops' nd segments are long
def pz3(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +k: Nat, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hr: {SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls)) == False{} : Bool}) -> {O.eval(~F, x, SV.eqat(SK.Sketch.eqs(sk), k)) == O.zero(F) : O.C(F)}:
  pz3.c(~F, SV.mem(k, SV.dropped(cls)), x, sk, cls, hf, af, hl, hz, k, hk, hr, {==})

def bf_l(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(h))
    case False{}:
      {==}

def zm3.c(~F: O.OField, b: Bool, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +k: Nat, +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>}, +eb: {SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))) == b : Bool}, ih: SK.Zeros(~F, x, KP.keepq(t, ot, SV.cat(SV.reds(cls), SV.ambers(cls)))))
  -> SK.Zeros(~F, x, KP.keepq.go(b, e, KP.keepq(t, ot, SV.cat(SV.reds(cls), SV.ambers(cls))))):
  match b:
    case True{}:
      ih
    case False{}:
      +hro = bf_l(SV.mem(o, SV.reds(cls)), SV.mem(o, SV.ambers(cls)), Equal.trans(Bool, SV.bor(SV.mem(o, SV.reds(cls)), SV.mem(o, SV.ambers(cls))), SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))), False{}, Equal.sym(Bool, SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))), SV.bor(SV.mem(o, SV.reds(cls)), SV.mem(o, SV.ambers(cls))), SP.mem_cat(o, SV.reds(cls), SV.ambers(cls))), eb))
      ((%OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq) : {O.eval(~F, x, _) == O.zero(F) : O.C(F)}
        pz3(~F, x, sk, cls, hf, af, hl, hz, k, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), (%Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho)) : {SV.mem(_, SV.reds(cls)) == False{} : Bool}
          hro))), ih)

def zm3.go(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), ys: List<&2, E.QExpr>, os: List<&2, Nat>, +k: Nat, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == ys : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == os : List<&2, Nat>}) -> SK.Zeros(~F, x, KP.keepq(ys, os, SV.cat(SV.reds(cls), SV.ambers(cls)))):
  match ys os:
    case Nil{} os:
      Unit{}
    case Con{e, t} Nil{}:
      Unit{}
    case Con{+e, +t} Con{+o, +ot}:
      zm3.c(~F, SV.mem(o, SV.cat(SV.reds(cls), SV.ambers(cls))), x, sk, cls, hf, af, hl, hz, k, e, t, o, ot, hq, ho, {==}, zm3.go(~F, x, sk, cls, hf, af, hl, hz, t, ot, 1n+k, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), OW.ndrop_step(k, SV.owners(sk), o, ot, ho)))

# every equation of the sketch less its red and amber constraints holds
def zr3(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hf: {HR.hfacts(sk, cls) == True{} : Bool}, +af: DP.AllFacts(~F, x, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(cls), SV.ncons(sk)), sk, cls, True{}, 0n)), +hl: DR.Longs(~F, x, SV.ents(sk), SV.live_nd(cls)), +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls)))) -> SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk))):
  %Equal.sym(List<&2, E.QExpr>, SK.Sketch.eqs(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KP.keepq(SK.Sketch.eqs(sk), SV.owners(sk), SV.cat(SV.reds(cls), SV.ambers(cls))), KP.kept_keepq(sk, SV.cat(SV.reds(cls), SV.ambers(cls)))) : SK.Zeros(~F, x, _)
  zm3.go(~F, x, sk, cls, hf, af, hl, hz, SK.Sketch.eqs(sk), SV.owners(sk), 0n, {==}, {==})

# The nd sides
# ------------

# the nd sides hold: the nd segments are long
def sd_longs(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>, +h: SK.Sides(~F, env, DR.ndsides(es, nd))) -> DR.Longs(~F, env, es, nd):
  match nd:
    case Nil{}:
      Unit{}
    case Con{+s, +t}:
      (DP.fst(DR.Long(~F, env, es, s), SK.Sides(~F, env, DR.ndsides(es, t)), h), sd_longs(~F, env, es, t, DP.snd(DR.Long(~F, env, es, s), SK.Sides(~F, env, DR.ndsides(es, t)), h)))

def an_of(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SV.Class, +h: DR.Longs(~F, env, es, SV.live_nd.of(k))) -> DR.Longs(~F, env, es, SV.amber_nd.of(k)):
  match k:
    case SV.Kept{dd}:
      Unit{}
    case SV.Amber{dd, rs}:
      h
    case SV.Over{j, s, w}:
      Unit{}
    case SV.Conflict{s, nd}:
      Unit{}

# the amber drops' nd is among the live ones
def an_live(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, cls: List<&2, SV.Class>, +h: DR.Longs(~F, env, es, SV.live_nd(cls))) -> DR.Longs(~F, env, es, SV.amber_nd(cls)):
  match cls:
    case Nil{}:
      Unit{}
    case Con{+k, +t}:
      DCL.longs_join(~F, env, es, SV.amber_nd.of(k), SV.amber_nd(t), an_of(~F, env, es, k, DAM.longs_l(~F, env, es, SV.live_nd.of(k), SV.live_nd(t), h)), an_live(~F, env, es, t, DAM.longs_r(~F, env, es, SV.live_nd.of(k), SV.live_nd(t), h)))

# Existence, for any answer whose final2 passes
# ---------------------------------------------


def ex2.f2(~F: O.OField, +y: M.Vec(~F), +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}, h2: DH.Honest(sk, SO.Out.cls(x)), +hz: SK.Zeros(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))), +hl: DR.Longs(~F, y, SV.ents(sk), SV.live_nd(SO.Out.cls(x))), +hsm: SK.Sides(~F, y, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk))),
  +hf: {HR.hfacts(sk, SO.Out.cls(x)) == True{} : Bool}, q: DP.AllFacts(~F, y, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(SO.Out.cls(x)), SV.ncons(sk)), sk, SO.Out.cls(x), True{}, 0n)) & DFC.Amb.go(sk, SO.Out.cls(x), SV.ncons(sk), 0n)) -> SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk)):
  match q:
    case (+af, amb):
      DAM.amber_law(~F, sk, SPF.wf_of(sk, g0, x, fin_of(sk, g0, x, h)), SO.Out.cls(x), h2, y, MN.sketch_sound(~F, y, SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk), WF.wf_ok(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk), WC.wf_mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk, SPF.wfd_of(sk, g0, x, fin_of(sk, g0, x, h)))),
        (zr3(~F, y, sk, SO.Out.cls(x), hf, af, hl, hz), hsm)), an_live(~F, y, SV.ents(sk), SO.Out.cls(x), hl))

def ex2.f1(~F: O.OField, +y: M.Vec(~F), +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}, h2: DH.Honest(sk, SO.Out.cls(x)), +hz: SK.Zeros(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))), +hl: DR.Longs(~F, y, SV.ents(sk), SV.live_nd(SO.Out.cls(x))), +hsm: SK.Sides(~F, y, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk))),
  q: ({HR.hfacts(sk, SO.Out.cls(x)) == True{} : Bool} & (DP.AllFacts(~F, y, SV.ents(sk), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(SO.Out.cls(x)), SV.ncons(sk)), sk, SO.Out.cls(x), True{}, 0n)) & DFC.Amb.go(sk, SO.Out.cls(x), SV.ncons(sk), 0n)))) -> SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk)):
  match q:
    case (+hf, q2):
      ex2.f2(~F, y, sk, g0, x, h, h2, hz, hl, hsm, hf, q2)

def ex2.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}, h1: DH.Honest(sk, SO.Out.cls(x)), h2: DH.Honest(sk, SO.Out.cls(x)), s: Sigma<&2, &2, M.Vec(~F), y => M.Both(BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y), SK.Zeros(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))))>)
  -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  (+y, hy) = s
  (+hin, +hz) = hy
  +hl = sd_longs(~F, y, SV.ents(sk), SV.live_nd(SO.Out.cls(x)), PP.box_sides(~KI.dnum(), ~F, ~H, DR.ndsides(SV.ents(sk), SV.live_nd(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), nd_of(sk, g0, x, h), y, hin))
  +hsm = PP.box_sides(~KI.dnum(), ~F, ~H, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk)), SO.Out.gc(x), SO.Out.gr(x), SPF.hE(sk, g0, x, fin_of(sk, g0, x, h)), y, hin)
  (y, (hin, ex2.f1(~F, y, sk, g0, x, h, h2, hz, hl, hsm, DFC.facts_hold(~F, y, sk, SO.Out.cls(x), h1, hz))))

def exists2_of(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {DSO.final2(sk, g0, x) == True{} : Bool}, h1: DH.Honest(sk, SO.Out.cls(x)), h2: DH.Honest(sk, SO.Out.cls(x)))
  -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  ex2.go(~F, ~H, sk, g0, x, h, h1, h2, PP.plan_exists(~KI.dnum(), ~F, ~R, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x), SPF.hD(sk, g0, x, fin_of(sk, g0, x, h))))

# Blame: a support has no red member
# ----------------------------------

def nin_c2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, b: Bool, h: DH.Fate.pick(sk, cls, red, ds, c, b, SV.Conflict{s, nd})) -> {SV.none_in(s, red) == True{} : Bool}:
  match b:
    case True{}:
      absurd({SV.none_in(s, red) == True{} : Bool}, h)
    case False{}:
      (+hb, r) = h
      L.band_r(SV.all_driving(sk, s), SV.none_in(s, red), L.band_r(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red)), L.band_r(SV.distinct(s), SV.band(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, red))), hb)))

def nin_fate2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, k: SV.Class, b: Bool, h: DH.Fate.pick(sk, cls, red, ds, c, b, k)) -> {SV.none_in(SV.support.of(k), red) == True{} : Bool}:
  match k:
    case SV.Kept{d}:
      {==}
    case SV.Amber{d, r}:
      {==}
    case SV.Over{j, s, w}:
      {==}
    case SV.Conflict{+s, +nd}:
      nin_c2(sk, cls, red, ds, c, s, nd, b, h)

def sn2.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, b: Bool, e: {SV.lt(c, SV.ncons(sk)) == b : Bool}, H: DH.Honest(sk, cls)) -> {SV.none_in(SV.support(cls, c), SV.reds(cls)) == True{} : Bool}:
  match b:
    case True{}:
      +hk = Equal.trans(Bool, KA.natle(1n+c, SV.ncons(sk)), SV.lt(c, SV.ncons(sk)), True{}, Equal.sym(Bool, SV.lt(c, SV.ncons(sk)), KA.natle(1n+c, SV.ncons(sk)), L.lt_sv(c, SV.ncons(sk))), e)
      nin_fate2(sk, cls, SV.reds(cls), SV.dropped(cls), c, SV.class_at(cls, c), SV.driven(sk, c), (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : DH.Fate(sk, cls, _)
        DCL.fate_at(sk, cls, SV.ncons(sk), 0n, c, DCL.hon_go(sk, cls, H), hk)))
    case False{}:
      BLM.nin_past(cls, c, SV.reds(cls), (%Equal.sym(Nat, SV.clsn(cls), SV.ncons(sk), DCL.hon_len(sk, cls, H)) : {SV.lt(c, _) == False{} : Bool}
        e))

# an honest classification of the draft: no support has a red member
def supp_nin2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, H: DH.Honest(sk, cls)) -> {SV.none_in(SV.support(cls, c), SV.reds(cls)) == True{} : Bool}:
  sn2.go(sk, cls, c, SV.lt(c, SV.ncons(sk)), {==}, H)

def blame2_m(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +x: SO.Out, +c: Nat, +hn: {SV.none_in(SV.support(SO.Out.cls(x), c), SV.reds(SO.Out.cls(x))) == True{} : Bool}, +y: M.Vec(~F),
  p: (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk)))) -> &y: M.Vec(~F) -> SK.Sketch.means(~F, y, SV.only(SV.support(SO.Out.cls(x), c), sk)):
  match p:
    case (hin, hm):
      (y, BLM.mo(~F, y, SV.support(SO.Out.cls(x), c), SV.reds(SO.Out.cls(x)), sk, hn, hm))

def blame2_pair(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +x: SO.Out, +c: Nat, +hn: {SV.none_in(SV.support(SO.Out.cls(x), c), SV.reds(SO.Out.cls(x))) == True{} : Bool},
  s: &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk)))) -> &y: M.Vec(~F) -> SK.Sketch.means(~F, y, SV.only(SV.support(SO.Out.cls(x), c), sk)):
  match s:
    case (+y, p):
      blame2_m(~F, ~H, sk, x, c, hn, y, p)

# The laws, for the draft solver
# ------------------------------

def solve_exists2(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool})
  -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk))):
  exists2_of(~F, ~R, ~H, sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok), hon2(sk, g0, l, ok), hon2(sk, g0, l, ok))

def solve_unique2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)),
  +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  SPF.unique_of(~F, ~H, sk, g0, DSO.solve_l2(sk, g0, l), fin_of(sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok)), x1, h1, m1, x2, h2, m2)

def solve_pins2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(DSO.solve_l2(sk, g0, l)), g0, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l))) == True{} : Bool}:
  SPF.pins_of(sk, g0, DSO.solve_l2(sk, g0, l), fin_of(sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok)))

def solve_regular2(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +x: M.Vec(~F), +h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x), m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)))
  -> DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(DSO.solve_l2(sk, g0, l)))):
  REG.regular_of(~F, ~H, sk, g0, DSO.solve_l2(sk, g0, l), fin_of(sk, g0, DSO.solve_l2(sk, g0, l), verdict2(sk, g0, l, ok)), x, h)

def solve_blame2(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +c: Nat) -> &x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c), sk)):
  blame2_pair(~F, ~H, sk, DSO.solve_l2(sk, g0, l), c, supp_nin2(sk, SO.Out.cls(DSO.solve_l2(sk, g0, l)), c, hon2(sk, g0, l, ok)), solve_exists2(~F, ~R, ~H, sk, g0, l, ok))

# The extended Honest's laws, for the draft solver
# ------------------------------------------------


# the classification is honest, at every level, ok or not
def solve_honest2(+sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> DH.Honest(sk, SO.Out.cls(DSO.solve_l2(sk, g0, l))):
  DPP.pass2_honest(sk, w, cov)

def solve_drop2(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l))))), +j: Nat, hj: {SV.mem(j, SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l)))) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(SO.Out.cls(DSO.solve_l2(sk, g0, l)), j)))
  -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  DFC.drop_law(~F, sk, SO.Out.cls(DSO.solve_l2(sk, g0, l)), solve_honest2(sk, w, cov, g0, l), x, hz, j, hj, hl)

def am2.w(~F: O.OField, +sk: SK.Sketch, +hw: {WF.wf_dec(sk) == True{} : Bool}, cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F),
  m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.ambers(SO.Out.cls(DSO.solve_l2(sk, g0, l)))), sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(SO.Out.cls(DSO.solve_l2(sk, g0, l))))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)):
  DAM.amber_law(~F, sk, WF.wf_ok(sk, hw), SO.Out.cls(DSO.solve_l2(sk, g0, l)), solve_honest2(sk, WF.wf_ok(sk, hw), cov, g0, l), x, m, hl)

def solve_amber2(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.ambers(SO.Out.cls(DSO.solve_l2(sk, g0, l)))), sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(SO.Out.cls(DSO.solve_l2(sk, g0, l)))))
  -> SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)):
  am2.w(~F, sk, WC.wf_dec_ok(sk, w), cov, g0, l, x, m, hl)

def solve_conflict2(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +c: Nat, hc: {SV.is_conflict(SV.class_at(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c)}, sk)),
  hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c))) -> Empty:
  DCL.conflict_law(~F, sk, SO.Out.cls(DSO.solve_l2(sk, g0, l)), solve_honest2(sk, w, cov, g0, l), c, hc, x, m, hl)
