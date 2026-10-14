# The sk-06 laws, plan-level and sketch-level (ROADMAP.bend, awaiting review) with their proofs
# (lib/planpf.bend), restated here so that the gate checks the proofs
# until the laws move to LAWS.bend.

import Base
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../lib/plan.bend as PL
import ../lib/planpf.bend as PP

def plan_exists(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  PP.plan_exists(~K, ~F, ~R, ~H, eqs, gc, gr, p, ok)

def plan_unique(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), z1: SK.Zeros(~F, x1, eqs), +x2: M.Vec(~F), h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), z2: SK.Zeros(~F, x2, eqs)) -> {x1 == x2 : M.Vec(~F)}:
  PP.plan_unique(~K, ~F, ~H, eqs, gc, gr, p, ok, x1, h1, z1, x2, h2, z2)

def box_sides(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K), ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> SK.Sides(~F, x, sides):
  PP.box_sides(~K, ~F, ~H, sides, gc, gr, ok, x, h)

def sketch_exists(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}, os: {PL.check_sides(~K, SK.Sketch.sides(sk), gc, gr) == True{} : Bool}) -> &x: M.Vec(~F) -> (BX.inbox(~K, ~F, ~H, gc, gr, x) & SK.Sketch.means(~F, x, sk)):
  PP.sketch_exists(~K, ~F, ~R, ~H, sk, w, gc, gr, p, ok, os)

def sketch_unique(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sk: SK.Sketch, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), m1: SK.Sketch.means(~F, x1, sk), +x2: M.Vec(~F), h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), m2: SK.Sketch.means(~F, x2, sk)) -> {x1 == x2 : M.Vec(~F)}:
  PP.sketch_unique(~K, ~F, ~H, sk, gc, gr, p, ok, x1, h1, m1, x2, h2, m2)
