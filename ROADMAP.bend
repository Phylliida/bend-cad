# bend-cad: laws planned but not proven yet (open claims). Not imported by
# PROOF.bend, so the gate stays meaningful. Checking this file reports its
# open laws as TODOs; that is expected.

import Base
import ./LAWS.bend as Laws
import ./spec/ring.bend as E
import ./spec/field.bend as O
import ./spec/mat.bend as M
import ./spec/knum.bend as N
import ./spec/real.bend as CR
import ./spec/sketch.bend as SK
import ./spec/box.bend as BX
import ./lib/plan.bend as PL

# Composition (sk-06, DESIGN §8.4). DRAFT FOR REVIEW.
# --------------------------------------------------
# A system is a list of equations over variables 0, 1, ... (the sketch's
# equations, pins made into radius-0 variables). A box gives each variable
# a center and a radius in the computing numbers K. A plan (lib/plan.bend:
# blocks in order, each with its unknowns, parameters, equations and a
# certificate) is checked by lib/plan.bend's checker; it never appears in
# the claim. The claim: the box holds exactly one solution of the system,
# and every point of the box meets the side conditions.

# LAW: in a complete ordered field, the box holds a solution of the system
law plan_exists:
  for ~K: N.Num
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<K, F>
  for +eqs: List<&2, E.QExpr>
  for +gc: N.KVec(~K)
  for +gr: N.KVec(~K)
  for +p: PL.Plan<K>
  for  ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}
  Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>

# LAW: in every ordered field, the box holds at most one solution
law plan_unique:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +eqs: List<&2, E.QExpr>
  for +gc: N.KVec(~K)
  for +gr: N.KVec(~K)
  for +p: PL.Plan<K>
  for  ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}
  for +x1: M.Vec(~F)
  for  h1: BX.inbox(~K, ~F, ~H, gc, gr, x1)
  for  z1: SK.Zeros(~F, x1, eqs)
  for +x2: M.Vec(~F)
  for  h2: BX.inbox(~K, ~F, ~H, gc, gr, x2)
  for  z2: SK.Zeros(~F, x2, eqs)
  {x1 == x2 : M.Vec(~F)}

# LAW: in every ordered field, every point of the box meets the side
# conditions the checker certified (e > 0, or e >= 0). Proven
# (lib/planpf.bend: ball enclosures over the box, a comparison in K); moves
# to LAWS.bend once the statement is reviewed.
law box_sides:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +sides: List<&2, SK.Side>
  for +gc: N.KVec(~K)
  for +gr: N.KVec(~K)
  for  ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}
  for +x: M.Vec(~F)
  for  h: BX.inbox(~K, ~F, ~H, gc, gr, x)
  SK.Sides(~F, x, sides)
