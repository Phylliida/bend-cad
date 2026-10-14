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

# Composition (sk-06, DESIGN §8.4). DRAFT FOR REVIEW. All five sk-06 laws
# (these three and the two sketch laws below) are proven in
# lib/planpf.bend; tests/plan_laws.bend restates them with their proofs, and
# the gate checks the restatements match these statements (tools/lawsync.py).
# --------------------------------------------------
# A system is a list of equations over variables 0, 1, ... (the sketch's
# equations, pins made into radius-0 variables). A box gives each variable
# a center and a radius in the computing numbers K. A plan (lib/plan.bend:
# blocks in order, each with its unknowns, parameters, equations and a
# certificate) is checked by lib/plan.bend's checker; it never appears in
# the claim. The claim: the box holds exactly one solution of the system,
# and every point of the box meets the side conditions. "Exactly one" is
# given the radius-0 coordinates: the proposer may pin free degrees of
# freedom (§8.1), and the statement cannot tell them from fixed ones. A
# variable past the box's end would read 0 in Zeros; these laws are about
# systems over the box's variables, which the checker enforces (it rejects
# an equation naming a later variable), and the sketch laws below state
# their coverage as a hypothesis.

# LAW: in a complete ordered field, the box holds a solution of the system.
# Proven (lib/planpf.bend: the blocks in order, each extended by its Banach
# point); moves to LAWS.bend once the statement is reviewed.
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

# LAW: in every ordered field, the box holds at most one solution. Proven
# (lib/planpf.bend: pinned coordinates are their centers; then block by
# block, both solutions' stretches lie in the certificate's box and are
# zeros of the block at the same parameters, so cert_unique makes them
# equal); moves to LAWS.bend once the statement is reviewed.
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

# Sketches (sk-06 capstone). DRAFT FOR REVIEW.
# --------------------------------------------
# For a sketch whose exact system (Sketch.eqs) has a checked plan, with a
# box that covers every variable the sketch names (spec/box.bend:
# Sketch.within; a shorter box would silently read the rest as 0): in every
# complete ordered field, if the sketch is well formed and its side
# conditions (Sketch.sides) are checked over the box, there is a geometry
# in the box where every circle and arc is proper and every driving
# constraint means what it says (sk-07's meaning laws); and in every ordered
# field only one geometry in the box does (given the radius-0
# coordinates). Both follow from the laws above with sketch_sound and
# sketch_complete. Degenerate geometry is allowed (sk-03): a segment may
# collapse, and then parallel, perpendicular and on-line hold of it.

# LAW: in a complete ordered field the box holds a geometry meaning the sketch
law sketch_exists:
  for ~K: N.Num
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<K, F>
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +gc: N.KVec(~K)
  for +gr: N.KVec(~K)
  for  cov: {BX.Sketch.within(sk, List.length(&2, N.NC(K), gc)) == True{} : Bool}
  for +p: PL.Plan<K>
  for  ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}
  for  os: {PL.check_sides(~K, SK.Sketch.sides(sk), gc, gr) == True{} : Bool}
  (&x: M.Vec(~F) -> (BX.inbox(~K, ~F, ~H, gc, gr, x) & SK.Sketch.means(~F, x, sk)))

# LAW: in every ordered field, at most one geometry in the box means the sketch
law sketch_unique:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +sk: SK.Sketch
  for +gc: N.KVec(~K)
  for +gr: N.KVec(~K)
  for  cov: {BX.Sketch.within(sk, List.length(&2, N.NC(K), gc)) == True{} : Bool}
  for +p: PL.Plan<K>
  for  ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}
  for +x1: M.Vec(~F)
  for  h1: BX.inbox(~K, ~F, ~H, gc, gr, x1)
  for  m1: SK.Sketch.means(~F, x1, sk)
  for +x2: M.Vec(~F)
  for  h2: BX.inbox(~K, ~F, ~H, gc, gr, x2)
  for  m2: SK.Sketch.means(~F, x2, sk)
  {x1 == x2 : M.Vec(~F)}
