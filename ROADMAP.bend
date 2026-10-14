# bend-cad: laws planned but not proven yet (open claims), and drafts
# awaiting review. Not imported by PROOF.bend, so the gate stays
# meaningful. Checking this file reports its laws as TODOs (before
# type-checking); drafts that are proven are restated with their proofs in
# tests/, and tools/lawsync.py (in the gate) checks the two say the same.

import Base
import ./LAWS.bend as Laws
import ./spec/num.bend as S
import ./spec/field.bend as O
import ./spec/mat.bend as M
import ./spec/knum.bend as N
import ./spec/real.bend as CR
import ./spec/sketch.bend as SK
import ./spec/box.bend as BX
import ./spec/solve.bend as SV
import ./lib/kinst.bend as KI
import ./lib/solve.bend as SO

# The verified solver (sk-09, DESIGN §10). DRAFTS FOR REVIEW, with
# spec/solve.bend. All four are proven (lib/solvepf.bend; restated with
# their proofs in tests/solve_laws.bend). Audited by a fresh agent
# (2026-10-14): no blocker; its two fixes are in (red flags must leave
# no spare: each red constraint's witness uses only kept constraints and
# itself; pins are reported and held at the drawing).
# ----------------------------------------------------------------------
# solve(sk, g0) (lib/solve.bend) takes a sketch and a drawing (one dyadic
# value per variable) and answers with ok, a box (centers gc and radii gr,
# dyadics), a plan (input to the checker; it never appears in a claim),
# the variables it pinned, and the constraints it flagged red (by
# position) with their reasons. When ok is True:
# - solve_exists: in every complete ordered field some geometry in the
#   box means the sketch with the red constraints made driven
#   (spec/solve.bend: mark);
# - solve_unique: in every ordered field only one does (given the box's
#   radius-0 coordinates: the pins and anything solved exactly);
# - solve_red: every red constraint is explained, and none is spare
#   (spec/solve.bend: explained);
# - solve_pins: every pin has radius 0 and sits exactly at its drawn value
#   (spec/solve.bend: held), so pinning never moves what the user drew.
# The laws say nothing yet about where the box is relative to the drawing
# (it could be a mirrored branch), nor about a red constraint at the
# solution (its deviation, sk-19). H is any ring map from the dyadics into
# F with sound comparisons: KI.demb is one, and e_ofq makes every such map
# agree with it on every dyadic, so the box is read at its own numbers.
# The statements also use lib/solve.bend's Out type and its projections
# (Out.ok, Out.gc, ...), one-line field reads: part of what is reviewed.
#
# solve recomputes its verdict from its answer alone (lib/solve.bend:
# seal), so the proofs use nothing about how the answer was found.

# LAW: in a complete ordered field, the solver's box holds a geometry
# meaning the sketch less its red constraints
law solve_exists:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}
  (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x) & SK.Sketch.means(~F, x, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))))

# LAW: in every ordered field, only one geometry in the solver's box means
# it
law solve_unique:
  for ~F: O.OField
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}
  for +x1: M.Vec(~F)
  for  h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x1)
  for  m1: SK.Sketch.means(~F, x1, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))
  for +x2: M.Vec(~F)
  for  h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x2)
  for  m2: SK.Sketch.means(~F, x2, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))
  {x1 == x2 : M.Vec(~F)}

# LAW: every red constraint is explained: it owns an equation in a set of
# the sketch's equations that uses fewer variables than it has equations,
# made only of its own and kept constraints' equations
law solve_red:
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}
  {SV.explained(sk, SO.Out.red(SO.solve(sk, g0)), SO.Out.why(SO.solve(sk, g0))) == True{} : Bool}

# LAW: every pin is held at the drawing's value, with radius 0
law solve_pins:
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}
  {SV.held(SO.Out.pins(SO.solve(sk, g0)), g0, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0))) == True{} : Bool}

# Completeness (sk-09, DESIGN §10.2): planned, statements not yet drafted.
# - solve_total: the structure stage never fails: on every sketch the red
#   constraints the search reports are explained, and the sketch less them
#   is well formed and covered whenever the sketch is.
# - solve_complete: in a complete ordered field, a regular solution of the
#   sketch less its red constraints, with the pins at the drawing's values
#   and every side condition strictly positive (or variable-free), is
#   certified from every drawing close enough to it, at some precision
#   budget. Needs a Jacobian in the spec (derivatives of QExpr) and a
#   budget parameter on solve (the default budget stops at 512 bits).
