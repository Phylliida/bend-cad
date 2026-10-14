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
# spec/solve.bend. All three are proven (lib/solvepf.bend; restated with
# their proofs in tests/solve_laws.bend).
# ----------------------------------------------------------------------
# solve(sk, g0) (lib/solve.bend) takes a sketch and a drawing (one dyadic
# value per variable) and answers with ok, a box (centers gc and radii gr,
# dyadics), a plan (input to the checker; it never appears in a claim),
# and the constraints it flagged red with their reasons. When ok is True:
# in every complete ordered field some geometry in the box means the
# sketch with the red constraints made driven (spec/solve.bend: mark); in
# every ordered field only one does (given the box's radius-0 coordinates:
# the pins, held at the drawing's values, and anything solved exactly);
# and every red constraint is explained (spec/solve.bend: explained). H
# is any ring map from the dyadics into F with sound comparisons; there is
# exactly one, so the box is read at its own numbers.
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
# the sketch's equations that uses fewer variables than it has equations
law solve_red:
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}
  {SV.explained(sk, SO.Out.red(SO.solve(sk, g0)), SO.Out.why(SO.solve(sk, g0))) == True{} : Bool}

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
