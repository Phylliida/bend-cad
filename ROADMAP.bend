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
import ./spec/deriv.bend as DV
import ./lib/kinst.bend as KI
import ./lib/wfdec.bend as WF
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

# Completeness (sk-09, DESIGN §10.2). DRAFTS FOR REVIEW, with
# spec/deriv.bend and the "for completeness" part of spec/solve.bend.
# solve_total is proven (lib/totalpf.bend; restated with its proof in
# tests/solve_laws.bend); solve_complete is open.
# --------------------------------------------------------------------
# solve_l(sk, g, l) is the solver at level l: it tries seven precisions
# of 64, 96, 128, 192, ... (doubling every two), starting at the l-th, and
# takes the first whose answer passes the whole verdict; solve is level 0
# (64 .. 512 bits), and a higher level is "try harder" (it never tries the
# coarse precisions, which can lose a drawing's detail). red_of(sk),
# why_of(sk) and pins_of(sk) are its red constraints, their reasons and
# its pins, computed from the sketch alone (lib/solve.bend).

# LAW: the structure stage never fails. For a well-formed sketch
# whose variables cover it, whatever the drawing and the level: the red
# constraints, reasons and pins solve reports are those of the sketch
# alone; every red constraint is explained; the sketch less them passes
# the solver's well-formedness check; the pins are distinct variables;
# and with the pins held the kept system is square (as many equations as
# free variables). (Proof: lib/dfspf.bend, the augmenting-path search and
# its witness; lib/redpf.bend, the red stage; lib/wfcpf.bend and
# lib/covpf.bend, well-formedness and coverage; lib/totalpf.bend, the
# pins. The pins are the structure's when they make the kept system
# square, which Kuhn's theorem says they always do; that theorem is not
# proven, so otherwise they are the red stage's free variables, which
# provably do.)
law solve_total:
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  M.Both({SO.Out.red(SO.solve_l(sk, g0, l)) == SO.red_of(sk) : List<&2, Nat>}, M.Both({SO.Out.why(SO.solve_l(sk, g0, l)) == SO.why_of(sk) : List<&2, SV.Why>}, M.Both({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>}, M.Both({SV.explained(sk, SO.red_of(sk), SO.why_of(sk)) == True{} : Bool}, M.Both({WF.wf_dec(SV.mark(SO.red_of(sk), sk)) == True{} : Bool}, M.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, M.Both({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}, {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat})))))))

# LAW (open, the hard one): a regular solution near the drawing is
# certified. In a complete ordered field F, take a well-formed sketch
# whose variables cover it and whose constants are dyadic, a drawing g0,
# and a point x with one entry per variable that equals g0 at the pins,
# solves the sketch less its red constraints, meets its side conditions
# strictly (spec/solve.bend: Strict), and is a regular point of that
# system in the free variables the solver chose (spec/deriv.bend: the
# Jacobian has an inverse; the free variables are chosen structurally,
# from the order of the variables, so a solution that is regular only in
# other free variables is not covered: e.g. a point on a vertical line
# whose only unknown is the line's far end). Then there are d > 0 and a
# level l such that from every drawing within d of x (at every free
# variable) that agrees with g0 at the pins, solve_l certifies, and x is
# in its box (so, by solve_unique, x is the geometry it certifies).
# (Audited 2026-10-14: the first draft was false for two reasons, both
# fixed in the solver: side conditions were checked only after the
# precision loop, so a box too wide for one was never retried; and every
# budget began at 64 bits, where rounding can lose the drawing's detail and
# certify a neighbouring solution, which levels now skip.)
law solve_complete:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for  dy: {SV.dyadic(sk) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +x: M.Vec(~F)
  for  hl: {M.len(~F, x) == SO.nvars(sk) : Nat}
  for  hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, SO.pins_of(sk), g0)
  for  hz: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk)))
  for  hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SO.red_of(sk), sk)))
  for  hr: DV.Regular(~F, x, SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk)), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))
  (&d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, SO.pins_of(sk), g0) -> ({SO.Out.ok(SO.solve_l(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g, l)), SO.Out.gr(SO.solve_l(sk, g, l)), x))))))
