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

# The verified solver (sk-09, DESIGN §10), with sk-13a's classes (v5,
# SK13A-REVIEW.md, after four audits; spec/solve.bend). History: the
# sk-09 drafts were audited (2026-10-14), read by Danielle and reviewed
# again (AUDIT-sk09-laws.md: they now hold at every level); sk-13a v5
# replaced the red list and its syntactic witnesses (solve_red) with one
# class per constraint and the honesty laws below (S0b, 2026-10-19).
# ----------------------------------------------------------------------
# solve_l(sk, g0, l) (lib/solve.bend) takes a sketch, a drawing (one
# dyadic value per variable) and a level (how hard to try; solve is level
# 0) and answers with ok, a box (centers gc and radii gr, dyadics), a plan
# (input to the checker; it never appears in a claim), the variables it
# pinned, and a class for each constraint (cls: Kept, Amber, Over,
# Conflict). Below, CLS is its classes, RED = reds(CLS) the red
# constraints and DS = dropped(CLS) the dropped equations; solved(sk,
# RED, DS) is the system solved.
#
# From the verdict (when ok is True, at every level; solve recomputes its
# verdict from its answer alone, lib/solve.bend: seal, so these use
# nothing about how the answer was found):
# - solve_exists: in every complete ordered field some geometry in the
#   box means the sketch with the red constraints made driven;
# - solve_unique: in every ordered field only one does (given the box's
#   radius-0 coordinates: the pins and anything solved exactly);
# - solve_pins: every pin has radius 0 and sits exactly at its drawn
#   value, so pinning never moves what the user drew;
# - solve_regular: that geometry is a regular point of the system solved,
#   in the free variables;
# - solve_blame: every conflict's support holds at some geometry.
# H is any ring map from the dyadics into F with sound comparisons:
# KI.demb is one, and e_ofq makes every such map agree with it on every
# dyadic. The statements also use lib/solve.bend's Out type and its
# projections, one-line field reads: part of what is reviewed.
#
# About the search (every well-formed sketch, ok or not): solve_honest
# (each constraint's class is the honest one given the classes before it,
# spec/solve.bend: Honest) and solve_total; the spec alone: honest_unique
# (honest classes agree, so the sketch determines them); semantic
# corollaries: solve_drop, solve_amber, solve_conflict; completeness:
# solve_complete, and solve_refused, what a refusal means today.
#
# Proven: solve_exists, solve_unique, solve_pins (lib/solvepf.bend),
# solve_regular (lib/regpf.bend), solve_blame (lib/blamepf.bend),
# solve_total and solve_honest (lib/totalpf.bend), and solve_complete
# (lib/completepf.bend), restated in tests/solve_laws.bend. The classes,
# pins and structure are the single pass's (lib/pass.bend; PLAN-sk13a S4,
# switched in S5), and the verdict certifies the dropped equations and
# amber sides by their combinations and refutations (lib/verdict.bend);
# the rest is open (PLAN-sk13a.md S6).

# LAW: in a complete ordered field, the solver's box holds a geometry
# meaning the sketch less its red constraints
law solve_exists:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))))

# LAW: in every ordered field, only one geometry in the solver's box means
# it
law solve_unique:
  for ~F: O.OField
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  for +x1: M.Vec(~F)
  for  h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x1)
  for  m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))
  for +x2: M.Vec(~F)
  for  h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x2)
  for  m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))
  {x1 == x2 : M.Vec(~F)}

# LAW: every pin is held at the drawing's value, with radius 0
law solve_pins:
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  {SV.held(SO.Out.pins(SO.solve_l(sk, g0, l)), g0, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l))) == True{} : Bool}

# LAW: the certified geometry is a regular point of the system solved, in
# the free variables (the verdict checks that the plan's pins are the
# reported pins and that its orders cover exactly the variables and the
# solved equations)
law solve_regular:
  for ~F: O.OField
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  for +x: M.Vec(~F)
  for  h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x)
  for  m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))
  DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(SO.solve_l(sk, g0, l))))

# LAW: every conflict's support is consistent: the certified geometry
# satisfies it (blame is earned)
law solve_blame:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  for +c: Nat
  (&x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), sk)))

# LAW: the classification is honest, at every level, ok or not: each
# constraint's class is the honest one given the classes before it
# (spec/solve.bend: Honest; v4's solve_red is part of it)
law solve_honest:
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  SV.Honest(sk, SO.Out.cls(SO.solve_l(sk, g0, l)))

# LAW (about the spec alone): honest classifications agree. Every
# constraint gets the same kind, and every equation is dropped in both or
# in neither; only the Over witnesses, which irreducible support is shown,
# the pins and the box may differ between solvers
law honest_unique:
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +c1: List<&2, SV.Class>
  for  h1: SV.Honest(sk, c1)
  for +c2: List<&2, SV.Class>
  for  h2: SV.Honest(sk, c2)
  for +c: Nat
  for +j: Nat
  M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool})

# LAW: in every ordered field, wherever the solved equations hold, every
# dropped equation holds
law solve_drop:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  for +x: M.Vec(~F)
  for  hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))))
  SK.Zeros(~F, x, SV.picked(SK.Sketch.eqs(sk), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))))

# LAW: deleting every amber constraint changes no solution
law solve_amber:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  for +x: M.Vec(~F)
  for  m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.ambers(SO.Out.cls(SO.solve_l(sk, g0, l)))), sk))
  SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))

# LAW: in every ordered field, a conflicting constraint and its support
# cannot all hold, so it cannot be restored
law solve_conflict:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  for +c: Nat
  for  hc: {SV.is_conflict(SV.class_at(SO.Out.cls(SO.solve_l(sk, g0, l)), c)) == True{} : Bool}
  for +x: M.Vec(~F)
  for  m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c)}, sk))
  Empty

# Completeness (sk-09, DESIGN §10.2, with sk-13a's classes)
# --------------------------------------------------------
# solve_l(sk, g, l) is the solver at level l: it tries seven precisions
# of 64, 96, 128, 192, ... (doubling every two), starting at the l-th, and
# takes the first whose answer passes the whole verdict; solve is level 0
# (64 .. 512 bits), and a higher level is "try harder" (it never tries the
# coarse precisions, which can lose a drawing's detail). cls_of(sk) and
# pins_of(sk) are its classes and pins, computed from the sketch alone
# (lib/solve.bend).

# LAW: the structure stage never fails. For a well-formed sketch whose
# variables cover it, whatever the drawing and the level: the classes and
# pins solve reports are those of the sketch alone; the sketch less the
# red constraints passes the solver's well-formedness check; the pins are
# distinct variables; and the system solved has a perfect matching onto
# the free variables, by dependence (so with the pins held it is square)
law solve_total:
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +l: Nat
  ({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>} & ({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool} & ({SV.distinct(SO.pins_of(sk)) == True{} : Bool} & ({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m)))))))

# LAW: a regular solution near the drawing is certified. In a complete
# ordered field F, take a well-formed sketch whose variables cover it and
# whose kept constraints' constants are dyadic, a drawing g0, and a point
# x with one entry per variable that equals g0 at the pins, solves the
# system solved, meets the side conditions of the kept constraints that
# are not amber strictly (spec/solve.bend: Strict, where a >= 0 side whose
# variables are all pins may hold with equality; amber sides are
# certified by their refutations instead), and is a regular point of the
# system solved in the free variables the solver chose (spec/deriv.bend;
# the free variables are chosen structurally, from the order of the
# variables: a segment with only a length, drawn horizontal, has p1.x,
# p1.y and p2.x pinned, and the length does not depend on p2.y there; pins
# chosen from the drawing are planned after sk-13a, Q26). Then there are
# d > 0 and a level l such that from every drawing within d of x (at
# every free variable) that agrees with g0 at the pins, solve_l certifies,
# and x is in its box.
law solve_complete:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for  dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for +x: M.Vec(~F)
  for  hl: {M.len(~F, x) == SO.nvars(sk) : Nat}
  for  hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, SO.pins_of(sk), g0)
  for  hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))))
  for  hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk))
  for  hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))
  (&d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, SO.pins_of(sk), g0) -> ({SO.Out.ok(SO.solve_l(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g, l)), SO.Out.gr(SO.solve_l(sk, g, l)), x))))))

# LAW: what a refusal means today: if no level certifies, the drawing
# itself is not a regular solution of the system solved in the solver's
# free variables (as solve_complete reads it). That is all it says;
# solve_refusal_explained (sk-13e) is the stronger form.
law solve_refused:
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for  cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}
  for  dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}
  for +g0: List<&2, S.D>
  for  hn: @l: Nat -> {SO.Out.ok(SO.solve_l(sk, g0, l)) == False{} : Bool}
  for +x: M.Vec(~F)
  for  hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}
  for  hl: {M.len(~F, x) == SO.nvars(sk) : Nat}
  for  hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))))
  for  hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk))
  for  hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))
  Empty
