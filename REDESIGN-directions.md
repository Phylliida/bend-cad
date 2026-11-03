# The direction layer from the goal, minimized (2026-11-02)

Danielle asked for this after C0 (spec/_draft13c.bend, 977fa18) smelled of
fixes on top of fixes: write down what is needed, question every design
constraint, and propose, critique and minimize until it is simple.
- **Part 1** (iterations 0 to 13) stays within B8b.
- **Part 2** (iterations 14 to 27), after "we can go much further", goes
  back to the decision B8b's problems come from.

If its question is answered yes, Part 2 replaces Part 1. Nothing here is
built.

## Part 1: B8b

**0. Start: B8b as planned, with what C0's review added.**
Objects: NdIrred, RefIrred, OverIrred; ValidA; placeholder facts; A
threaded through the closure and its proofs; a deletion loop per segment.
On top of those come the three patches from the review: Angle and
LineDistance exceptions, irreducible sources, and page filters with hover
wording.

**1. The goal, and the constraints.**
- N1. The classification is decided by the sketch, and complete for the
  calculus (honest_unique). *Necessary* (trusted everything is verified
  and complete).
- N2. The certified drawing satisfies every constraint that is not red.
  *Necessary*: it is the product.
- N3. The solver never refuses a drawing at which some derivation of each
  live drop holds. *Necessary*: you asked for every case.
- N4. Everything the page says is proven. *Necessary.*
- N5. The sets the page shows are minimal. *Examine.*

**2. What B8b buys.** It buys N3 and N5. But irreducible nd serves N3 only
if the minimal sufficient set is unique. Then it is contained in every
sufficient set, so if any derivation holds at a drawing, the recorded one
does too. Is it unique?
- I tried to build two sufficient sets with neither inside the other, and
  every attempt failed. The constraint that closes the second path is
  itself dropped, through the first path, so its fact carries the first
  path's nd.
- That suggests uniqueness, but it is not proven.
- This corrects my last message, which said two different irreducible
  sets can exist. I had no example.

So B8b's N3 rests on a conjecture.

**3. Serve N3 directly.** Certification asks whether some derivation holds
at this drawing. It does not ask whether the recorded one is minimal.
P1: after the box is known, look, for each live drop, for a derivation
that passes only through segments the box certifies nonzero. That needs
a restricted closure.

**4. The restricted closure is already there.** "May not be passed
through" is what *collapsed* means in the calculus, and the context
decides collapse.
- P2: run the same closure with the context extended by the uncertified
  segments' two direction parts.
- A derivation valid in the bigger context is valid in the original one
  (Open is antitone in the context).
- Every segment it passes through is open there, so not uncertified.

This removes ValidA, the threading of A, and the second-calculus risk.

**5. Facts from earlier drops.** A derivation found in P2 may read an
earlier drop's fact whose recorded nd the box does not certify. That
doesn't matter. At the drawing, the earlier equation already holds: drops
are checked in order. So the facts can be read as holding outright, which
is DP.sound with the facts' nd dropped (facts.go's withnd False, as rfacts
does). No placeholders are needed.

**6. Where the answer would change.** If the derivation found replaced
the recorded one, the answer's witnesses would depend on the drawing.
solve_exists says `Out.cls(solve_l(..)) == cls_of(sk)`, and that would
break.
P3: the answer stays as it is, and the *verdict* checks, for each live
drop, that it is derivable at the drawing. The classification comes from
the sketch, and the certification from the drawing.

**7. Cost.** A closure per live direction drop at each precision is too
much to pay every time. So today's check stays as the fast path:
- if the recorded nd is certified, accept, as now;
- otherwise run the closure of P2.

The common case costs nothing new. This is an optimization under the same
statement.

**8. The laws.**
- solve_total keeps its statement.
- solve_complete and solve_refused change their hypothesis. Today it is
  "the live drops' recorded nd is nonzero at x*". It becomes "each live
  drop has some derivation, over facts read outright, whose segments are
  nonzero at x*". That is N3 as a theorem, and the weakest condition the
  calculus allows.
- Completeness at x* follows. A derivation valid at x* is valid in the
  extended context: a segment collapsed there is a combination of
  uncertified ones modulo equations that vanish at x*. At a high enough
  precision those are zero at x*, so it is zero too, and was not passed
  through.

**9. N5, examined: two kinds of set.**
- *Removal sets* answer "what do I take out?": the support and the Over
  set. "Remove any one of them" is true only of an irreducible set.
  - The support is irreducible already.
  - The Over set too (OverIrred, decided 2026-11-02).
- *Assumption sets* describe a reason: nd, and the sources. For these, it
  is enough that they are exact for the reason shown and worded as such:
  "its reason needs L4 and L5 to have nonzero length", not "unless".

With that, the three patches go away:
- an Angle's or a LineDistance's segment in nd is a true assumption of
  the reason;
- the order of support against nd stops mattering;
- the sources are described as sufficient.

**10. angle_args.** Under 9's wording a conflict needs no Angle exception.
Removing it would simplify DirRefutes, dconflict's ndclean and the
conflict law's proof. It is optional: what is there is proven.

**11. Drop.nd is stored as well as computed (nd == DR.nd(dv)).** Is that
redundant? Dropping it would make the spec compute the facts' nd
recursively over the constraints. Keep it: here the existing design is
right.

**12. Wider: the spec carries the degree-0 layer twice.**
- A degree-0 drop is a derivation with no nd. PLAN-sk13b already says so:
  "K(e) ... includes sk-13a's degree-0 drops".
- A degree-0 refutation is an RMotz with no nd.
- Yet Honest has WLin, Derivable, NotDerivable, Ref0 and NoRef0 beside
  the direction notions. One calculus would do.

This is outside B8b, and is noted only, not proposed.

**13. Each remaining piece, questioned again.** The fast path is an
optimization, not a concept. The extended context is a list append. The
verdict's new branch is one Or. Nothing else is left.

### Part 1's result

Three things, and one already decided:
1. **The verdict accepts a live drop that is derivable at the drawing.**
   The existing closure, run with the uncertified segments' directions
   added to its context, holds the drop's equation; today's check stays as
   the fast path. The proof needs three things:
   - Open, and so validity, is antitone in the context (a small
     induction);
   - DP.sound with the facts read outright;
   - the closure's two directions, for any context: its positive answer
     gives a derivation (as the pass already uses it), and dclose_closed
     (which already takes ctx) gives completeness for solve_complete.
2. **solve_complete and solve_refused** take the weakest hypothesis
   (iteration 8).
3. **The page's wording:** nd and sources describe the reason; supports
   and Over sets are "remove any one".
4. **OverIrred**, as decided: the only clause Honest gains.

What goes: NdIrred, RefIrred, ValidA, placeholder facts, the threading of
A, the deletion loop, and the three patches.

What is given up is a minimal nd in messages. If that is still wanted, it
is the expensive part. Proving that no derivation avoids a segment needs
the facts filtered and the syntactic nd respected, which the
extended-context trick does not give: in a triangle, collapsing two sides
collapses the third. That would be its own decision, with its own one
statement found first.

## Part 2: further, back to the decision behind B8b

**14. Where nd comes from.** Part 1 questioned B8b's parts, not the
reason B8b exists. nd exists because of Q15 (Danielle, sk-03,
2026-10-13): "Geometry may collapse to zero length: no ℓ_min, no
nondegeneracy conditions on segments". DESIGN v0.6 had > 0 side
conditions on segments, and v0.7 dropped them, together with ℓ_min.
Circles kept r > 0 and arcs b > 0. Every direction rule that passes
through a segment is sound only where that segment is nonzero, so under
Q15 each judgment has to say which segments it needs.

**15. What Q15 costs, as built.**
- **nd everywhere:** Drop.nd, Conflict.nd, facts' nd, DR.nd and ref.nd,
  the laws' `hl` and `hn` hypotheses, the verdict's ndok, the page's
  "unless" and "where" text.
- **The context, Open and Collapsed**, so that derivations do not pass
  through segments known to be zero. Every Honest notion takes `ctx`.
- **In the closure:** links from collapsed segments, their sets
  (full/free/tied), and the open test (dcopenpf, dclinkpf, dcreppf,
  dctiedpf, dcftiepf, and parts of most other dc*pf files).
- **∥-void and RAngle:** two rules that exist only for collapsed segments.
- **angle_args:** the conflict exception for Angles.
- **Decision 4's limit:** a later constraint that collapses a segment an
  earlier one uses leaves the system singular, so it is refused with
  nothing red.
- **All of B8b**, and the three patches the C0 review proposed.

**16. What Q15 buys.** It makes zero-length segments legal geometry. Who
needs that?
- On a zero-length segment, every direction constraint holds vacuously
  (Parallel, Perpendicular, OnLine, Symmetric). Angle and LineDistance
  cannot hold at all: their meanings already require nonzero length.
- The page never makes a segment from a point to itself (ui.js checks
  `q.id !== from`).
- Circles and arcs already mean nondegenerate.
- If ℓ_min was the concern in sk-03, it no longer applies. With exact
  certification, a strict side needs no ℓ_min: the box only has to
  exclude 0, as it does for r > 0.

I don't know Danielle's reason for Q15. That is the question this part
turns on.

**17. Proposal: a segment means a segment.**
- Ent.sides gains |q − p|² > 0 for GSeg, the way GCirc has r > 0.
- Ent.means gains p ≠ q.
- Ent.wf_refs adds that p and q are not the same two variables, so no
  segment is identically zero.

Then wherever the sketch holds, every segment is nonzero, and the
verdict's existing Strict check over Sketch.sides certifies it like any
other side.

**18. The calculus without collapse.** Wherever the premises are
consistent, no segment's direction is in K². So:
- Open is always true, and the context has no other use: it goes.
- A derived collapse of *any* segment is a refutation (RColl without the
  open test). An Angle on a collapsed segment is a case of it, so RAngle
  goes.
- ∥-void never applies in a closure that has not exploded, so it goes.
- The closure keeps K's span, the forest of nodes with labels, the hulls,
  and one explosion check: 1 ∈ K, or a segment's direction in K². Links,
  collapsed sets and the open test go.

**19. What answers change.**
- **par-collapse** (Parallel, then a Coincident collapsing its segment):
  the Coincident is red, "makes L zero length". Today it is refused with
  nothing red. This is decision 4's limit, gone.
- **collapse-par:** the Coincident is red. Today the Parallel is amber,
  vacuously.
- **A Distance 0 between a segment's ends, or a Horizontal and a Vertical
  on the same segment:** red. Today these give a legal zero-length
  segment.
- **par-perp:** a plain conflict, with no "unless".
- **Every other class in the regression should stay the same**, and lose
  its nd. To be confirmed by running it.

**20. What goes with nd.**
- The data: Drop{j, why} and Conflict{s}; facts without nd.
- The laws: solve_amber and solve_conflict lose `hl`, because
  Sketch.means includes the entities' meanings, so every segment is
  nonzero. solve_drop reads only the solved equations, so its `hl`
  becomes "the entity sides hold" (every segment nonzero).
- solve_complete and solve_refused lose `hn`, because hs now includes
  every segment's side.
- The verdict loses ndok.
- angle_args, live_nd, amber_nd, conflict_nd, dnd_at and ndsides go.
- **B8b goes entirely.** There is no nd to minimize, and no certification
  gap: a zero-length segment violates the sketch, so refusing it is right.

**21. Facts.** Decision 3 read every kept equation, dropped ones included,
because a dropped equation could be the only one that knows a segment is
collapsed. With no collapse in any consistent closure, that reason is
gone. Can the facts then shrink to the solved equations, the list degree
0 reads?
- I first wrote yes, but no. A dropped equation's direction statement is
  read by ∥-premise, and no rule turns K(cross(z_a, x)) into ∥(a, x).
  The frame has one (frame), segments do not.
- So a dropped Parallel whose equation is a constant combination of
  solved ones could lose its ∥ fact, and the calculus would derive less.
- The facts stay today's list (every kept equation before c, and c's own
  earlier ones not dropped), only without nd. That list contains the
  solved basis, which is what iteration 22 needs.

**22. One calculus.** Degree 0 is the calculus's K fragment:
- a constant combination is DPrem and DKAdd;
- a degree-0 refutation is an RMotz over premise derivations.

So Honest needs only "dropped iff derivable" and "conflict iff
refutable". Derivable, NotDerivable, WLin, Mul, mlin, in_basis, Ref0,
NoRef0, NoRefute and NoRefute2 go from the spec, and Why is a Der. The
solver keeps its fast linear layer. Its answers become K-derivations by
one embedding lemma.

**23. Amber's sides.** Implied stays degree-0 Motzkin over the premises'
equations, as now. Reading the calculus's derived K facts there would
make more constraints amber, and nothing needs it.

**24. Over.** It is unchanged and irreducible (OverIrred, as decided).

**25. Staging, so that the gate stays green.**
- **Stage 1** gives the behavior and is small: segment sides, wf, and
  `ctx` defined as Nil. The closure and its theorems take any context,
  so with Nil nothing is collapsed and RColl applies to every segment.
  How many proofs unfold `SV.ctx` is to be checked. The page drops the
  nd text: every segment is nonzero by meaning, so it is vacuous.
- **Stage 2:** remove nd and ctx from the spec, the laws and the verdict.
- **Stage 3:** delete the closure's dead collapse code, ∥-void and RAngle,
  and the proofs about them.
- **Stage 4:** one calculus (iteration 22).

**26. What else read Q15?** "Distances may be 0" (d ≥ 0) is separate: two
points that are not a segment's ends may still coincide, and a Distance 0
between them stays fine. Q15's other consequence was in sk-13a's
merges: a Horizontal and a Vertical on one segment makes it zero length.
That becomes a conflict.

**27. Each remaining piece, questioned again.**
- The calculus's rules are the four ways linear facts give a direction
  (PLAN-sk13b's isotropic subspaces), minus void.
- Honest's structure (conflict, then drops, then Over, then kept or
  amber) is the order Q21 needs.
- Nothing nd-shaped is left to question.

### Part 2's result

Three things:
1. **A segment means distinct endpoints:** |q − p|² > 0, as a circle
   means r > 0. Reverses Q15 for segments.
2. **One calculus with no context and no nd.** Degree 0 is its K
   fragment. A collapse of any segment is a conflict.
3. **Over sets irreducible**, as decided.

What goes:
- nd in every form, the context, Open and Collapsed;
- the closure's collapse machinery, ∥-void, RAngle and angle_args;
- decision 4's limit;
- the separate degree-0 notions in Honest;
- all of B8b.

What is given up: zero-length segments as legal geometry.

The question for Danielle: what was Q15 for, and does it still hold?
