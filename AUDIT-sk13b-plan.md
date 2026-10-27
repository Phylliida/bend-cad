# Audit: PLAN-sk13b.md v1, the trusted part (2026-10-26)

**Verdict: no blocker.** I found no counterexample to the soundness of any
derivation or refutation rule with its stated nondegeneracy, to the global
theorem, to monotonicity of refutation, or to `honest_unique`. Two gaps in
the statements must be closed before B0 (findings 2 and 3). The family's
boundary (finding 1) should be settled first, because it changes
spec/dir.bend.

Rechecked with sympy (scratchpad `audit13b/`: ident.py, cex.py, cexb2.py,
order.py):
- the path lemma;
- cross(P·a, a) = −Im(P)·|a|²;
- dot(a, b) = −cross(i·a, b);
- cross(g·w, v) = −cross(conj(g)·v, w) (backward edges);
- every certificate and Jacobian rank quoted below.

Notation: a segment is written from→to, and dir s = to − from.

## 1. The family is closed only pairwise, so natural dependencies inside it stay refused with nothing red (high, design)

The isotropic-subspace argument is correct for a single relation
cross(g·a, b) against linear facts. Segment directions are not independent,
though. Segments share points, so their directions satisfy linear
identities: dir(A→C) = dir(A→B) + dir(B→C). Derived relations also combine
linearly. The calculus never adds two walk relations together, and never
combines a walk relation with an affine fact.

**Sketch A** (Parallels only).
- Points: A, B, C, D, E.
- Segments: h = D→E, s1 = A→B, s2 = B→C, s3 = A→C.
- Constraints: #0 Parallel{h, s1}; #1 Parallel{s1, s2}; #2 Parallel{h, s3}.

#2 is implied, with nd {s1}:

|s1|²·cross(h,s3) = (|s1|² + dot(s1,s2))·cross(h,s1) + dot(h,s1)·cross(s1,s2).

None of the rules derives it:
- it is not in the span of #0 and #1, so D0 fails;
- s3 has no edge (L contains no linear forms), so D-rel fails;
- D-frame and D-void do not apply.

So #2 is kept. At a generic solution the Jacobian has rank 2 of 3, and the
sketch is refused with nothing red. This contradicts DESIGN §8.11: "These
three layers are complete for their families: every dependency or conflict
among constraints of one family is found."

**Sketch B** (a split edge). It uses the collinearity idiom that sketch(1)
`base` already uses: Parallel on two segments that share a point (#16,
#20 there).
- Points: A, B, C, D, E.
- Segments: h = D→E, s1 = A→B, s2 = B→C.
- Constraints: #0 Horizontal{D, E}; #1 Parallel{h, s1}; #2 Parallel{s1, s2};
  #3 Horizontal{A, C}.

#3 is implied, with nd {h, s1}: h_x·|s1|²·(y_C − y_A) is in the ideal of
#0–#2 (certificate checked). But y_A − y_C = −(s1_y + s2_y) needs two
derived frames, and D-frame admits only one segment. For each of h, s1 and
s2, no λ works (checked). So #3 is kept, the rank is 3 of 4, and the sketch
is refused with nothing red. Replacing #2 with Parallel{h, s2} gives the
same result.

**Sketch V** (an affine fact, and a conflict that is missed).
- Points: A, B, D, E.
- Segments: h = D→E, s = A→B.
- Constraints: #0 Horizontal{D, E}; #1 Parallel{h, s}; #2 VDistance{A, B, 3}.

We have 3·h_x = cross(h,s) − h_x·(y_B − y_A − 3) − (y_D − y_E)·s_x, so h has
length 0 at every solution. The plan's own convention is "A Vertical there
is red". By that convention #2 should be red, "unless h has length 0".

The calculus does not see this:
- s_y − 3 ∈ L is affine, so it gives no Frame fact and no edge, hence no
  closed walk;
- there is no degree-0 refutation.

So #2 is kept. At the solutions (h collapsed) the system is regular (rank
3 of 3). Depending on the pins, the solver either certifies a geometry in
which the horizontal reference has shrunk to a point, or it refuses.

The plan's claim that "the layer is complete for it" holds only relative to
rules whose boundary is arbitrary. D-frame takes one segment, although a
span test costs the same: one rank test against L'. The facts read only the
linear part of L.

Suggested fix, cheapest first:
- **D-frame over a span.** Drop e_i when e_i ∈ L' + span{cross(P_a, dir a) :
  a in F's component}; nd is the union of the walks used.
- **Better: feed derived frames back into the linear layer.** Add these
  derived linear forms to the linear layer as L⁺, each with its nd. Read
  Collapsed, Frame and Tie, and run the degree-0 tests (Motzkin included),
  over L⁺, to a fixpoint. A node collapsed in L⁺ but not in L is a
  refutation. This catches B and V: in V, L⁺ contains the constant 3, with
  nd {h}.
- **Components without F (Sketch A).** Either drop by
  e_i ∈ L' + span{cross(P_uv·dir u, dir v)}, or state the polygon-identity
  limit and correct DESIGN §8.11.

Each option keeps every definition a function of P, so `honest_unique`'s
induction and monotonicity in S still go through.

## 2. ConflictOk must bind nd, and the stated nd of D-rel and D-void is incomplete (high, statement)

**ConflictOk.** `solve_conflict` is proven from `Honest`
(lib/conflawpf.bend goes through solve_honest), not from the verdict. As
written, ConflictOk only "reads a refutation in either", so nd is free
data. Counterexample:
- segments a, b; #0 Parallel{a, b}; #1 Perpendicular{a, b};
- the class Conflict{[0], nd = []} satisfies ConflictOk as written;
- the restated `solve_conflict` would then say #0 and #1 can never both
  hold, which is false at a = 0.

Fix: ConflictOk requires a refutation whose segments all lie in nd (for
degree 0, any nd will do). Irreducibility stays as it is: without a
member, there is no refutation of either kind, whatever nd.

**Inherited nd.** D-rel's nd is not just the walk's interior, and D-void's
is not always empty. L = span(P) contains direction-dropped equations, so
an edge, frame, tie or collapse that uses one of them inherits that
equation's nd. Decision 3 says this, but the rules as written do not.
Counterexample:
- Points: P, Q, R, X, Y.
- Segments: s1 = P→Q, s2 = Q→R, s3 = P→R, k = X→Y.
- Constraints:
  - #0 Horizontal{P, Q};
  - #1 Parallel{s1, s2};
  - #2 Horizontal{P, R}, dropped by D-frame through s2 with nd {s1};
  - #3 Horizontal{X, Y};
  - #4 Parallel{s3, k}.

s3's frame fact y_R − y_P ∈ L is #2's dropped equation, and #4's walk
s3–F–k has an empty interior. So the text gives nd = [], but no certificate
over the solved system exists without |s1|². At P = Q, s2 is free, so #2
and then #4 can fail.

For drops, the verdict enforces the right nd (solve_drop is proven from
the checks), so a wrong nd causes a refusal, not unsoundness. Still, write
each rule's nd as "the walk's interior ∪ the nd of the dropped equations
used", so that B4 has the right proof target. D-void inherits an nd only
in pathological cases, for example an HDistance whose d is a polynomial.

## 3. "A kept drop's nd" must mean the drops of every constraint that is not red (medium, statement)

The verdict already checks Kept and Amber drops alike (lib/verdict.bend:
`kdrops.ok`). The proofs need the nd of amber drops checked over the box
too:
- `solve_exists`: every constraint that is not red holds at the certified
  geometry;
- `solve_blame`: a support may contain amber constraints.

`solve_complete`'s new hypothesis must name the same set as the verdict.
Otherwise it is false at an x* where an amber's nd segment is 0, because
the verdict refuses there. Write "the drops of every Kept or Amber
constraint" in the verdict, in `solve_complete` and in `solve_refused`.

## 4. Decision 4: the outcome is right, but the cause is broader and older, and there is a principled fix (medium, design)

**Simplest case:** segments a, b; #0 Parallel{a, b}; #1 Coincident{b.p, b.q}.
- The solved system is {cross(a,b), b_x, b_y}.
- At b = 0 its rank is 2 of 3: the gradient of cross(a,b) lies in the span
  of the collapse's gradients.
- It is refused in sk-13a and in sk-13b, with nothing red.
- In the other order, #0 is amber by D-void and the sketch certifies.

So B8's "a Coincident collapsing a segment in a direction (amber)" holds
only when the Coincident comes first.

**Decision 4's case** is this case with a drop added:
- #0 Parallel{a, b}; #1 Parallel{b, c}; #2 Parallel{a, c} (amber, nd {b});
  #3 Coincident{b.p, b.q}.
- The solved system {cross(a,b), cross(b,c), b_x, b_y} has rank 2 of 4 at
  b = 0, so the sketch is refused whatever #2's nd says.

Whenever the collapsed interior segment has a solved direction equation and
the collapse comes from solved linear equations, the refusal is caused by
this singularity, not by the nd check. The nd check alone causes a refusal
only when the segment's walk edges are linear facts or dropped equations
(finding 5 has such a case). The plan's "Rare: needs a zero-length segment
in a chain" understates the scope: any later collapse of a segment that has
a kept direction constraint is refused.

**Principled fix: judge the linear constraints first.** Judge the
constraints of degree ≤ 1 first, then the rest, each group in sketch order.
This is the "exact linear presolve" that SK13A-REVIEW lists as the next
step. Collapse, Frame and Tie facts are then final by the time directions
are judged, and both sketches above certify:
- in the simplest case, #0 is amber (solved {b_x, b_y}, rank 2 of 2);
- in Decision 4's sketch, #0 and #1 are amber and #2 is kept (rank 3 of 3).

D-frame then matters only for nonlinear equations with a linear remainder,
and I could not construct one. `honest_unique` is unaffected, since any
fixed order works.

The cost: in mixed dependencies, blame moves to the direction constraint.
- In "Horizontal on a segment parallel to a horizontal one", the Parallel
  becomes amber, not the Horizontal.
- In the Vertical variant, the Parallel is red.

This is Danielle's decision. If she declines it, DESIGN should say the limit
belongs to the order rule and is already present in sk-13a. Judging linear
constraints first does not fix finding 1: Sketches B and V are missed in
either order.

## 5. nd is not canonical, and the choice of walk alone can refuse a sketch (medium)

`Honest` does not fix nd. Yet the verdict, `solve_complete`'s hypothesis
and `solve_refused` all depend on it, so two honest solvers can disagree
about whether a sketch certifies. Union–find walks pass through roots or
tie-group representatives, which adds segments the identity does not need.

Example (contrived, but it isolates the effect):
- Points: Y0, Y1, B0, B1, Z0, Z1.
- Segments: y = Y0→Y1, b = B0→B1, z = Z0→Z1.
- Constraints:
  - #0–#3 HDistance{Y0,B0,3}, VDistance{Y0,B0,1}, HDistance{Y1,B1,3},
    VDistance{Y1,B1,1} (b is y moved);
  - #4–#7 HDistance{B0,Z0,2}, VDistance{B0,Z0,7}, HDistance{B1,Z1,2},
    VDistance{B1,Z1,7} (z is b moved);
  - #8 Parallel{y, z};
  - #9 Coincident{B0, B1}.

What happens:
- Tie(y,b,1), Tie(b,z,1) and Tie(y,z,1) all hold.
- #8 is amber by D-rel, and cross(y,z) = cross(y, z − y) needs no nd.
- If the walk is y–b–z (b being the root or the group's representative),
  then nd = {b}.
- #9 collapses b, and with it y and z.
- The solved system (10 independent linear equations) is regular, but
  |b|² > 0 fails, so the sketch is refused at every level.
- With nd = [] it certifies, and #8 holds there because y = z = 0.

Repeated nodes are a second problem. A tree walk a→root→b repeats the nodes
below the common ancestor, so h gets repeated factors. Since |s|⁴·g ∈ I does
not give |s|²·g ∈ I, nd must be a multiset, or the walk must be simplified
first.

Suggested fix:
- build certificates from simple paths;
- prefer a direct pair fact (tie or frame) to a walk;
- drop from nd every segment the premises already force to be nonzero:
  - a direction component ≡ a nonzero constant mod L;
  - an argument of a kept Angle, whose side dot > 0 forces nonzero length;
- optionally, let the verdict choose among walks at the solution;
- add nd to the "may differ" list in ROADMAP's `honest_unique` comment.

## 6. Angle and Q15 (medium)

**An Angle on a collapsed segment cannot hold.** G.angle needs u ≠ 0, and
the side dot > 0 is 0 there. Example:
- Points: A, B, C, D.
- Segments: a = A→B, b = C→D.
- Constraints: #0 Coincident{A, B}; #1 Angle{a, b, 3/5, 4/5}.

What the plan does:
- D-void drops #1's equation.
- There is no refutation of either kind.
- The side is not implied, so #1 is Kept with every equation dropped.
- The side then fails over every box: refused, with nothing red.

It should be a conflict with support [#0] and nd = []. dot(g·a, b) lies in
the ideal of the collapse (its multipliers are b's coordinates), against a
strict side; that is a degree-1 Positivstellensatz certificate. The rule "a
strict side of c lies in the ideal of a collapse in span(S ∪ c)" is
monotone in S.

**Other Angle points:**
- **"Amber" is overstated.** "A constraint whose equations are all dropped
  is amber, as today" is inaccurate. Amber also needs every side implied,
  and at degree 0 an Angle's dot > 0 is implied only by an equivalent
  Angle. An Angle that closes a cycle is therefore Kept with all its
  equations dropped. B8's Angle cycle should expect that.
- **Misleading nd.** A direction conflict's nd should leave out the
  arguments of any Angle in c or s. Their meaning already requires nonzero
  length, so "unless seg X has length 0" misleads.
- **GUI rounding.** The GUI's `rationalRotation` approximates angles whose
  rotation is not Pythagorean. So an Angle cycle that looks exact, such as
  a triangle's three angles, has a non-real product and comes out red, not
  amber. That is honest for the constants actually sent, but it deserves a
  note in B8 and on the page.

## 7. Smaller points (low)

**Definitions and text**
- Define "constant Angle" as an Angle whose c and s contain no variables.
  QExpr allows variables (sketch.bend: "variables pinned to exact
  constants elsewhere"); the GUI happens to send constants.
- B3/B4 do not describe the D-frame search. It is one proportionality test
  of residuals mod L' for each segment in F's component (or the span test
  from finding 1).
- B2 cites lib/elimpf.bend for "derivable iff residual 0"; that result is
  in lib/indpf.bend.

**Rules and invariants**
- D-frame's walk lives in P's graph, but L' may collapse a segment on it,
  and nd then fails at every solution. In the cases I built, the system is
  singular anyway, but the walk should still use only nodes that are not
  collapsed in L'.
- B2: each residual carries its own positive scale. lib/elim.bend's
  `step.go` leaves r unscaled when its pivot coefficient is 0, and `clr`
  adds a further factor. Frame and collapse tests do not depend on scale.
  A tie does, because it compares the residuals of dir_x and dir_y as one
  complex vector. So divide each residual by its recorded bt (and clearing
  factor) before normalizing.
- If the deletion filter is seeded with "the cycle's own constraints", the
  seed must include the constraints in the combinations behind the cycle's
  frame and tie edges; otherwise the seed may not refute.
- A direction support's irreducibility is relative to P's context (nodes
  collapsed by other premises), not to "the support alone". ConflictOk now
  reads P for more than `none_in`.

**Regression**
- Today sketch(4) has #41 (position 32) red as Over, so it is not a
  "nothing red" case. sk-13b changes two of its positions: #38 becomes
  amber and #41 kept. `expected` changes at both.

**Laws, cost and scope**
- `solve_amber` with the composed nd is true, but weaker than it needs to
  be. Kept constraints hold at x by hypothesis, so only the amber
  derivation's own nd, relative to the premises, is needed.
- Composition is well-founded: each certificate refers only to earlier
  positions; Q is solved when c is Kept and empty when c is Amber. But h's
  degree grows with nesting depth, so measure it on sketches 6 and 7.
- OnLine, the first equation of LineDistance, and Symmetric are also
  vacuous on a collapsed segment, with the same multipliers as D-void.
  They are outside the family, so such sketches stay refused. That is fine
  for this scope, but worth a line.

## Checked and found sound

- **The rules.** Each rule with its stated nd is an identity over every
  commutative ring, and so holds in every ordered field, where |s|² ≠ 0
  iff s ≠ 0:
  - D0, D-rel, D-frame with λ, and D-void;
  - closed walks at a segment (nd includes the start) and at F
    (|F|² = 1);
  - walks through F, backward edges (conj), ties, and walks that repeat
    nodes (given a multiset h).
- **The global theorem.** The premises' graph at the next constraint is
  exactly the refutation graph of the last kept c with S = P: same nodes,
  same constraint edges, same facts. So it has no conflicting closed walk.
  Later collapses only remove nodes, which only deletes walks, so
  non-monotonicity does no harm. It follows that all walks between two
  nodes have alike products, so union–find decides D-rel exactly. Among
  nodes that are not collapsed, a tie or frame inconsistency would force a
  collapse, so the linear facts never conflict with each other.
- **Monotonicity.** With the nodes fixed by the context, constraint edges,
  frames and ties only grow with S. A node that is not collapsed has at
  most one frame label, and at most one tie label per partner. So the
  deletion filter's result is irreducible, and an irreducible support
  exists whenever P refutes.
- **`honest_unique`.** Every new definition is a function of:
  - P (the red constraints before c);
  - the basis (red constraints and drops before c);
  - own_rest (c's own drops, decided in order).

  Conflict needs s ⊆ P, so a refutation with s gives one with P, which
  excludes the other cases. When P does not refute, the drops, then Over
  or Matchable, then Amber or Kept, are forced as in sk-13a.
- **Unchanged answers.**
  - D0 over the premises equals sk-13a's D0 whenever every earlier drop
    has h = 1, because span(P) is then span(presolved).
  - D-frame never fires without direction constraints, since frame and tie
    chains are linear facts already.
  - So linear-only sketches keep their answers, and `base` and
    `angle-lines` have no direction cycle.
- **Composition.** Every certificate bottoms out in solved equations:
  - edges and facts come from P, at earlier positions;
  - Q is solved when c is Kept and empty when c is Amber;
  - Over carries no certificates, and conflicts need none.
- **The unchanged laws.** `solve_unique`, `solve_pins`, `solve_regular`,
  `solve_total`, `fast_solve` and `honest_unique` keep their statements
  and still hold. `solve_exists` and `solve_blame` hold once finding 3 is
  fixed.
