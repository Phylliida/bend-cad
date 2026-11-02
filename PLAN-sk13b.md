# Plan: sk-13b, the direction layer (v2, 2026-10-26; decisions agreed)

This is PLAN-sk13.md's Phase 2 (DESIGN §8.11, "Directions"), worked out
against sk-13a as built. It has two halves: the trusted part (what the
answer means: the calculus, `Honest`, the classes, the laws), and the
order of work. Danielle asked for it on 2026-10-26 after slowsketches 8
and 9 ("the correct, proper way").

v2 follows the audit of v1 (AUDIT-sk13b-plan.md: no blocker, seven
findings). The main change is finding 1. v1 related directions only in
pairs, so a chord of a split line was missed. v2 closes the direction and
linear layers under each other, and OnLine joins the family. The
statement fixes (findings 2, 3, 5, 6, 7) are folded in. Finding 4 is
decision 4.

## Why

Today's layer sees only constant combinations (degree 0). Dependencies
among directions need polynomial multipliers, so the solver keeps every
such constraint. The block is then singular at every solution, Newton
fails at all seven precisions, and the page says "Not certified" with
nothing red.
- sketch(4) (vertical-twice): seg 28 is made vertical twice, through #25
  ⊥, #27 ∥ and #38 ∥. Refused.
- slowsketches 8 and 9: #66 makes seg93 ∥ seg95 and #67 makes them ⊥.
  Refused after 54 s and 132 s. Dropping either one certifies in a few
  seconds.

## What sk-13b delivers

**The solver**, in the same single pass, also reasons about directions:
- **Implied**: an equation that the directions imply is dropped, with a
  certificate. A constraint is amber when all its equations are dropped
  and its side conditions are implied, as today. An Angle that closes a
  cycle is kept with its equation dropped: its side (dot > 0) is not a
  degree-0 consequence.
- **Conflict**: a constraint whose directions cannot hold together with
  earlier ones is red, with an irreducible support, as today.
- **Nondegeneracy is explicit.** Collapsed segments satisfy every
  direction relation (Q15), so each direction judgment names the segments
  it needs to have nonzero length (nd). The verdict proves those lengths
  nonzero over the certified box with ball arithmetic, like side
  conditions (§8.6).

**For your sketches:**
- slowsketches 8 and 9: #67 is red, "conflicts with #66, unless seg93 or
  seg95 has length 0", and the rest certifies in about the time it takes
  without #67.
- sketch(4): #38 is amber, and the sketch certifies. Today's Over at #41
  goes away too, so `expected` changes at two positions.
- A chain of parallels or OnLines closed again, a fourth right angle, a
  chord of a split line, or a Horizontal across a split edge comes out
  amber. A Vertical there, or a VDistance 3 on a segment parallel to a
  horizontal one, is red.

**What is proven** (the same shape as sk-13a):
- the answer is honest for the extended calculus, and the layer is
  complete for it;
- honest classifications are still unique (`honest_unique`, same
  statement);
- the semantic laws hold with the nondegeneracy stated;
- the existing laws still hold over the solved system.

## Decisions for Danielle

Danielle agreed to all four as recommended (2026-10-26).

1. **Direction judgments carry nondegeneracy.**
   - #67 in sketches 8 and 9 holds together with #66 when seg93 or seg95
     has length 0. Today's `solve_conflict` says a conflict "cannot hold";
     here it can.
   - DESIGN §8.11 already says direction conflicts hold "at a
     nondegenerate configuration", and SK13A-REVIEW says "nondegeneracy
     enters as explicit geometric hypotheses from a fixed vocabulary".
   - The vocabulary is one notion: *segment s has nonzero length* (its
     endpoints differ). The solver never picks a polynomial.
   - A conflict becomes: c and its support cannot all hold at any geometry
     where its nd segments have nonzero length. An implied equation holds
     wherever the solved ones hold and its nd segments have nonzero
     length.
   - Recommended: yes.
2. **The family: direction statements over the linear layer, closed under
   each other.**
   - A *direction statement* says one vector is parallel to a segment.
     Parallel, Perpendicular, an Angle with constant rotation, and OnLine
     (the point's offset from the line's start) are such statements.
   - The linear layer is what degree 0 knows.
   - Each feeds the other. A segment that the directions make horizontal
     gives the linear layer its y-difference. Sums of parallel vectors are
     parallel, and shared points make directions add.
   - Not in it: Symmetric, LineDistance, lengths (sk-13c), and Angle
     orientation (a sign question: sk-13s's layers, as in sketch(5)).
   - Recommended: as stated. v1's pairwise family missed natural
     dependencies (the audit's sketches A and B), and it had no OnLine.
     Your sketches use OnLine a lot: 9 to 13 times each.
3. **The layer reads all the kept constraints' equations, amber ones
   included, not only the system solved.**
   - Reading only the solved system breaks the calculus. A segment that
     the kept constraints force to length 0 can still look nonzero to the
     solved system (some equation that collapses it was dropped). A false
     cycle then stays in the graph, and every later constraint would be
     red.
   - Reading the premises keeps the closure consistent by construction:
     each kept constraint was checked against exactly what the next one
     reads.
   - The cost: certificates compose. A fact from a dropped equation brings
     that equation's certificate and nd along. Degree-0 drops still read
     the system solved, as in sk-13a.
   - Recommended: as stated.
4. **Later collapses (the audit's finding 4).**
   - A constraint is judged from the ones before it. If a later
     constraint collapses a segment that an earlier direction constraint
     uses, that earlier equation becomes vacuous (it holds trivially), so
     the system solved is singular.
   - Example: Parallel{a, b}, then a Coincident merging b's endpoints.
     This is refused today, in sk-13a, with nothing red. It is refused in
     sk-13b too.
   - In the other order, the Parallel is amber (vacuous) and the sketch
     certifies. A later collapse of an interior segment of an earlier drop
     is the same case.
   - The principled fix is to judge the linear constraints first (DESIGN
     §8.11's "Linear, then directions" order, and the planned linear
     presolve). Collapses are then known before any direction is judged.
   - That changes Q21 ("the last one is flagged") for mixed dependencies:
     in "∥ to a horizontal segment, then Vertical", the Parallel would be
     red, not the Vertical you just added.
   - Recommended: keep sketch order in sk-13b, and take this up with the
     linear presolve. The calculus is the same in either order; only the
     order of judging changes.

## The trusted part

### Vocabulary

- For a segment s from p to q, its direction z_s is the complex linear
  form (x_q − x_p) + i(y_q − y_p). The frame node F has z_F = 1, the
  direction of the x axis.
- For complex linear forms x and y, cross(x, y) = Im(conj(x)·y) and
  dot(x, y) = Re(conj(x)·y), polynomials in the variables.
- A label g is a constant Gaussian rational c + is, g ≠ 0.
- A *direction statement* is an equation of the form cross(z_a, x) for a
  segment a and a complex linear form x, up to a constant factor. By
  constraint kind:

  | kind | x |
  |---|---|
  | Parallel{a, b} | z_b |
  | Perpendicular{a, b} | i·z_b (dot(z_a, z_b) = cross(z_a, i·z_b)) |
  | Angle{a, ra, b, rb, c, s}, c and s with no variables | conj(c + is)·z_b, signs from ra, rb |
  | OnLine{p, a} | p − (a's start) |

  An Angle whose c or s mentions a variable is not one.
- Nondegeneracy: `Long(x, s)`, |z_s|^2 > 0 at x (in an ordered field the
  same as s's endpoints differing; B1 notes why this form). nd is a list of segments, and a segment may repeat (the
  verdict's h is the product over the list). The semantics read it as a
  set.

### The calculus

Fixed for a constraint c by its **premises** P: the equations of the kept
(not red) driving constraints before c, every one (dropped ones too).
When c's i-th equation is judged, the facts also read Q_i, c's own
earlier equations that were not dropped. Every fact carries an nd. A
premise equation's nd is empty if it is solved, and its drop's nd if it
was dropped.

The **context** of c is the rational span of the equations of P and all
of c, taken as polynomials. A segment is *collapsed* when both parts of
its direction lie in the context. Collapsed segments are never passed
through, in refutations and derivations alike.
- The context only decides which segments may be passed through. It is
  never used as a fact, so reading c's own equations there is not
  circular.
- One context for both keeps the derivation closure (P ∪ Q_i) inside the
  refutation closure (P ∪ eqs(c)), which `NoRefute` has checked. So the
  closure a drop reads is consistent too.

**Two judgments**, defined together as the least set closed under the
rules:
- **K(e, nd)**: e vanishes. The linear layer, extended.
- **∥(a, x, nd)**: the complex linear form x is parallel to node a's
  direction, i.e. cross(z_a, x) vanishes.

**Rules** (nd is the union of the premises' nd, plus what is named):

| rule | from | gives | nd added |
|---|---|---|---|
| K-premise | e is an equation of P | K(e) | e's own |
| K-zero | | K(0) | |
| K-add | K(e₁), K(e₂), a rational λ | K(λ·e₁ + e₂) | |
| ∥-premise | a direction statement cross(z_a, x) in P | ∥(a, x) | its own |
| ∥-self | | ∥(a, z_a) | |
| ∥-lin | ∥(a, x₁), ∥(a, x₂), rationals μ₁, μ₂ | ∥(a, μ₁x₁ + μ₂x₂) | |
| ∥-known | ∥(a, x), K(Re ℓ), K(Im ℓ) | ∥(a, x + ℓ) | |
| ∥-turn | ∥(a, conj(g)·z_b), b any node | ∥(b, g·z_a) | |
| ∥-through | ∥(a, conj(g)·z_b), ∥(b, x), b a node not collapsed | ∥(a, conj(g)·x) | b, if a segment |
| frame | K(Im x) | ∥(F, x) | |
| frame-back | ∥(F, x) | K(Im x) | |
| complex line | ∥(a, x), ∥(a, i·x) | K(Re x), K(Im x) | a, if a segment |
| ∥-void | K(Re z_a), K(Im z_a) | ∥(a, x), any x | |

Each rule is an identity with polynomial multipliers, proven once:
- **∥-through** is the path lemma:
  |b|²·cross(g₁g₂·a, c) = dot(g₁·a, b)·cross(g₂·b, c) + cross(g₁·a, b)·dot(g₂·b, c).
- **complex line**: cross(z_a, x) and cross(z_a, i·x) vanish, so
  conj(z_a)·x does, and |z_a|²·x = z_a·(conj(z_a)·x).
- **∥-known**: cross(z_a, ℓ) = a_x·Im ℓ − a_y·Re ℓ.
- **∥-void**: cross(z_a, x) = Re(z_a)·Im x − Im(z_a)·Re x, a combination
  of a's two direction parts with polynomial multipliers. A collapsed
  segment is parallel to everything (Q15).
- **∥-turn**: cross(z_a, conj(g)·z_b) = −cross(z_b, g·z_a).
- **frame**: cross(1, x) = Im x.

Every rule's identity was checked with sympy on 2026-10-26, in complex
form: the path lemma (∥-through), complex line, ∥-known, ∥-void, ∥-turn,
frame, and the Perpendicular and Angle forms in the table above. The
audit rechecked the path lemma independently.

**Why this family is natural.** Linear facts imply a single direction
relation in only four ways. cross(g·a, b), as a quadratic form in (a, b),
has signature (2, 2), and its 2-dimensional totally isotropic subspaces
are: a = 0; b = 0; b = λ·g·a for a fixed real λ; and a ∈ ℝu with
b ∈ ℝ·g·u. The rules reach each of these: a collapse; a tie (∥-premise
or ∥-known with ∥-self); two frames. With ∥-lin, sums of parallel
vectors are parallel, so the audit's chord sketch is in. With frame-back
and complex line, direction knowledge returns to the linear layer, so
its split-edge and VDistance sketches are in.

**Derivations** (for c's i-th equation e, over P ∪ Q_i):
- K(e) holds. This includes sk-13a's degree-0 drops, with nd empty.
- Or e is a direction statement cross(z_a, x), and ∥(a, x) holds. This
  includes a statement on a segment whose collapse is known (∥-void).

**Refutations** (for c with a set S of kept constraints before it), in
the closure of S and c. The context, and so which segments are
collapsed, is still that of P and c.
- A degree-0 (Motzkin) refutation of the K facts with the side
  conditions. A nonzero constant in K is the simplest case. The nd is
  that of the facts used.
- A *derived collapse*: both parts of z_s are in K for a segment s that
  is not collapsed in the context. The nd is that of the facts, plus s.
- An Angle in S or c on a segment whose collapse is a K fact: its side
  dot > 0 is then a combination of the collapse's facts with polynomial
  multipliers, so it is 0. This is a degree-1 Positivstellensatz
  refutation, and its nd is the collapse's.

Refutability is monotone in S: more constraints give more facts, and the
segments that may be passed through stay fixed by the context. So
Chinneck's deletion filter gives an irreducible support, and one exists
whenever P refutes. A conflict's nd may leave out the arguments of any
Angle in c or s, since the Angle's meaning already makes them nonzero.

**Global theorem**: the premises' closure never refutes. By induction:
each kept constraint had no refutation in exactly the closure the next
constraint reads. So among segments that are not collapsed, labels are
consistent, every hull is a real span with no complex line in it, and the
decision below is exact.

### `Honest`, extended (spec/solve.bend)

The cases stay exclusive, in the same order:
- **Conflict iff refutable**: a degree-0 refutation *or* one above, of c
  with its premises.
  - `ConflictOk{s, nd}` asks for a refutation of c with s *whose nd is
    within the class's nd*. Without that, the restated `solve_conflict`
    would be false (the audit's finding 2).
  - Irreducibility: without any one member of s, no refutation of either
    kind, whatever its nd.
- **Drops**: each equation of c is dropped iff it has a derivation above.
  The recorded nd must cover the nd of some derivation of it.
- **Over, Kept, Amber**: unchanged. They read the drops, and `NoRefute`
  now excludes both kinds of refutation.

`honest_unique` keeps its statement. Every new definition is a function
of the premises, the classes before c (for nd) and c's own earlier drops,
so the induction goes through. nd joins the list of what may differ
between two honest solvers, with the Over witnesses, the supports, the
pins and the box.

### The answer's shape

- `Drop{j, nd, qs}`: equation j, its nd, and multipliers on equations of
  the system solved, with Π_{s∈nd} |s|²·g_j ≡ Σ q_k·g_{i_k} as
  polynomials. sk-13a's drops have nd = [] and h = 1, as now.
- `Conflict{s, nd}`.
- **The verdict** checks:
  - each identity, with the ring normalizer (as now, with h built from
    nd);
  - |s|² > 0 over the box, with ball arithmetic, for every s in the nd of
    a drop of any constraint that is not red, Kept or Amber (finding 3).

### The laws

A = `SO.solve_l(sk, g0, l)`, as in SK13A-REVIEW.md.
- **Unchanged statements**: `solve_exists`, `solve_unique`, `solve_pins`,
  `solve_regular`, `solve_blame`, `solve_honest` (its `Honest` extended),
  `honest_unique`, `solve_total` and `fast_solve`. The certified geometry
  still satisfies every constraint that is not red, because the verdict
  checks the nd over the box.
- **`solve_drop`**: wherever the solved equations hold *and that drop's
  nd segments have nonzero length*, the dropped equation holds.
- **`solve_amber`**: deleting every amber constraint changes no solution
  *at which the amber constraints' own derivations' nd hold*. Kept
  constraints hold at x by hypothesis, so only the amber derivation's own
  nd relative to the premises is needed (the audit: the stronger form).
- **`solve_conflict`**: a conflicting constraint and its support cannot
  all hold *at any geometry where its nd segments have nonzero length*.
- **`solve_complete`**: also needs |s|² > 0 at the regular solution x*,
  for every s in the nd of a drop of a Kept or Amber constraint (a
  `Strict` side, like the others).
- **`solve_refused`**: if no level certifies, the drawing is not a
  regular solution of the system solved, or some such nd segment has
  length 0 there.

### What nd is chosen

nd affects only whether the verdict passes, never soundness. But two
honest solvers with different nd can disagree about certifying, so the
solver keeps nd small:
- certificates come from simple paths;
- a direct fact is preferred to a walk;
- a segment the premises already force to be nonzero is left out: a
  direction component that is a nonzero constant modulo the context, or
  an argument of a kept Angle in a conflict.

The audit's example of a choice of walk that refuses is avoided this way.
There, a tie through a representative added a segment the identity does
not need.

## Steps

### B0. Statements
*Done 2026-10-26.* As built:
- **Staging, like sk-13a's S0b but without opening proven laws.**
  - spec/dir.bend is in place. It is new and trusted, and only the draft
    imports it.
  - The extended solve spec is spec/_draft13b.bend. It replaces
    spec/solve.bend at the switch (B4), when the pass decides the layer.
    Replacing it now would make `solve_honest` false for today's pass
    (#67 kept), and would turn several proven laws open for many sessions.
  - tests/dir_draft.bend keeps both checking in the gate: their functions
    on sketch 8's shape by `{==}`, and the restated laws' content over any
    honest classification, as statements only.
  - tools/drafts/roadmap13b.draft holds the five solver-level texts. They
    are installed, and checked by `tools/stmtcheck.py`, at B4.
- **Choices made while writing.**
  - `solve_drop` is restated per drop (equation j with its own nd), not
    for all drops at once.
  - Drops read facts with their drops' nd (inherited). Refutations read
    facts with nd none: where the refuted constraints hold, so do their
    equations.
  - `Drop` keeps its `Comb`. The verdict (B5) will require h ≡ ndh(nd).
  - A conflict's nd may leave out the segments of Angles among the
    constraints refuted (`angle_args`).
  - `RAngle` names a constraint position.
  - dir.bend's `Same` and `dlin` repeat solve's `Ident` and `lin`, to
    keep dir.bend free of spec/solve.bend (which will import it). To be
    unified at the switch.
- **Checks.**
  - Both files type-check.
  - Five planted errors were rejected: a wrong nd, a short refutation nd,
    a constant Angle read as none, a law's missing argument, and an amber
    nd left out of `live_nd`.
- The plan as written:
- spec/dir.bend (new, trusted): directions as complex linear forms,
  labels, direction statements by kind, the two judgments as an
  inductive derivation type, `Long`, the context and collapse.
- spec/solve.bend: `Drop` and `Conflict` with nd, derivations and
  refutations, `Honest` extended (`ConflictOk` binds nd).
- ROADMAP.bend: the five laws restated, with "Kept or Amber" wherever nd
  is checked; `tools/stmtcheck.py` type-checks them.
- DESIGN §8.11: the family, its completeness claim restated for this
  calculus, decision 4's limit, and nd's place among what may differ.
- No further statement audit unless you want one. v1's audit checked the
  approach; proving checks the rest.

### B1. The rules, proven once
*Done 2026-10-27* (lib/dirpf.bend, from tools/drafts/dirpf.draft; the
gate checks it through tests/dir_draft.bend). As built:
- **`sound`**: in every ordered field, wherever a derivation's facts hold
  (each where its own nd is long) and its nd segments are long, its
  conclusion holds: K(e) evaluates to 0, par(a, x) makes cross(z_a, x) 0.
  It is one lemma per rule, each a certificate whose identity the
  normalizer checks (the path lemma included), with |z|^2 cancelled where
  a rule names a segment.
- **`dstat_ok`**: every constraint kind's direction statement is right.
  Parallel and OnLine are their equations; Perpendicular is dot = cross
  with i z_b; an Angle with constant rotation, taken forwards or reversed,
  differs from its statement by its sign and (t + s) dot(a, w) (the sine's
  conjugate t = -s).
- **One spec change, forced by Bend and harmless:** `Long` is "|z_s|^2 > 0",
  not "the endpoints differ". Bend is affine for every type: a hypothesis
  that is a function (ne is "equal implies Empty") cannot be used twice,
  and the proof uses nd at several places. In an ordered field the two
  are the same, and |z_s|^2 > 0 is exactly the side condition the
  verdict checks over the box. Facts' truth is Data the same way: some nd
  segment has squared length 0, or the fact holds.
- **Checks**: planted errors rejected (a sign in the path lemma's
  certificate; labels swapped in K-lin; the spec's nd for through without
  the segment passed through; Perpendicular given Parallel's statement; a
  normalizer identity in a helper, caught through the gate's root).
- **Moved to B4:** the certificate half (a derivation's polynomial
  identity over solved equations, for the verdict). The pass builds the
  certificates there, so their identities are proven with it.
- The plan as written:
- Each rule's identity as `Ident`, by the ring normalizer on atoms.
- A derivation gives a certificate: Π_{nd}|s|²·e ≡ Σ q·g over P's
  equations, by induction on the derivation. Composed with dropped
  premises' certificates, it lands on solved equations only. That is
  well founded, since every fact refers to earlier positions.
- Semantics: wherever the solved equations hold and nd is nonzero, a
  derived e vanishes, in every ordered field.

**Turn and through take any node (2026-10-27).** B1 first had b a
segment. With b allowed to be the frame (z_F = 1), a constant parallel to
a segment fixes its direction: OnLine with fixed points gives ∥(a, κ),
and turning at the frame gives ∥(F, conj(κ)·z_a). The rule set is the
same; the soundness lemmas already took any vectors.

### The decision procedure (B2–B4), as designed 2026-10-27

**State**, for the facts of P (and c's earlier equations):
- **K**: generator polynomials, each with nd and a derivation (the
  premise equations first, then derived affine forms), in sk-13a's
  echelon form (lib/elim.bend). Membership is a zero residual
  (lib/indpf.bend's result for the independence half).
- **Components** of the open nodes (F and the segments the context does
  not collapse), by a union–find with labels. A member v has a label g_v
  with ∥(r, conj(g_v)·z_v) for the root r, and a derivation of it.
- **Hulls**, one per component without F, in the root's frame: real
  spans of complex forms modulo K², each generator with nd and a
  derivation. A form x = x_re + i·x_im is encoded as the one polynomial
  x_re + t·x_im (t a fresh variable), so that hull membership modulo K² is
  membership in the span of the encoded generators, K and t·K: the same
  elimination again. F's component needs no hull: ∥(F, x) iff Im x ∈ K.
- **Collapsed segments** (in the context): each has its own hull. They
  are never passed through, but their statements turn into the open
  hulls, and through-steps land on them.

**Fixpoint**, each step one of:
- a premise statement ∥(a, x) joins a's hull (rotated into the root's
  frame by a's label);
- a node b joins a component when conj(g)·z_b lies in its hull for some
  g ≠ 0: a dependence among the hull, z_b and i·z_b, read off the
  residual's combination. With b = F this is a constant in the hull;
- a component that reaches F gives K the imaginary parts of its hull
  (frame-back);
- a complex line in a hull (the hull, then i times it, become dependent)
  gives K both parts of it;
- K's new rows reduce the hulls again.

It ends: each step grows K's rank or a hull's rank, or merges two
components, and all are bounded.

**Proof obligations:**
- **Sound**: every state element carries a valid derivation (Der) with
  its nd, checked against spec/dir.bend's Valid.
- **Complete**: the final state is closed under every rule, so by
  induction on a derivation its conclusion lies in the state. The fixpoint
  tests that passed at the end are what closure means, rule by rule: K a
  span, hulls spans with K² inside, members' labels consistent, no
  complex line left, F's component's imaginary parts in K.
- **Decisions**: c's equation is dropped iff it is in K, or its statement
  lies in its segment's hull. c is refuted iff the state of P and c
  refutes: a Motzkin refutation of K's generators with the sides (sk-13a's
  simplex, lib/refute.bend), a derived collapse, or an Angle on a
  segment collapsed in K.

### B2. The linear layer, extended (K)
*Core done 2026-10-27* (lib/kspace.bend, lib/kspacepf.bend). As built:
- K holds sk-13a's rows and one derivation per generator. The generators
  are read off the derivations' conclusions, so the two cannot drift.
  Adding a generator keeps it only if its residual is not 0.
- Proven: the invariant (sk-13a's echelon form of the generators, every
  derivation valid and proving a K judgment) is kept by adding
  (sk-13a's new_rinv). A zero residual gives a valid derivation proving e:
  a chain of K-add steps whose conclusion is exactly lin of the
  generators, which sk-13a's derivable shows is e. A nonzero residual
  shows no constant combination of the generators is e (sk-13a's indep).
- Two spec changes made it clean: K(0) (DZero), and K-add (λ·e₁ + e₂) in
  place of K-lin, so chains have spec/solve.bend's lin shape.
- The segments' residuals are not kept apart: with the hull encoding
  (above), each hull test reduces its forms afresh, so there is nothing
  to keep up to date.
- The plan as written:
- Rows for P's equations (the basis's rows, plus the dropped ones' until
  the first direction drop changes the span), and rows for derived
  linear forms, each with its nd.
- Residuals of every segment's direction parts, kept up to date as rows
  are added. Each residual is divided by its recorded scale before
  complex comparisons (the audit: the scales of x and y parts differ).
- Proven: K(e) holds iff e's residual is 0 (lib/indpf.bend's result,
  extended to the derived rows).

### B3. Components and hulls (∥)
*Started 2026-10-27.* Done: lib/seppf.bend, the way back from the tag
encoding: if a + t·b and c + t·d are the same polynomial and none of them
mentions t, then a = c and b = d (at each rational point, t set to 0 and
to 1). It lets a hull membership found by one elimination of encoded forms
give both component identities that Valid's SameV asks for.
- Bend note: an `Ident` is a function, so it cannot be used twice; its
  reusable form is the normalizer's `{qzero(e1 - e2) == True}`
  (lib/identpf.bend: qzero_ident, ident_ok).
- **Hull spaces, as designed:** a hull of root r is a list of derivations
  of ∥(r, g_j). K's generators enter it as the forms (k, 0) and (0, k),
  each derived by ∥-known from K(k), so the basis is uniform. One
  elimination runs over the encoded forms g_j,re + t·g_j,im. A zero
  residual gives multipliers ls, and the witness is the ∥-lin chain over
  the generators. Its conclusion is the real combination clin(ls, g), and
  lin over the encoded generators equals the encoding of clin (one
  induction, pointwise rational identities). The separation lemma then
  gives SameV(y, clin) as Valid asks. A nonzero residual means no
  combination (sk-13a's indep). t is a variable index past every
  expression's variables (the sketch's coverage, `within`).
- *Hull spaces done 2026-10-27* (lib/hspace.bend, lib/hspacepf.bend): the
  invariant kept by adding, membership with its valid chain proving
  SameV(y, ·) (pchain_x, enc_lin, the separation lemma), and
  non-membership (indep). K's generators enter as (k, 0) and (0, k) by
  `kre`/`kim` (par-known on 0·z_r + 0·z_r).
- **The rest of B3, as designed 2026-10-27:**
  - **Nodes in three kinds.** *Frame-tied* (a's direction is fixed:
    Im(conj(u_a)·z_a) ∈ K, with a derivation). Its hull is implicit,
    ∥(a, y) iff Im(conj(u_a)·y) ∈ K, so through-steps at F stay finite.
    *Free* (an explicit hull). *Collapsed* in the context (an explicit
    hull, never passed through).
  - **Events of the fixpoint.**
    - A free hull containing a constant κ makes the node frame-tied (turn
      at F).
    - conj(g)·z_b in a's hull, b open: through adds conj(g)·(b's
      generators) to a's hull, and turn adds g·z_a to b's.
    - A free hull touching a frame-tied b makes a frame-tied.
    - A complex line in a hull gives K both its parts.
    - K's new rows rebuild the hulls.
  - **Termination, proven by counting** (Bend needs a visible measure).
    Echelon rows have distinct pivots, and every pivot is a monomial of
    something inserted. Those monomials come from a finite set the sketch
    determines: a rotation conj(g)·x has x's monomials, and Re/Im take a
    form's. So there are two nested loops with fuel. The outer one runs
    once per K row (at most |M_K| + 1 times). The inner one, at fixed K,
    runs the merges, frame-ties and hull rows (at most nodes + Σ|M_H| + 1).
    Sufficiency is pigeonhole on pivots (lib/pigeon.bend's style, as
    sk-13a's simplex).
  - **Closure, rule by rule**, for the final state:
    - spans are closed (coefficient lists combine);
    - frame-tied hulls are closed by their definition;
    - through and turn between free nodes hold by the fixpoint's last
      round. Another label g' alike to g gives the same span, since a
      hull with no complex line meets ℂ·z_b in a real line;
    - a refutation is found iff one exists (Motzkin over K's
      generators, a derived collapse, an Angle on a K-collapsed
      segment).
- *Spans done 2026-10-27* (lib/spanpf.bend): InSpan as reusable Data,
  decided exactly both ways by the elimination, grown by appending, and
  closed under l·e₁ + e₂ and 0. These are the closure proof's linear
  algebra for K. The hull analogues follow the same pattern over the
  encoded forms.
- *Pair test done 2026-10-27* (lib/pair.bend, lib/pairpf.bend): find
  (a, b), not both 0, with a·u + b·v in a span. Proven sound, and
  complete for b ≠ 0 and for b = 0 with a ≠ 0. The hull label test is
  u, v = enc(z_b), enc(i·z_b), and the frame test against K is
  u, v = Im z, −Re z.
- *Speed:* rational identities are chains of lib/qalg.bend's small lemmas.
  A six-atom normalizer call cost about 130 s; the gate is back to about
  a minute.
- **Closure, as designed 2026-10-27 (supersedes the node kinds above).**
  The four-kinds note had two gaps. A collapsed node tied to a constant u
  can hold more than {y : cross(u, y) ∈ K}: nothing passes through it, so
  its extra facts never reach K. And two independent ties make a node
  hold every form without being void. The design:
  - *Explosion.* If 1 ∈ K, or an open node's direction is in K², every
    judgment is derivable: ∥(F, (0, e)) by ∥-void or ∥-through, then
    K(e) by frame-back. The closure stops there, with that witness. The
    refutations that do not explode (Motzkin with sides, an Angle on a
    K-collapsed segment) do not change derivability, and are detected on
    the fixpoint.
  - *Open nodes* (F and the segments not collapsed in the context) form
    a union–find forest with F always a root. Each open a has a root r
    and a label ℓ_a ≠ 0, with a derivation of ∥(r, ℓ_a z_a). Its set is
    P_a = {y : ℓ_a y ∈ P_r}: F's is implicit, {y : Im y ∈ K}, and any
    other root's is the span of its generators. Two open nodes with a
    link are rotations of each other (w P_b ⊆ P_a and conj(w) P_a ⊆
    P_b), which is why components suffice.
  - *Collapsed nodes* c have three kinds: *Free* (span of generators),
    *Tied* to u (span plus u·Q[x], so membership is cross(u, y) ∈
    span(cross(u, g_j))), and *Full* (z_c ∈ K²; two independent ties
    force it). They are linked to other nodes by stored derivations of
    ∥(c, w z_b), at most two independent w per pair.
  - *The skeleton:* K's generators, the forest, the links, the ties and
    the Full flags. Every round rebuilds the hulls from the skeleton (the
    stored derivations stay valid), runs the checks below, and adds one
    skeleton item for the first failure. Its measure (K's rows, merges,
    links, ties, Full flags) is bounded: K's rows by pivots in the
    monomials of the facts and the sketch's base forms (lib/coefpf.bend's
    coefficients are linear, and lib/elim's rows have distinct pivots),
    the rest by the number of nodes. So the hull dimensions never need
    counting.
  - *Generators,* with derivations:
    - an open root r: ℓ_a z_a, ℓ_a x for each statement ∥(a, x), and
      ℓ_a conj(w) z_c for each link ∥(c, w z_a), over r's members a
      (through at a), plus K²;
    - a collapsed c: z_c, its statements, w·conj(ℓ_b)·g for each link
      ∥(c, w z_b) to an open b with root r and g among r's generators
      (through at b; a link into F's component is a tie instead, and F
      gets its turned form), and conj(w) z_c' for each link ∥(c', w z_c),
      plus K².
  - *Checks* (all passing means closed):
    - no open root's set holds a nonzero rotation of an open node
      outside its component (the pair test; a failure merges);
    - F's generators have their imaginary parts in K (frame-back);
    - no Free open root has a complex line outside K² (inserting i·g_j
      for its non-K generators leaves every residual nonzero; failure:
      complex line);
    - every node with z ∈ K² is Full (open means explosion);
    - for collapsed c and every node b, the links span G_cb = {w : w z_b
      ∈ P_c} (the pair test, then one membership for i·w₁);
    - for an open root r and collapsed c, conj(G_rc) is in G_cr (turn
      from r).
  - *Closure,* rule by rule over the represented sets. Inside a
    component, a second label for b would give P_r a complex line through
    z_b, hence z_b ∈ K² (explosion), so labels are unique up to Q.
  - *Audited 2026-10-27* (AUDIT-sk13b-closure.md): no wrong rule or case
    pair. Six refinements, adopted:
    - Full is z_c ∈ K² only. Two ties force it: each tie turns at F, and
      frame-back puts cross(u, z_c) in K. So ties are links on F's side,
      and F's generators include their turned forms.
    - A link ∥(c, w z_b) to an open member b gives c the generators
      w·conj(ℓ_b)·g over the root's generators g (through at b), so no
      chain of checks is needed.
    - Rebuilt sets are not monotone. The link check computes a fresh
      basis of G_cb (the pair test, then i·w₁) and compares it with the
      stored span.
    - The complex-line check inserts i·b_j over the hull's kept non-K
      rows, with K²'s generators first (lib/indset.bend).
    - Nodes outside the sketch have direction 0 (collapsed, void). The
      checks range over F and the sketch's segments, and a lemma covers
      the rest.
    - A Tied set's generators include K²'s, so its membership includes
      K.
- *Labels done 2026-10-27* (lib/lab.bend, lib/labpf.bend): products of
  labels, the rotation-composition identity g(h x) = (g h) x, and the
  hull label test, proven sound (a found w has w z in the hull) and
  complete (if some nonzero w does, it finds one).
- *Frame test and independence of a set done 2026-10-27*: ks.lab
  (Im(w z) ∈ K), sound and complete like the hull's (lib/labpf.bend); and
  lib/indset.bend, lib/indsetpf.bend: forms inserted in turn, each with a
  nonzero residual, combine into the span only with every coefficient 0.
- *The closure's exec code done 2026-10-27* (lib/dclose.bend, unproven
  yet): the skeleton, generators, the three kinds of collapsed sets, the
  checks in order (explosion, frame-back, complex line, merges, links),
  the round and a fuel loop. proto/dclose_run.bend runs it natively on
  eleven small sketches: parallel/perpendicular conflicts explode,
  parallel chains merge, horizontal segments join F, and segments
  collapsed in the context are linked and tied as designed. All eleven
  take 74 ms.
- *Soundness proofs in progress 2026-10-27:*
  - lib/dcopenpf.bend: isopen true gives Open.
  - lib/dcvd.bend: VD, a Data mirror of Valid (identities in the
    normalizer's form, Open as the closure's test), giving Valid. It is
    needed because Bend uses a Type-valued proof once, and the closure
    shares one derivation among many generators.
  - lib/dcinvpf.bend: KInvD and HInvD (VD and below t per generator),
    kept by adding and folding, giving KInv and HInv.
  - lib/dcbelowpf.bend: forms below t (directions under DC.zb,
    rotations, i, K squared).
  - lib/dcgenpf.bend: the member and link invariants (MOkD, LOkD), the
    label identities as Data, and every root generator valid at its
    root, so rebuilt root hulls keep HInvD.
  - lib/dcderpf.bend: ks.der and hs.der in VD form, with conclusions the
    same as asked.
  - lib/dcmergepf.bend: merges keep MOkD (a merge's derivation is itself
    a member record of the old root under the new).
  - lib/dcclxpf.bend: frame-back and complex-line K facts are KGens (the
    elimination's multipliers split over the hull's generators and the
    inserted ones; i and the encoding are linear).
  - lib/labnzpf.bend: labels are nonzero (|gh|² = |g|²|h|², the pair
    test's (1, 0) and (−c, 1)). A tied set divides by |u|², and an open
    member's query scales by 1/|w|². This is kept as a separate list
    invariant beside MOkD and LOkD.
  - All gated through tests/dir_draft.bend; the gate is still about a
    minute.
  - lib/dcreppf.bend: collapsed sets keep RepOk (generators valid at c;
    Free hull; Tied span with its tie valid, the same as u (1, 0), u
    nonzero; Full).
  - lib/dctiedpf.bend: the tied derivation proves y (y = combination +
    (dot(u, rest)/|u|²) u, from cross(u, rest) = 0).
  - lib/dclinkpf.bend: collapsed sets' derivations per kind, their basis
    labels (members and nonzero), the tied label test, and both kinds of
    new link.
  - lib/dcroundpf.bend: nonzero labels kept by merges, each round
    stage, the initial state, and the run. **dclose_ok: whatever the
    closure returns keeps the invariant**: a state (K, members and links
    valid, labels nonzero), or an explosion with its witnesses (a K
    derivation of 1, or an open segment with both parts of its direction
    derived in K). Soundness of the closure is done.
- **Closure of a fixpoint, the plan (next, before termination).** If
  the closure misses a case, the exec code changes, and that would
  invalidate termination work.
  - *Represented sets* (Bool, from the state):
    - K: `ks.inb`.
    - An open a with member (r, w): r = F gives `Im(w y) ∈ K`; another
      root gives `w y` in r's rebuilt hull.
    - A collapsed sketch segment: `rep.inb` of its set.
    - Any other node: its direction is 0, so every form (z ∈ K²
      trivially).
  - *Fixpoint facts* (each check passed):
    - no explosion;
    - F's generators have Im in K;
    - no complex line at free roots (indset);
    - no root holds a rotation of an outside open node (label tests
      None; complete by hs_lab_some / ks_lab_some);
    - links complete for each collapsed c and node b, and from roots
      (qspan).
  - *Theorem:* every valid derivation's conclusion is represented, by
    induction on Der. Membership is invariant under SameV (residuals
    read the polynomial: zero_of_in / in_of_zero / in_tr).
  - *Per rule:*
    - K rules: spans.
    - DBack: F's set is {Im ∈ K}.
    - DLine: F's members automatically; free roots by indset; never at
      collapsed nodes.
    - DPPrem / DSelf: generators.
    - DPLin / DKnown: spans plus K².
    - DFrame: F.
    - DVoid: Full, or explosion for open nodes.
    - DTurn / DThrough by the two nodes' kinds:
      - same component: labels unique up to Q, else a complex line;
      - different components: a merge would have been found;
      - collapsed: links and generators.
  - *The hard cases, worked out.* For open nodes, write (r_a, w_a) for
    a's root and label and Q_r for r's set.
    - **Turn, both open, different roots:** the merge check found no
      nonzero v with v z_b in Q_{r_a}. So g = 0, and the conclusion is
      0.
    - **Turn, both open, same root r:** let u = w_a conj(g) conj(w_b).
      Q_r holds y = w_b z_b and (u/|w_b|²) y. If u is not real, Q_r
      holds i y, a complex line, so y ∈ K², so z_b ∈ K²: an explosion
      (the void check). So u is real, and w_b g z_a = (u/|w_a|²) w_a z_a
      ∈ Q_r.
    - **Through, both open:** the same two cases.
    - **Turn, a open and c collapsed:** w_a conj(g) is in G_rc. The
      root-link check puts conj(w_a) g in span(stored(c, r)). c's
      generators hold u·g' for each stored u and g' ∈ Gen_r, so P_c holds
      conj(w_a) g w_a z_a = |w_a|² g z_a.
    - **Turn, c collapsed and b open:** conj(g) is in span(stored(c, b)).
      b's root's generators hold w_b conj(u) z_c for each stored u, so
      Q_{r_b} holds w_b g z_c.
    - **Turn, both collapsed:** the lins generators of c'.
    - **Through, c collapsed and b open:** conj(g) is in
      span(stored(c, b)).
      - When r_b ≠ F, c's generators hold u conj(w_b) H_{r_b}.
      - When r_b = F, the tie: all of c's ties are parallel to the first,
        U. Each tie's turned form is a generator of F, so frame-back gives
        cross(U_i, z_c) ∈ K. Two independent ties would make z_c ∈ K², so
        c would be Full. So u·P_F ⊆ Tied(U).
    - **Full nodes** (z ∈ K²): every g z_c ∈ K² is in every set. Links
      from Full nodes are not needed.
  - *Extra invariants this needs:*
    - roots carry (1, DSelf);
    - every open node has exactly one member record, whose root is a
      root;
    - every fact is in K (K only grows);
    - stored labels per pair are at most two, independent when two;
    - qspan is sound: a span member is a real combination of the stored
      labels. That needs the labels nonzero (have) and Cramer for two.
  - *Label algebra needed:* gmul linear in the label, w conj(w) = |w|²
    real, real labels act as scalars, and "u not real ⟹ i y in the
    span of y and u y".
  - *Refinements found re-reading the code (2026-10-27, after a
    compaction):*
    - Sketch ids may repeat, so the member list can hold several records
      for one node (they evolve identically). The theorem reads "the
      record" as mem_of's, with three Data invariants: every record is
      the first record of its node (kept by reroot, since mem_of commutes
      with it); a record with a = r is (a, a, 1, DSelf a); every record's
      node is F or among snodes(segids). A Bool invariant says each
      sketch segment is collapsed in ctx or has a record.
    - A node with no record has the collapsed set crep(c). A segment
      outside segids has direction 0 (find gives no GSeg), so fullc holds
      and its set is everything; Open fails at it.
    - The fixpoint facts stay in their Bool form (mgs(..) == None, and so
      on), which is Data and reusable; each use extracts its instance by
      a lemma. A "for all" fact would be a function, usable once.
    - Turn with a = b needs no link: g z = 2 Re(g) z - conj(g) z, a
      combination of z_a and the premise.
    - The pair invariant as a Bool: every link's pair has its first two
      stored labels independent (pairok), kept because a link is added
      only when qspan of its pair's stored labels says no.
    - A hull's Bool test reads y through x + t y, faithful only when y
      does not mention t, and derivations reach forms that do (par(F,
      (t, 0)) by frame). So in the theorem a hull set is semantic: real
      combinations of the hull's kept generators (a Sigma over the
      coefficients, Data). The Bool test agrees with it both ways for
      forms below t, which is all the checks and the queries use (one
      way by linearity of the encoding, the other by the separation
      lemma). K, F's set and tied sets are exact as they are: their tests
      are polynomial spans with no encoding.
    - The sets share one shape: a membership kind (frame, hull, tied,
      all) closed under SameV and m1 x1 + m2 x2, holding (k, 0) and
      (0, k) for each K generator k (so K squared, for any form, by the
      combination K gives). Tied sets need no u != 0 for this.
  - Then NotDirDerivable is the contrapositive. An explosion derives
    everything: ∥(F, (0, e)) by ∥-void at F or ∥-through at the open
    void segment, then K(e) by frame-back, and ∥(a, x) by ∥-void.
  - *Progress (2026-10-27, lib/dcreprpf.bend):* Repr and the fixpoint
    hypotheses bundle (Hyp); the rules zero, premise, K-add, frame-back,
    frame, par-lin, known, self, pprem, void and line, each a lemma
    `rule_*` from the premises' Repr. Along the way: the collapse test is
    sound as well as complete (lib/dcopenpf.bend `coll_sound`), and an
    open node always has a record (`open_rec`: a segment entity is among
    the segment ids, so collapsed or recorded; a non-segment's direction
    is 0).
  - *Turn and through, the remaining rules.* Write P_a for a's set, and
    (r, w) for an open node's root and label. Cases by records:
    - both open, different roots: the merge check gives LZ(w_a conj(g))
      (zero_k / zero_h at mgF_none / mgR_none), so g = 0.
    - both open, same root: u = w_a conj(g) conj(w_b). Not real: Q_r
      holds y = w_b z_b and u y, so i y (gmul_i), a complex line
      (line.root), so z_b in K squared (unrot), against void.node. Real:
      the conclusion is a real multiple of w_a z_a (turn) or of w_b x
      (through).
    - one collapsed c, not Full: the link checks. lk.c gives
      conj(g) in LSp(stored(c, b)) for turn from c and through at c
      (bfree_ok / btied_ok, basis_in, lsp_trans); lk.r gives conj(w_a g)
      in LSp(stored(c, r_a)) for turn into c (bfree_ok / bk_ok,
      lsp_conj, basis_inc). The stored labels come from links, whose
      generators carry the conclusion: llinks at b (turn from c),
      lout.gens over r's generators (into c, r not F), lins (between
      collapsed nodes).
    - a link into F's component makes c Tied(U). Every tie T has
      cross(T, z_c) in K (its turned form is F's generator, then
      frame-back), so two independent ties make c Full; hence all ties
      are parallel to U, and cross(U, ·) of the conclusion lies in K,
      which a Tied set holds.
    - Full: every form; and a Full c's direction is in K squared.
    - a = b collapsed: g z = 2 Re(g) z - conj(g) z (g2re).
  - The shared tools: a rotation gmul(L, ·) sends a hull's set into a
    set S when it sends each kept generator in (kept generators are
    among the inputs of the fold); the stored labels' first two are
    link labels or 0.
  - *Done 2026-10-27 (gate PASS @ecc2e45):* the closure theorem
    (lib/dcclosepf.bend `dclose_closed`, induction on Der over the rules
    in dcreprpf, dcturnpf, dcpushpf, dcturncpf, dclopf, dcftiepf) and
    its negative answers (lib/dcdecpf.bend `not_dir`: DC.holds false at
    a fixpoint gives the spec's NotDirDerivable). Positive answers too
    (lib/dcholdpf.bend `hold_ok`: DC.hold.der valid and proving e when
    DC.holds is true; lib/dcexplpf.bend `expl_ok`: an explosion's
    DC.expl.der proves any e by K). Then owed for B4: the refutation
    decision (a refutation is found iff one exists: Motzkin over K's
    generators, a derived collapse, an Angle on a K-collapsed segment),
    and termination (done 2026-10-30, below). B4 also needs sub(nd, nd)
    for the reported nd (the draft spec's own sub, not spec/solve's).
- *Done 2026-10-30 (gate PASS @eb5b6ad): termination.* `DC.dfuel(es,
  fs)` (lib/dclose.bend) is enough fuel: lib/dctermpf.bend
  `dclose_term` / `dclose_nostep`, gated as b3_term. The measure adds
  three counts, and every round that does not stop takes one down while
  the others stay:
  - *K's pivots* (lib/dckslpf.bend): `DC.bases` lists every fact's
    equation and statement parts and every node's direction parts, and
    `DC.kmons` their normal forms' monomials. A new K row's pivot is a
    base monomial (else its coefficient there would be 0: dcbasepf
    `span_cz`, through the elimination's Rel) and no earlier pivot.
    The plan's affine-below-t bound was not needed: the bases' span is
    the invariant (lib/dcgspanpf.bend: every generator form the closure
    reads is a rotation, sum or chain of directions, statements and K
    facts; a segment outside the sketch has direction 0).
  - *The new K fact is new* (lib/dcclprogpf.bend). Frame-back checks it.
    For a complex line x = g_d − (earlier kept ones), cl.k gives K the
    real part when K lacks it, else the imaginary part, which K lacks too:
    with both in K, x's encoding is in K squared's hull span (khull spans
    each K generator k as (k, 0) and (0, k)), so g_d's encoding would lie
    in the span of K squared's and the earlier kept generators', and the
    fold kept g_d because it did not (`hk_ind`: the kept generators pass
    indset after khull's rows; the walk carries those rows as ghosts).
  - *Roots and links* (lib/dcslotpf.bend): a merge reroots a root under
    another root, which takes its own record off the roots and puts none
    on; a link is added only while its pair holds fewer than two labels
    (qspan says yes from two), and only for a collapsed sketch segment
    and a listed node.
  - proto/dclose_run.bend now runs with DC.dfuel: the same eleven
    answers, fuel 42 to 76, about 74 ms.
- Still owed for B4: sub(nd, nd) (the draft spec's own sub).
- *The refutation decision, done 2026-10-30 (gate PASS @45a6378):*
  lib/dref.bend `DF.dref`, lib/drefpf.bend `dref_sound` (any o with its
  OutInv) and `dref_complete` (at OFix), gated as b3_dref_sound and
  b3_dref_complete over LRefOk, the spec's RefOk with the sides and the
  Angles given as lists (the sk-level bridge is B4's). **B3 is complete.**
  As designed: Exec, at the
  closure's result o, for the facts fs = rfacts(sk, c:cs), the sides
  ss = csides(sk, c:cs) ++ esides(sk), and the Angles among c:cs:
  - OOne{d}: RMotz{[d], [−1], zeros(|ss|), −1}.
  - OVoid{g, dr, di}: RColl{dr, di, g}.
  - OFix{s}: sk-13a's refute(kexprs(K), ss). Some cert gives
    RMotz{K's derivations, cert}. None: the first Angle whose first or
    second segment has both direction parts in K gives
    RAngle{ks.der(Re z), ks.der(Im z), p, fst}. None: no refutation.
  - OStep cannot happen with DC.dfuel (dclose_nostep).
  - *Sound:* K's derivations are valid K judgments (KInv), and the
    certificate is over exactly their conclusions (refute_ok); OOne and
    OVoid by OutInv; RAngle by ks_der_ok at the Angle's segment.
  - *Complete* (None gives NoDirRef):
    - RMotz{ds, ls, ms, k}: each conclusion is derivable, so in K's span
      at the fixpoint (dclose_closed: Repr of JK{e} is ks.inb). So
      lin(ls, conclusions) is a combination of K's generators, with one
      composed coefficient per generator (padded to refok's lengths): a
      Refutes0 over kexprs, against refute's NoRef (satpf).
    - RColl{dr, di, s}: s open with both parts in K contradicts the
      fixpoint's void check (Fx: voidseg None; a segment outside the
      sketch is not open).
    - RAngle{dr, di, p, fst}: by the closure theorem the Angle's segment
      has both parts in K, so the check finds an Angle (maybe another).
  - Stated over (es, fs, ss, the Angles); the sk-level RefOk is bridged
    in B4.
- Then the decision interface, and B4.
  - Speed lesson: a four-atom degree-2 normalizer identity with squares
    took over 120 s. One square at a time, plus degree-1
    rearrangements, takes seconds.
- Scope, honestly: this is the largest proof of sk-13b, several more
  sessions.
- The plan as written:
- Union–find over segments and F, with labels. Each component keeps its
  *hull*: the real span of the vectors known parallel to its root,
  reduced modulo K.
- To a fixpoint:
  - a segment whose direction lies in a hull joins that component;
  - F's hull gives K its imaginary parts (frame-back);
  - a complex line in a hull gives K its parts (complex line);
  - K's new rows reduce the hulls.
- It terminates: K's dimension and the number of components are bounded,
  and each round grows one or shrinks the other.
- Proven:
  - the final state is closed under every rule, so it contains the least
    closure (completeness, by induction on derivations);
  - everything in it is derivable (soundness), with the nd recorded;
  - a refutation is reported iff one exists.

### B4. The pass
- For each driving c:
  - the degree-0 check (unchanged);
  - the closure of P and c, giving Conflict with the deletion filter
    generalized. Its seed is the constraints behind the refutation's
    facts, including those behind its K combinations;
  - each equation's drop: degree 0 over the basis, else a derivation over
    P;
  - then structure, Over, Kept and Amber (unchanged).
- If c is kept, the tentative closure becomes the premises' closure.
- Certificates compose with those of the dropped equations they use.
- Proven: `solve_honest` for the extended `Honest`, and the global
  theorem.

**As designed 2026-10-30.**
- **Staging.** The solver keeps running sk-13a's pass until the switch.
  The new pass is built beside it and proven honest against the draft's
  Honest, so every proven law stays proven meanwhile. It reuses sk-13a's
  pass infrastructure (kbpf, clslpf, solvedpf, ownpf, cwpf, gmpf, prepf),
  which is typed over spec/solve.bend's Class, so Class must be one type
  first (B4.0). When to switch is for Danielle at the check-in: then, with
  the laws downstream of Honest open until B5–B7 re-prove them; or after
  B7, with those laws re-proven against the new pass first.
  *Decided 2026-11-01 (Danielle): re-prove, then switch.* B5–B7 are proven
  against the new pass and the draft Honest beside sk-13a's (the gate
  green throughout), and the switch comes once they all are.
- **B4.0, the spec staged** (the gate stays green):
  - spec/solve.bend takes the shapes agreed in B0, `Drop{j, nd, c}` and
    `Conflict{s, nd}`, and the draft's definitions that do not clash
    with its Honest: the direction facts (ents ... NoDirRef), Ref0,
    NoRef0, NoRefute2 and the laws' nd lists. Its Honest is unchanged and
    reads no nd, and honest_unique compares kinds and drops only, so no
    proven law changes meaning.
  - spec/_draft13b.bend keeps only the extended Honest (drops_ok ...
    Honest), importing the rest from spec/solve.bend.
  - sk-13a's pass emits nd = Nil. Patterns change through the drafts
    (tools/drafts regenerate lib exactly, checked 2026-10-30).
  - The owed sub(nd, nd) is then prepf's `sub_refl`.
  - *Done 2026-10-30 (gate PASS @af059dd).*
- **B4.1, reindexing derivations.** Premises are by index (DPrem{i}), so
  a derivation over the facts of fewer constraints is moved to more by
  mapping indices. rfacts(sk, c:cs) is a sublist of rfacts(sk, c:cs') for
  cs within cs' (a SubF witness, as conflictpf's SubE). dmap renumbers a
  derivation; concl, nd and Valid carry over (an index past the small
  list maps past the big one, so concl is equal for every derivation). A
  Motzkin refutation's side multipliers are padded with 0s along the SubS
  of the sides (conflictpf's supp_mono_s). Result: NoDirRef(sk, c, cs',
  cx) gives NoDirRef(sk, c, cs, cx). This is the deletion filter's
  monotonicity.
  - *Done 2026-10-30* (lib/dmappf.bend `nodir_mono`, gated as
    b4_nodir_mono).
- **B4.2, the bridge and coverage.** angl(sk, cs) lists Ang{p, k} for
  every p in cs with a kind (non-Angles are harmless: angle_seg is None
  there). LRefOk over (ents, rfacts(c:cs), cx, cats(csides(c:cs),
  esides), angl(c:cs)) is RefOk(sk, c, cs, cx) both ways. The closure
  runs with t = 1 + nvars (zb needs t > 0); zb and fb follow from
  `within`.
  - *Done 2026-10-30* (lib/dbridgepf.bend `lref_of`, `lref_to`,
    `nodir_of`, `zb_tv`, `fb_rf`; gated as b4_lref_of, b4_nodir_of,
    b4_fb). The exec of B4.3 is lib/dconflict.bend.
- **B4.3, refutability and the filter generalized** (lib/dconflict.bend).
  refutable2(c, cs) is sk-13a's degree-0 test, else the closure of
  rfacts(c:cs) in c's context with dref. Chinneck's filter runs it over
  every kept constraint, as sk-13a's does. A seed (only the constraints
  behind the refutation's facts) would need its own refutation proven by
  moving the derivation to a sublist of facts; it is left as a measured
  optimization. The conflict's nd: Nil when c with s refutes at degree
  0; else the refutation's nd, without the Angles' segments, each segment
  once. Proven: ConflictOk, the irreducibility by B4.1 and dref_complete.
  - *Done 2026-10-30* (lib/dconflictpf.bend `conflict2_ok`, gated as
    b4_conflict; a planted wrong nd is rejected).
- **B4.4, the walk** (each equation k of c, in order):
  - degree 0 against the basis rows, as now: Drop{k, Nil, cert};
  - else the closure of the facts: every equation of kb with its drop's
    nd, and c's earlier equations not dropped;
  - a fixpoint that holds e_k, or an explosion, drops it:
    Drop{k, DR.nd(der), cert}. The nd is kept as is, repeats included:
    the certificate's h is one squared length per use;
  - a fixpoint that does not hold it: e_k joins the basis
    (NotDirDerivable by DEC.not_dir).
  - The facts are SV.facts.go over kb with the classes so far. They
    equal SV.dfacts with the final classes, since a class drops only its
    own equations (downs), and ofacts reads d only before k.
  - Proven: DropsOk and DropsNd (lib/dcwpf.bend).
  - *Done 2026-10-30* (lib/dcwpf.bend `cw2_final`, gated as b4_walk;
    planted errors rejected: an empty recorded nd, and a swapped
    decision). DropsNd rides along the walk as "the drops so far
    suffice, then so do the final ones".
- **B4.5, the pass** (lib/dpass.bend): one constraint is the degree-0
  test, else the direction refutation, then the conflict (B4.3), else the
  walk, then Over, Kept and Amber as now. The state is sk-13a's plus the
  classes so far. The closure is rerun from the facts for each test;
  "the tentative closure becomes the premises'" is an optimization to
  measure, not needed. Proven: the draft's Honest for it
  (lib/dpasspf.bend), with sk-13a's PInv and its generic lemmas.
  - *Done 2026-10-30 (gate PASS)*: lib/dpasspf.bend `pass2_honest`,
    gated as b4_honest. The classes so far agree with the final ones on
    every equation of an earlier constraint (pcf, through downs: a later
    class drops only its own equations).
- **B4.6, each drop's reason, proven** (Danielle, 2026-11-01; replaces
  "the certificates": a derivation's identity composed with the dropped
  facts' certificates, h = ndh(nd), checked by the verdict and proven to
  pass in B7). Decided: a drop is correct by construction, nothing about
  it is checked at run time, and the answer still says why each equation
  is dropped. The polynomial identity would repeat what lib/dirpf.bend's
  `sound` and pass2_honest already prove (and be unreadable: angle-lines'
  numbers run to thousands of bits); the readable reason is the witness
  the pass already has.
  - Data: `Drop{j, nd, why}`, `Why` either a degree-0 drop's constants
    over its basis (Derivable's witness: Ident(g_j, lin(ls, basis))) or
    a direction drop's derivation (DirDerivable's witness). Comb and Mul
    go.
  - (a) sk-13a first, the gate green throughout: lib/pass.bend records
    the elimination's constants; a lemma that each recorded reason is
    its drop's witness (from lib/drvpf.bend / lib/ckpf.bend's dgood);
    solve_drop and the zeros chain (lib/vrdpf.bend zeros_mark, read by
    solve_exists and the others) take each drop's truth from it instead
    of the verdict's drop check, which goes (VD.exact keeps the amber
    sides' refutations); solve_complete loses the drop check's part.
    Every sk-13a statement unchanged.
    *Done 2026-11-01 (gate PASS, tools/regress.sh PASS):* spec/solve.bend
    `Why` (WLin{ms}: Mul{i, q} with q a constant; WDer{d}), `Drop{j, nd,
    why}`, Comb gone; lib/dropok.bend holds what a degree-0 reason must
    pass (moved out of the verdict, never run); VD.exact = the amber
    check alone; lib/ckpf.bend why_pass (the drops' half of ckall) beside
    ck_pass; lib/solvepf.bend reads the pass's adjacency off the verdict
    (wfd_of, cov_of, adjb_of, moved down from lib/blamepf.bend) so
    solve_exists gets the drops from why_pass (hwhy), its statement
    unchanged; solve_drop and solve_amber likewise. The direction pass
    already records WDer{der} (dcert gone).
  - (b) the direction pass records the closure's derivation; the draft's
    Honest (DropsNd) says each recorded reason is its drop's witness
    (the constants: Derivable's identity; the derivation: Valid, Proves,
    its nd within the drop's), so the explanation is a theorem;
    lib/dcwpf.bend already proves the recorded derivation valid (dd_ok).
    *Done 2026-11-01 (gate PASS, tools/regress.sh PASS):*
    spec/_draft13b.bend `why_ok`: a WLin{ms} reason names only equations
    the drop may be combined from (`in_basis`: a solved one of a
    constraint before c, or c's own before j not dropped, by position)
    and g_j is the same polynomial as `SV.mlin(eqs, ms)` (spec/solve.bend,
    which lib/dropok.bend now reads too: comb.rhs gone); a WDer{dv}
    reason is DirDerivable's body for dv with the drop's nd. drops_nd
    says each recorded drop's why_ok (no longer the Or). lib/dcwpf.bend
    lin_wit (the elimination's identity, ckpf's rhs_lin, and the basis
    positions: bp0 from pib, now a hypothesis of cw2_final and the walk,
    us from the walk's invariant and the final drops agreeing below k)
    and dwit_k (the closure's derivation, dsk.w).
  - At the switch (B5/B6): a direction drop holds wherever the system
    solved holds and its nd segments are nonzero, by `sound`, its facts
    holding by induction over the equations (an earlier drop's fact
    where its own nd is nonzero); the nd sides over the box are B5's.
  - The page (B8) can show a drop's reason: the combination, or the
    constraints a derivation's facts come from and the segments it
    assumes nonzero.
- **B4.7, a run**: sketches 4, 8 and 9 and proto/dclose_run's eleven,
  with the cost measured.
  - *First run, 2026-10-30* (lib/dpass.bend's exec, before its proofs;
    proto/probe_dpass.bend against proto/probe_pass.bend on
    proto/sketches; 8 and 9 are not on disk):
    - **Decisions right.** The 17 sketches without direction
      constraints get the same classes. vertical-twice (sketch 4) and
      its raw input change at exactly the two planned places: one
      constraint amber (its equation dropped by directions), and the old
      Over kept.
    - **Too slow.** base 59 ms -> 8.1 s; oncircle-pairs 0.37 s -> 123 s;
      vertical-twice 0.46 s -> 234 s; angle-lines 58 ms -> over 300 s.
      The target was a few percent of the solve.
    - **nd bloated.** The amber drop's nd has 530 entries over 5
      distinct segments: hold.der's membership chains carry every
      generator's derivation, coefficient 0 or not, and nest.
    - **Where the time goes** (callgrind, base and angle-opposite): no
      single hot spot. The closure runs about twice per constraint, and
      each run rebuilds every hull from the skeleton each round, with
      K squared inside every hull, and reruns every check; directions
      are recomputed by entity lookup (SK.find, about a tenth of base's
      instructions), conclusions of nested derivations are recomputed,
      and angle rotations make the rationals large (bit-serial Pos
      addition dominates angle-opposite).
    - So B3's closure needs a performance redesign before the switch.
      B4.4 and B4.5's proofs use only the closure's proven interface
      (dclose_ok, dclose_nostep, hold_ok, not_dir/dec_none, expl_ok,
      dref_sound/complete), so they survive a redesign that keeps it.
- The global theorem is not needed by Honest; it is taken up where a law
  needs it (B6).
- **B4.8, the closure made fast** (designed 2026-10-30, after B4.7).
  Danielle: optimize as much as needed, as long as every proven
  statement stays the same. The closure's interface (dclose_ok,
  dclose_nostep, hold_ok, dec_none/not_dir, expl_ok, dref_sound/complete,
  hyp_of) keeps its statements. Underneath it there are two changes, of
  different kinds:
  - *Measured shape* (proto/probe_dstats.bend, every earlier constraint
    kept): a run is 1 to 22 rounds; nearly every round is a merge or a
    K addition, and there were no links. K is about as large as the
    facts (17 on base, 41 on vertical-twice), and roots go from one per
    segment down to a few. Each round rebuilds about two full hulls per
    root (clxs, then mgs), each with K squared's 2|K| generators first,
    and every insertion carries sk-13a's combination vector (O(rows) Z
    products per step). The checks evaluate every alternative eagerly:
    mgs builds every root's hull and the merge derivation of every later
    success, even after F's check found one. The label tests encode
    every generator before knowing they need any. About 60% of base's
    instructions are the runtime freeing those terms.
  - **A. Minimal derivations (nd).** HS.pchain and KS.kchain skip
    multipliers that are 0. hs.der and ks.der keep their lemmas
    (hs_der_okd, ks_der_okd: VD, proving the form asked); pchain_x and
    kchain_e become SameV/Same statements, or HS.clin skips 0 alongside.
    Tried unproven on vertical-twice: the amber drop's nd goes from 530
    entries to 20, with the same decisions. This changes derivations, so
    it is re-proven where the chains are unfolded (lib/hspacepf.bend,
    lib/kspacepf.bend, lib/dcderpf.bend, and the pchain_x users in
    lib/dcclprogpf.bend, lib/dcclxpf.bend, lib/dctiedpf.bend,
    lib/dcgspanpf.bend). *Done 2026-10-30:* pchain_x is SameV to clin and
    kchain_e Same to lin; pchain_below replaces the rewrite through
    clin_below; the pointwise users go through enc, i and cross
    congruences. Gate PASS.
  - **B. The same closure, computed fast.** The new run returns exactly
    the Out the current one does (an equation, dclose == dclose_ref), so
    B3's proofs stand unchanged, renamed to dclose_ref; each interface
    lemma is its old proof after one rewrite. What changes is only how
    much is computed:
    - B.1 Lean residuals. A residual's polynomial does not depend on the
      combination vectors (EL.step's p part reads only p, pv). resid_p
      and a lean fold over rows without cb, with the projection lemmas
      resp(resid(rows, e)) == resid_p(proj(rows), e) and proj(hfold(gs,
      h)) == lfold(gs, proj(h)). Every Bool a check decides on is then a
      lean one.
    - B.2 Short-circuit and lazy. Each check returns its first item
      without computing the alternatives after it; a label test's
      generator encodings, and an item's derivation, are computed only
      once the lean test has found it, by the current full functions (so
      the item is the same data).
    - B.3 Lean K squared, cached. The run carries, per open node, the
      lean rows of khull(K, node), which depend only on K: updated by two
      lean insertions when K keeps a new generator (khull of K's list
      with one appended is the fold of its two forms on the old one).
      Each round, a free root's lean set is its own generators folded on
      that, once, shared by clxs, mgs and lks.
    - B.4 The fast round equals round under the cache invariant (cache
      == proj(khull(Sk.k(s), node))); the fast run equals run; dclose is
      the fast run, and the old definition is dclose_ref.
    - B.5 Re-measure on proto/sketches.
    - *Done 2026-10-30:* lib/lres.bend and lib/lrespf.bend (lean residuals
      and their projection lemmas), the fast run at the end of
      lib/dclose.bend (dclose; the old one is dclose_ref), and
      lib/dfastpf.bend (dclose_eq: dclose == dclose_ref). Only
      dclose_ok, dclose_term and dclose_fix unfold dclose; each rewrites
      by dclose_eq first, and every statement is unchanged. The cache is
      a list of (node, lean rows of K squared at that node), looked up by
      node, with a computed default.
    - *Measured* (native, one thread, the whole pass): base 8.1 s ->
      1.2 s; oncircle-pairs 123 s -> 12.9 s; vertical-twice 234 s ->
      21 s; zeros 1.0 s; the S8 sketches about 10 ms. Every sketch gets
      the same classes as before (nd aside, which A shrank). Base's
      instructions went from 69.5G to 8.6G; about 64% of what is left is
      the runtime freeing terms (bit-list integers and polynomials).
    - *angle-lines still does not finish* (over 600 s): in the run for
      its Angle, each round takes longer than the last (0.1 s, 4 s,
      11 s, then over a minute) with K at 5. That is number growth, not
      structure: S.Q is never reduced (a label product doubles its
      size), QN.clr multiplies every constant's denominator (2^40 each
      here), and the fraction-free elimination never removes content.
  - *Number growth, measured 2026-10-31* (proto/probe_dtime.bend's sizes,
    angle-lines' Angle run): K's rows reach 160, 320, 2558 bits in five
    rows, almost all of it factors of 2; a merge then gives a label that
    is 0 over a 6392-bit denominator (5602 bits of twos), and member
    forms with 6392-bit constants. The inputs are dyadic (the GUI sends
    floats over 2^40); QN.clr multiplies every constant's denominator, so
    a form with n such constants is cleared by 2^(40n).
    - *Experiment (unproven, reverted):* clearing a sum by the larger of
      two power-of-two denominators instead of their product, plus labels
      without common twos (0 over 1): K's rows become 40, 40, 318 bits;
      angle-lines' whole pass finishes in 32 s (classes K K K K, as
      sk-13a), where it never finished; the other sketches do not move.
      Halving residuals added nothing once clearing was fixed. One label
      stayed 2132/2132 bits, both odd: a small ratio with a large common
      odd factor, which only a gcd removes.
    - *Why it is not a small change:* QN.clr is the cleared normal form
      under all of sk-13a's elimination and refutation (EL.start, EP.NE,
      lib/coefpf.bend's coef = cz(m, norm(clr e)) / den e). coef_add,
      coef_lin and their kin are data equalities that hold because a sum
      is cleared by the product, and refpf, satpf, drvpf and indpf rewrite
      with coef about 130 times. Two ways, both large: (a) change clr
      everywhere and make coef's lemmas Q.eq-based (the main solver gets
      smaller numbers too); (b) closure only: hand elimination each form
      simplified to one denominator, proving Same, which changes every
      K/hull row relation in B3's proofs. A gcd for the odd part needs no
      check-and-fallback: Stein's binary gcd can carry quotient witnesses
      (g q_a = a, g q_b = b), and fuel running out may return 1, which
      divides everything.
    - *Danielle, 2026-10-31: (a).* Next: QN.clr clears a sum by the larger
      of two power-of-two denominators (clr_ok's statement kept), and
      lib/coefpf.bend's lemmas become Q.eq statements, their users in
      refpf, satpf, drvpf and indpf following; then labels without common
      twos and a witnessed gcd for the odd part.
    - *The design of (a), 2026-10-31:*
      - lib/qnorm (its draft): sd(x, y) is a shared denominator SD{d, fa,
        fb} with x fa = d = y fb (sd_a, sd_b). Both even: twice sd(x/2,
        y/2); otherwise the product. So common factors of 2 are taken
        once, and for powers of two d is the larger. den and clr of a sum
        or a difference use it; constants, products and negations are as
        before. clr_ok's statement is unchanged.
      - lib/coefpf (made a draft, for @RING): coef_add, coef_sub and
        coef_lin become Q.eq statements; coef_neg, coef_cmul and the
        constants stay data equalities; coef_zero and ident_coef keep
        their statements (a cancellation of d). num0: a rational Q.eq to
        one with numerator 0 has numerator 0.
      - The users, about fifteen sites: under ofq the rewrite goes
        through QE.ofq_eq (satpf's psi_add, psi_lin, psi_slin; indpf's
        psi_eq); under num through num0 (drvpf's drop_at, refpf's
        ident_m, dcbasepf's lin_cz). refpf's coef_slin becomes Q.eq, and
        tests/ident_laws' re-export of coef_lin follows. Every other use
        of den and clr treats them as opaque.
      - Later, sd's product case can divide by a witnessed gcd without
        changing its interface.
      - *Done 2026-10-31* (2b54294): gate PASS, regression PASS (every
        answer as before). The closure pass (native, one thread, other
        jobs running): base 1.19 s -> 0.41 s, oncircle-pairs 12.9 s ->
        4.1 s, vertical-twice 21 s -> 6.8 s, zeros 0.96 s -> 0.51 s.
        angle-lines still runs over 600 s. Its Angle's K rows are now 40,
        40, 318 bits (were 160, 320, 2558), but merges give labels whose
        cosine is 0 over a 792-bit, then a 7900-bit denominator, and
        member forms with 7900-bit constants: label products (LB.lmul)
        multiply all four denominators and never reduce, and their
        denominators are mostly odd (the elimination's pivots). So labels
        are next: zero as 0/1, then common factors out.
    - *Labels trimmed, 2026-10-31:* lib/lab.bend's qtrim (a zero part as
      0/1, the factors of 2 shared by numerator and denominator out) and
      ltrim (both parts). The closure trims a label where it stores one:
      a rerooted member's (reroot.one), the merge's link label (merge.go),
      a tie's (ctie.mem), and the label tests' (lab_of). bpair's i w is
      left as it is: its membership test is on the untrimmed form, and it
      only doubles one denominator before a trimmed product. Proofs:
      qtrim_ok (Q.eq) and qtrim_nz (same zero test) in lib/labpf.bend;
      gtrim and gtrim_c (a trimmed label, and its conjugate, act as the
      label: SameVD) and mok_trim in lib/dcgenpf.bend; nz_trim in
      lib/labnzpf.bend; tie_trim in lib/dcreppf.bend; the label tests
      through enc_gmul_q, im_gmul_q and cross_gmul_q; dcftiepf's tie
      relation is u == ltrim(lmul(..)), and crossU carries K membership
      along gtrim_c with ST.ri.tr. Every interface statement is unchanged
      (dfastpf and lrespf did not move). Gate PASS, regression PASS.
      *Measured* (the closure pass, native, one thread): angle-lines
      20.5 s (over 600 s before), each constraint at a fixpoint (K 1, 2,
      5, 6); base 0.41 s, oncircle-pairs 4.4 s, vertical-twice 6.8 s,
      zeros 0.51 s, oncircle-thrice 0.38 s, with the same outputs as
      before trimming. One label of angle-lines' Angle is still 2132 over
      2132 bits, both odd: the gcd for the odd part, next.
    - *The odd part, 2026-10-31:* lib/gcdw.bend, a binary gcd with its
      quotients: gcdw(fuel, a, b, k) with k = gkind(a, b) the step (both
      even, one even, both odd with a - b zero, positive or negative),
      passed in since Bend has no mutual recursion; out of fuel g = 1.
      lib/gcdwpf.bend: gw_ok/gcd_ok, g qa = a and g qb = b, by the steps
      (KindOk). qtrim now divides by the gcd (a zero part still 0/1);
      only qtrim_ok and qtrim_nz were re-proven. Gate PASS, regression
      PASS. angle-lines' closure pass 20.5 s -> 11.4 s (its large label
      4264 -> 80 bits); the others unchanged, every output the same.
      sd's product case could divide by the same gcd later.
  - *Profiled, 2026-10-31* (callgrind and instruction counts, closure
    pass): the native runtime evaluates arguments strictly, and matching
    a shared constructor costs a refcount bump per field (span_fade).
    - fe4bbeb: pins took its recursive insertion as an argument, built
      and dropped whenever the term went in early; now a thunk (the same
      for mcmp and minsert was neutral, monomials being short).
      f5b2ef1: a lean row carries its pivot coefficient (lstep looked it
      up by a scan per step). cd7484b: cleared form and denominator in one
      pass. No proof statement changed; outputs identical.
    - Instructions, closure pass then the whole solve for comparison:
      base 3.49 G -> 2.39 G (solve 0.62 G); oncircle-pairs 36.2 G ->
      23.6 G (2.9 G); vertical-twice 59.9 G -> 38.7 G (34.2 G);
      angle-lines 84.0 G -> 83.0 G (14.3 G).
    - What is left: on base, the runtime's freeing and refcounts are
      about 60%, coefficient scans of residuals (EL.cz, a monomial
      compare per term) about 25%, entity lookups for directions
      (SK.find) about 5%. On angle-lines, bit-serial multiplication in
      the elimination's scalings (pscale; Pos.add called 2 M times from
      Pos.mul) is most of it: the fraction-free residuals grow.
    - Candidates: cz stopping early on sorted residuals (needs reducedness
      threaded through lrespf); directions per node cached; content
      removal in the lean residuals, proven up to positive scaling (zero
      tests unchanged), for angle-lines. None of these closes the gap to
      a few percent of the solve on its own; the pass runs the closure
      once per constraint, each run from scratch.
    - *Content removal, tried unproven 2026-10-31 (reverted):* zero tests
      on residuals divided by their coefficients' gcd after each step,
      stored rows kept exact (so dfastpf's equalities would stand).
      Every step: angle-lines 83.0 G -> 65.1 G, but base 2.39 G -> 8.68 G,
      vertical-twice 38.7 G -> 101 G. Only above 256 bits: angle-lines
      -> 63.1 G, base +60%, vertical-twice and oncircle-pairs +47%: each
      added row is reduced twice (content-reduced for the test, exact to
      store). Reducing stored rows too would turn dfastpf's cache
      invariant from equalities into positive-multiple relations, a large
      rework for about a quarter of one sketch. Not pursued.
    - *Within one solve the cost is quadratic* (measured 2026-10-31): the
      pass calls the closure about twice per constraint over a growing
      prefix, each call from scratch, and a call costs about in proportion
      to its facts. vertical-twice: 33 calls, 4.3 s in all, the last 0.34
      s; base 15 calls, 276 ms, the last 49 ms. Perfect reuse would bound
      the gain near the last call's cost; context changes (a kept
      equation collapsing a segment) limit it.
    - *Danielle, 2026-10-31:* first the single-call optimizations (cz
      stopping early on reduced residuals; directions cached), then
      measure how often a memo across calls (pure values, outputs
      byte-identical) would hit, then decide between it and an
      incremental closure. An incremental closure is acceptable only with
      its correctness proven in the most general proper way.
    - *The single-call items, looked at 2026-10-31:* cz stopping early, and
      scaling by a constant as a coefficient map, are equal to today's
      only on reduced polynomials, while dclose_eq is unconditional and
      elimpf's step_zero/step_keep carry no reducedness; either needs a
      reducedness invariant threaded through dfastpf's run or through
      elimpf (a few hundred lines, perhaps 10-15%). Direction lookups
      (SK.find) come from the spec's DR.concl recomputing nested
      conclusions when generators are encoded (lh.add, kexprs), so the
      cache would be of generators' conclusions inside K and the hulls,
      a representation change (perhaps 5%).
    - *Where a call's time goes* (measured by doing one part twice,
      2026-10-31; base, vertical-twice): the initial K squared cache
      (kc.of, every open node's lean khull of K0) is 40% and 30% of the
      pass; root hulls (rls) 6-7%; cache updates within a call (kc.upd)
      4-5%; the rest (checks, derivations, the rounds) about half.
    - *A memo across calls for the initial cache* (byte-identical
      outputs): K0 = kinit is ks.add folded over the facts in fs order
      (DPrem{i}), and rfacts lists facts in the sketch's equation order,
      so a constraint's second call (dirref: the kept constraints and c)
      extends its first call's facts, and the next constraint's extend
      whichever earlier list has its kept set. So the previous call's
      cache C0 for K0(fs) gives K0(fs ++ new) by one kc.add per new fact,
      the step dfastpf already proves (kc_upd_inv, lfold_cat); a context
      change only drops or adds open nodes. Needs: concl unchanged when
      fs is extended, for derivations below len fs (so K0 and its rows
      agree); dclose with a given C0 under CacheOk equals dclose; the
      pass threading the memo, with a pass-level equality so B4.4/B4.5
      stand. Bound: the kc.of share, 30-40%.
    - *The memo, as designed 2026-10-31.* The pass keeps M = MK{n, k, C}:
      K from the facts R = rfacts(sk, kb) of the kept constraints so far
      (n = their count, k = kinit over R), and C the cache of k's rows
      for every segment node (not only the open ones, since contexts
      differ between constraints).
      - A call reads M through dclose.m, which is dclose with that k and
        the open nodes' entries looked up in C (kc.get). dclose_m_eq:
        it returns what dclose returns, given k = kinit(fs) and CInv for
        fs (so frun_eq applies as in dclose_eq).
      - Each call's facts extend R as far as derivations can see them:
        c's refutation call reads rfacts(sk, c : kb) = R ++ rfacts(sk,
        [c]) (owners sorted, kb below c); an equation's call reads F0 ++
        (c's earlier equations not dropped), and F0 differs from R only
        in nd, which no conclusion reads. So M is extended by mext (one
        ks.add and one kc.add per new fact, the steps dfastpf proves:
        kc_add_inv) and handed to dclose.m.
      - The facts: Pre(R, fs), fs agreeing with R on e and ds at every
        position of R; DB(d, n), every premise of d below n. concl_pre: a
        derivation's conclusion depends only on the facts it cites. From
        it, ks.add, kinit, lh.add, lfold, lkhull and CInv carry from R to
        fs (k's derivations are premises below n: kinit_below), and
        kinit over R ++ ys is kinit over ys after kinit over R.
      - After c: if c is kept (its class not red), kb gains c and M
        becomes the memo of its refutation call (rfacts(sk, kb ++ [c]) =
        rfacts(sk, c : kb)); otherwise M stays.
      - Proven statement: pass2m(..., M) = pass2(...) under the memo's
        invariant, by one2m = one2 (refutable2.m = refutable2, cwalk2.m
        = cwalk2); classes2 runs pass2m, and classes2_eq lets
        lib/dpasspf.bend keep its proof (it unfolds classes2 in three
        places). final2_st likewise. The conflict's support and nd calls
        keep plain dclose (subsets of kb, and rare).
      - *Built and proven 2026-10-31.* lib/dmemopf.bend (Pre, DB,
        concl_pre, the carries, kinit_below/kinit_cat, mext_ok,
        mext_reuse, dclose_m_eq) and lib/dpassmpf.bend (rfacts_split,
        facts_pre/facts_len, mstart_ok, cwalk2_m_eq, one2m_eq, one2_kb,
        pass2m_eq, classes2_eq, final2_st_eq); lib/dpasspf.bend reads
        classes2 through classes2_eq (three places). Gate PASS, regress
        PASS. The pass (proto/probe_dpass.bend, instructions): base 4.85 G
        -> 3.09 G, oncircle-pairs 48.8 G -> 35.3 G, vertical-twice 79.1 G
        -> 56.9 G, angle-lines 124.6 G -> 124.5 G (its time is in the
        rounds); every output byte-identical.
    - The other half (the rounds replayed from scratch each call) is what
      an incremental closure would address (Danielle: only with a fully
      general correctness proof).
    - *Incremental closure, design 2026-11-01* (Danielle: go ahead).
      - What the B3 proofs already give: run_ok, run_fix and run_t hold
        from ANY start state with the invariants (SkInv, ShInv, KSpan;
        μ below the fuel for run_t), and the closure theorem, dec_none
        and dref_complete read only RR.Hyp at an OFix state. So a run
        started from any valid state ends, and its fixpoint decides
        exactly.
      - The start: the last fixpoint, with the new facts given to K
        (ks.add DPrem{i}: the round's own K step, so the invariants
        keep) and its cache extended (kc.add). Facts extend: SkInv
        carries by validity (a valid derivation cites only facts it has,
        so concl_pre applies), KF by the new facts in K, KSpan by the
        bases growing. Contexts: validity reads the context only
        through Open, and a larger context opens fewer nodes, so a state
        carries to a context with the same open segments (SkInv and ShM
        read ctx only through coll). Measured: along the pass the open
        segments never change in base, oncircle-pairs, vertical-twice,
        angle-lines.
      - Fuel: dfuel bounds μ of every state with the invariants
        (kslack <= |kmons|; lslack <= its value with no links; rcount <=
        records <= nodes, records having distinct nodes by AllFirst and
        all among the nodes by RecN: a pigeonhole).
      - Fixpoints are mostly forest: vertical-twice's last call has ~7
        derived K facts and ~14 merges, no links. So the state must
        carry whole (K alone saves little).
      - Scope per constraint c: carry S, a fixpoint for rfacts(kb) in
        c's context (warm from the previous constraint's when the open
        segments agree, else from sk0 with the memo); c's refutation
        call and each equation's call start from S plus their own new
        facts; after c, S becomes the refutation call's fixpoint if c is
        kept.
      - *Danielle, 2026-11-01:* behaviour may change as long as it is
        provably correct, and more work for more cases is fine: so warm
        derivations are used directly (a drop's nd may differ from
        today's, still honest), and B4 is re-proven over the warm
        closure. Context repair deferred (start cold when the open
        segments differ).
      - Steps: (A) B4 over an interface, no behaviour change: Ex(o) in
        lib/dcexpf.bend (never a step; RR.Hyp at a fixpoint; OutInv at
        an explosion), dclose_ex for the closure from sk0; dd_ok, dn.o
        and dref_complete read Ex/Hyp instead of `dclose(...) == o`
        (done 2026-11-01, gate PASS). (B) the warm start and run: the
        invariants carry across fact extension and equal open segments,
        the new facts join K by the round's K step, dfuel bounds μ of
        every state with the invariants, the run's cache comes back at
        its fixpoint; so a warm run gives Ex. (C) the pass threads the
        carried state (it replaces the memo M: its K and cache are part
        of it) and B4.4/B4.5 are re-proven over it.
      - (B) done 2026-11-01 (lib/dwarmpf.bend; gate PASS): skinv_pre,
        kspan_pre, kfw, wstart_t, mu_w (DC.wfuel: dfuel with the state's
        records, past μ of every state, no pigeonhole needed), warm_ex,
        frun_fo (CacheOk now covers fixpoints), run_inv (Step reports K's
        span at a fixpoint), and the context step: DC.sameopen, open_tr (a
        non-segment's direction is 0, collapsed anywhere), tinv_ctx.
      - Measured before (C), the warm pass as separate functions
        (dpass.bend pass2.w, unproven, a throwaway probe): instructions
        base 4.85 G (memo 3.09 G) -> 1.50 G, oncircle-pairs 48.8 G (35.3 G)
        -> 10.3 G, vertical-twice 79.1 G (56.9 G) -> 16.2 G; outputs
        byte-identical to today's, the amber drop's nd included.
      - (C) plan: WOk/WInv (the state for some P agreeing with rfacts(kb),
        in the context it carries), wk_at_ok, wcall_ex, wnext_ok; the warm
        and the cold refutation decisions are the same Bool (both exact:
        ro_eq), so the conflict branch's proof stands; dcwpf and dpasspf
        thread the state and its invariant (their macros $WP, $O2,
        $PARGS); then pass2.w becomes pass2 and the memo pass goes.
      - *Found 2026-11-01: carrying the forest blows up angle-lines*
        (2139 G against 124.5 G; outputs still identical). A round looks
        for K facts before merges, so a cold run finds them at unmerged
        single-node roots; a warm start brings the forest merged, so the
        same K facts are first found at merged roots, as much bigger
        polynomials (constraint 2: K rows 318 bits cold, 2531 warm; K's
        row order is not the cause: facts-first K changes nothing).
        Carrying K alone (forest reset) avoids it but gains little (base
        2.88 G, vertical-twice 46.7 G, angle-lines 117 G).
      - *The fix: two phases* (measured, unproven, then reverted): phase 1
        runs from the carried K with the new facts and the forest unmerged,
        taking only the rounds that add to K (it pauses where a round would
        merge or link); phase 2 continues from phase 1's K with the carried
        forest. K facts are found as a cold run finds them, the merges are
        not redone. Instructions: base 1.85 G, oncircle-pairs 12.1 G,
        vertical-twice 18.9 G, angle-lines 46.9 G (2.6x to 4.2x over the
        original on every sketch), outputs byte-identical. Proof: any
        state with the invariants is a start, so phase 2's start (phase
        1's K, the carried records and links) needs only a mix lemma; phase
        1's rounds are the round's own until the pause (the fast round's
        equalities, dfastpf), and need no completeness or termination.
        dwarmpf's lemmas carry over (wstart's K part, skinv_pre, kfw,
        kspan_pre, tinv_ctx, warm_ex, frun_fo, run_inv); the walk's draft
        changes are kept aside (scratchpad) until dpasspf is threaded.
      - *(C) done 2026-11-01* (gate PASS, tools/regress.sh PASS). The
        two-phase call is lib/dclose.bend's wcall (fround.k, frun.k, ph2;
        phase 1 ends at its pause or its fuel's end, and either way phase
        2 runs from its K). Proven in lib/dwarmpf.bend: phase 1 keeps the
        run's invariants and the cache, an explosion its own (KI: each of
        its stages is the round's stage or the pause, kr.*; krun); mix
        (one state's K with another's records and links); phase 1 starts
        from mix(the warm K, sk0); wcall_ex and wnext_ok keep their
        statements. lib/dpass.bend is the warm pass (classes2 and
        final2_st run it; the memo pass and the cold walk are gone, with
        their equalities in lib/dpassmpf.bend, dmemopf's dclose_m_eq and
        dconflict's .m forms). lib/dpasspf.bend proves DH.Honest(sk,
        classes2(sk)) over it directly: hon carries W, a ghost context
        and WInv for rfacts(kb); at a driving constraint W is taken to
        c's context (wk_at_ok), c's call gives Ex (wcall_ex), so the warm
        refutation decision is the cold one (ro_eq), the walk is
        cw2_final with W, and the next W keeps WInv (wn_ok: c joins kb
        exactly when not red, one2_kb; rfacts(kb ++ [c]) = rfacts(c :
        kb), facts_snoc). tests/dir_draft.bend's walk statement now takes
        W and its WInv; pass2_honest's statement is unchanged.
        Instructions (native, one thread, the closure pass): base 4.85 G
        -> 1.85 G, oncircle-pairs 48.8 G -> 12.1 G, vertical-twice 79.1 G
        -> 18.9 G, angle-lines 124.6 G -> 46.9 G; outputs byte-identical
        to the cold pass on all four.
    - The other sketches' time is elsewhere (base's profile: the runtime
      freeing terms, Pos arithmetic, monomial compares; a simplex in the
      refutation decision runs about 213k steps on base).
  - *Later, if still too slow*: the found item's full hull from a cached
    full khull per root (filled lazily); smaller numbers (content
    removal in the lean residuals, proven up to positive scaling);
    warm-starting a constraint's run from the previous fixpoint when the
    context collapses nothing new (a start state for dclose, so the
    interface gains a parameter and B4's uses change: only with
    Danielle's agreement).

### B5. The verdict and soundness
- `VD.exact` checks only the amber sides (B4.6: no drop check). The nd
  sides are checked over the box by `check_sides`, for Kept and Amber
  drops.
- `solve_exists`, `solve_unique`, `solve_pins`, `solve_regular` and
  `solve_blame` re-proven.
- `fast_solve`: the generic `final` gains the nd sides. The fast solver's
  proof is generic, so this is a substitution.

**As planned 2026-11-01** (read before building; Danielle: go ahead).
`VD.exact` already checks only the amber sides (B4.6). Re-prove, then
switch: a draft solver runs the new pass beside sk-13a's, and the laws are
proven for it, the gate green throughout. At the switch it replaces
lib/solve.bend, and these proofs replace the old ones.
- **B5.1 The new pass's structure.** lib/dpass.bend gains `solved_pos2`,
  `pins2` and `skel2`, read off `final2_st` exactly as lib/pass.bend's
  are off `final_st`.
- **B5.2 The draft solver** (lib/dsolve.bend). sk-13a's search and
  answer over the new pass's classes, pins, structure and system solved.
  Its verdict is `final2 = ndok ∧ SO.final`. `ndok` checks |s|² > 0 over
  the box (`PL.check_sides` on `DR.ndsides(ents, live_nd(cls))`), for
  every s in the nd of a Kept or Amber drop. The answer type and the
  loop's shape are sk-13a's.
- **B5.3 The verdict laws for it** (lib/dsolvepf.bend). A True ok is a
  True `final2` (the loop lemmas, copied). `final2` gives sk-13a's
  `final`, and solvepf's and regpf's lemmas are stated for any answer
  whose `final` passes, so `solve_pins`, `solve_unique` and
  `solve_regular` follow unchanged.
  - `solve_exists` is the new part. Before, every drop was degree 0
    (`dck`), so the dropped equations held wherever the solved ones did.
    Now, at the box's point y where the system solved holds:
    1. `ndok` makes every live drop's nd segments long at y;
    2. so `facts_hold` gives every Kept constraint's dropped equations
       at y, and with the box's sides, y means the sketch less its red
       and amber constraints;
    3. `amber_law` (B6) then gives the sketch less its red ones.
    The Honest is `pass2_honest`, called once per use.
  - `solve_blame`: the support is not red, read off the draft Honest's
    ConflictOk (as blamepf's, over DH's Fate), then blamepf's `mo`.
  - `solve_honest`, `solve_drop`, `solve_amber` and `solve_conflict` at
    the solver level, from `pass2_honest` and the B6 laws.
- **B5.4 `solve_total` for the new pass**: the pins distinct and below
  nvars, the system solved perfectly matched onto the free variables
  (perfpf's `total_pass` over `final2_st`), and the marked sketch well
  formed.
- **B5.5 `fast_solve`**: the word solver over the new pass with the same
  `final2`, equal to the draft solver (fastpf's proof is generic in the
  numbers, so this is the same proof over the new verdict).
- Each restated over the draft solver in tests/dir_draft.bend. The
  solver-level texts in tools/drafts/roadmap13b.draft are unchanged.

**As built 2026-11-01: B5 done.**
- B5.1–B5.3 @9eb40bb: lib/dpass.bend's structure, lib/dsolve.bend, and
  lib/dsolvepf.bend (`solve_exists2`, `solve_unique2`, `solve_pins2`,
  `solve_regular2`, `solve_blame2`, and `solve_honest2`, `solve_drop2`,
  `solve_amber2`, `solve_conflict2`), restated in tests/dsolve_laws.bend
  (not dir_draft, which is already the slowest root). Existence went as
  planned; `pass2_honest` is called twice, since the Honest is single-use.
- B5.4: lib/dpasspf.bend's `final2_inv` (the honest walk again over
  `pass2_st`, keeping the state invariant), and lib/dtotalpf.bend:
  perfpf's last part over the new pass's end state (the rest of perfpf
  reused), and `solve_total2`.
- B5.5: lib/dwfast.bend (the fast solver over the new pass, `final2` in
  K, the pass run once by `walk22`) and lib/dwfastpf.bend (`solve_l2_eq`,
  fastpf's proof with the nd check through the map by `check_sides_h`),
  checked at the CLI's base in tests/dwfast_laws.bend.
- At the switch, dsolve/dwfast replace solve/fast, the d-proofs replace
  the old ones, and the restatements become ROADMAP's.

### B6. Corollaries and uniqueness
- `solve_drop`, `solve_amber` and `solve_conflict` with nd.
- `honest_unique` re-proven with the extended cases.
- *solve_drop's content proven 2026-11-01 (gate PASS)*, over any
  classification with the draft's Honest (tests/dir_draft.bend b6_drop,
  replacing stmt_drop). lib/dfactpf.bend `facts_hold`: wherever the
  system solved holds, every fact of a kept constraint holds (KF(c), the
  facts of the kept constraints before c, by induction along the
  constraints; each step reads one Fate, its drops' reasons turned into
  facts at x: a degree-0 reason's combination is of solved equations,
  `ident_all`; a direction reason's facts are KF(c)'s and c's own solved
  equations, `sound`, and Proves). A direction constraint's statement
  holds exactly where its one equation does (`stat_r`, `eq_r`, through
  `at`: an equation's position is one of its owner's constraint's
  equations). `drop_law` reads fact j out of KF(the end). The Honest is
  read once for `downs` first (the hreadpf pattern). dpassmpf's `split`
  is now general in the classes and nd (rfacts_split unchanged).
  facts_hold is what solve_amber and solve_conflict will read too.
- *solve_amber's content proven 2026-11-01 (gate PASS)*, over any
  classification with the draft's Honest (tests/dir_draft.bend b6_amber,
  replacing stmt_amber): lib/dambpf.bend `amber_law`. The ambers drop all
  their equations (read once, ap_rb, amberlawpf's allP), so the system
  solved holds at a geometry meaning the sketch less its reds and ambers;
  facts_hold then gives the ambers' equations where amber_nd is long
  (pz2), and their sides come from their Implied refutations along the
  order (vsdpf's record walk, the ambers' Fates' sides parts handed on by
  facts_hold). For this the draft Honest's AmberOk now holds one Implied
  per side (DH.AllImplied, @298e5f9): Bend applies a function hypothesis
  only once (closures are affine), and a LineDistance has two sides.
- *solve_conflict's content proven 2026-11-01*, over any classification
  with the draft's Honest (tests/dir_draft.bend b6_conflict, replacing
  stmt_conflict, without the unused wf and cover hypotheses):
  lib/dcflawpf.bend `conflict_law`. A degree-0 refutation goes through
  conflawpf's cf_m. For a direction refutation, at a geometry meaning the
  sketch with only c and its support: rfacts (no nd) hold, from the
  equations and `stat_at`; the refutation's nd is within the conflict's
  nd and the Angles' segments, which the Angles' sides make long (dot > 0
  is 0 when a segment collapses: `dot0_a`, `dot0_b`, `sumsq_zero`). Then
  each kind has no point there: Motzkin by `sound` on each K fact and
  vsdpf's refute_at; a collapse makes a long segment's squared length 0;
  an Angle's collapse makes its own side's dot 0 (its sides read out of
  csides by position, `sides_of`, the constraint driving). It doesn't use
  facts_hold: a conflict's facts are its own and its support's
  equations, which hold at x.
- *honest_unique proven over the draft Honest 2026-11-01*
  (tests/dir_draft.bend b6_honest_unique, replacing stmt_honest_unique,
  without the unused wf hypothesis): lib/duniqpf.bend `honest_unique2`.
  uniqpf's walk is reused wherever it reads only the classes; the Fates'
  cases are redone:
  - drops of both layers agree (lib/dagreepf.bend `drops_ag2`, agreepf's
    walk along c's equations). A direction drop in one and none in the
    other cannot meet: the facts it may read are the same in both once
    nd is erased (`df_ag`: the kept constraints' facts differ only in
    their drops' nd; c's own are its undropped equations with its
    statement, `of_or`), and a derivation never reads a fact's nd
    (lib/dstrippf.bend `ctr`, `vtr`, dmappf's cmap/vmap with the
    identity renumbering). So two classifications that record different
    reasons for a drop still agree on every later drop;
  - a conflict's refutation against NoRefute2: degree 0 through
    nrconfpf's cn.m, by directions through dmappf's nodir_mono (the
    support is among the kept constraints before c);
  - an amber's sides: `ai_at` reads one Implied out of DH.AllImplied.
  With this, B6 is done: every B6 law is proven over the draft Honest.

### B7. `solve_complete` and `solve_refused`
- No drop certificate to pass any more (B4.6: drops are correct by
  construction); the amber sides' refutations pass as in sk-13a. The nd
  sides hold over a small enough box, from `Strict` at x*, like the
  other sides.

**As built 2026-11-01: B7 done** (for the draft solver, as roadmap13b
states the two laws; restated in tests/dcomplete_laws.bend, its own gate
root).
- The new pass's classes pass the exact check: lib/dpasspf.bend
  `ck2_pass` (the walk again, each driving class a conflict, an over, or
  PA.one.k, whose refutations pass by ckpf's `kam_onek` over the kept list
  the invariant names).
- lib/dskdpf.bend: skdpf over the new pass's end state (each lemma also
  takes the wf and cover facts, which `final2_inv` needs);
  lib/dtotalpf.bend gains `vend_pass2`.
- lib/dcompletepf.bend: completepf redirected to the draft solver. The
  proof runs on sk-13a's sides followed by the nd sides (one budget for
  both, `strict_cat`; the nd sides have no constants, `dys_nd`), and the
  side check on that list splits into the two final2 reads (`cs_l`,
  `cs_r`). `solve_complete2` takes hn (the nd sides strict at x).
- lib/drefusedpf.bend: `solve_refused2`, refusedpf's over the draft solver.

**Switch readiness, measured 2026-11-01** (a throwaway CLI on
`DWF.wsolve2`, every sketch in proto/sketches/expected, both CLIs side by
side, 4 at a time, load average 12–34, so times are rough):
- 19 of 21 answers are sk-13a's exactly.
- vertical-twice and vertical-twice.raw change, as intended: sk-13a
  refuses them (Over, red 32 / 34, ok False); the new pass drops the
  repeated vertical's equation by directions, so it is amber (A/30,
  A/32) and the sketch certifies (ok True). The expected file's comment
  already said "stays refused until sk-13b".
- Every sketch is within its limit. Slowest: angle-lines 7.8 s (sk-13a
  1.6 s, limit 60); oncircle-pairs 1.5 s (0.3 s); the rest under 3 s.
- So the switch would update those two expected lines, and nothing else
  in the regression.

**Before the switch, read 2026-11-02 (Danielle: make nd exact).** The
spec bounded nd only from above: free at degree 0, and the derivation's
or refutation's nd within the recorded one. Padding would weaken every
law by the extra segments, make the verdict check sides for nothing, and
put false "unless" segments on the page. Now (spec/_draft13b.bend, and
spec/solve.bend's DirRefutes, which only the draft reads):
- a degree-0 drop or conflict has nd Nil;
- a direction drop's nd is its derivation's nd;
- a direction conflict's nd is within its refutation's nd, which is
  within nd and the Angles' segments.
The solver already recorded exactly these (dconflictpf `nc_in`: the
cleaned list keeps only the refutation's segments). Read and found fine:
ctx only blocks steps through collapsed segments, never a premise; the
basis and the facts read only driving, non-red constraints before c; a
derivation's nd includes its facts' own, so solve_drop's covers a chain
of drops; nd sides are Gt0, never exempt at pins. Intended, worth
knowing: a direction conflict means no drawing with its nd long (∥ and ⊥
on one pair is red, unless a segment collapses), while a collapse by
plain equations stays green (Vertical and Horizontal on one segment), as
in sk-13a.

**As built 2026-11-02: the switch.** One commit, after the nd change
above and a rename (the sk-13a verdict `final` is now `checks`, so that
`final` is the whole verdict, `ndok` then `checks`, as ROADMAP names it):
- spec/solve.bend's Honest is sk-13b's (spec/_draft13b.bend's, which is
  gone); its header says what it now covers.
- lib/solve.bend and lib/fast.bend run the new pass and verdict
  (lib/dsolve.bend and lib/dwfast.bend merged in and gone).
- ROADMAP.bend: the five laws as tools/drafts/roadmap13b.draft had them
  (that draft is gone), DR imported, the comments naming files and
  classes updated; honest_unique's comment adds the drops' reasons and nd
  to what may differ. lawsync: all 14 in sync; stmtcheck: none open.
- tests: solve_laws.bend restates the laws with the new proofs,
  complete_laws.bend (was dcomplete_laws) and fast_laws.bend the others;
  dir_draft.bend is dir_laws.bend, without its statement-only checks;
  dsolve_laws, dwfast_laws and pass_laws are gone; struct_laws and
  binv_laws read lib/dskdpf.bend; refute_laws lost sk-13a's conflict_ok
  (dir_laws has the new one); solve_demo reads lib/dsolvepf.bend.
- The sk-13a proofs of the laws are gone: every def that read the old
  Honest or the old solver's loop, found by a def-level reference walk
  and confirmed by the checker. lib/droplawpf.bend and lib/totalpf.bend
  are gone; the other old files keep what the new proofs reuse, each with
  a note saying where its law is proven now.
- Regression: only vertical-twice and vertical-twice.raw changed (A/30,
  A/32, ok True); REGRESS: PASS.
- Left as it is: the proof files keep their d names (dsolvepf, ...) and
  their lemmas' 2 suffixes (solve_l2_eq, ...); lib/pass.bend's sk-13a
  walk stays (lib/dpass.bend reuses its parts, and the protos call it).

### B8. The page, the CLI and the regression
- The CLI prints nd with drops and conflicts; serve.py parses it.
- The page:
  - "conflicts with #66, unless seg93 or seg95 has length 0";
  - an amber or partly implied constraint says what it assumes when nd
    is not empty.
  - The GUI sends angles as rational rotations. An Angle cycle that looks
    exact (a triangle's three angles) has a product that is not real, so
    it is honestly red. The page says the rotation was rounded.
- The regression:
  - sketch(4) and slowsketches 8 and 9 join it;
  - the audit's sketches A, B and V;
  - small sketches: four right angles; a chain of parallels closed; ∥
    with ⊥ on one pair; Horizontal then Vertical across a ∥; OnLine
    twice then a Parallel; a Coincident collapsing a segment, *then* a
    Parallel on it (amber, vacuous; in the other order it stays refused,
    decision 4); an Angle cycle (kept, its equation dropped).
  - `expected` is updated where answers change, and only there.

**As built 2026-11-02: B8, without slowsketches 8 and 9.**
- gui/solve_cli.bend prints each drop as its equation and its nd
  (`A/30:31:24:23:4`), a conflict's nd after its support (`C/0/5,2`),
  each segment once (nd lists one per use; the meaning is the same), and
  a `why` line: each drop's reason, L and the equations of its constant
  combination (nonzero multipliers only), or D and the equations its
  derivation's premises are (the facts' positions mapped back as
  SV.dfacts picks them). serve.py parses both.
- The page: "conflicts with #1, unless L2 or L5 has length 0";
  "redundant where L4 and L5 have nonzero length, holds anyway" (and
  "partly implied ... where"); the hover names the constraints a dropped
  equation follows from, "by directions" for a derivation, and that the
  certified drawing has the nd segments nonzero; a conflict involving an
  Angle that is not a multiple of 90 degrees says its rotation was
  rounded.
- Regression: proto/sketches/b8.mjs makes the small sketches and the
  audit's A, B and V; every answer is as planned (A amber with nd
  {h, s1}, B amber with nd {h, s1}, V red, unless h has length 0). `expected` changed
  only at vertical-twice and its raw input, by their nd. REGRESS: PASS.
- Found:
  - nd is sound but not minimal: the closure's derivations pass through
    each component's root, so A's nd is {h, s1} where {s1} suffices, and
    four right angles name all four sides where two suffice. Shortening
    them changes proven derivations; not done here.
  - h-par-v and audit-v are red and not certified: the page relaxes the
    drawing toward the red constraints too, and a red merge (h-par-v's
    Vertical) holds in the drawing itself. Relaxing again without the red
    constraints certifies audit-v; h-par-v needs the merge classes to
    leave the red one out, a change to the page's model.
- Not done: slowsketches 6 to 9 are not on disk any more (the directory
  is gone), so 8 and 9 are not in the regression and the pass's cost on
  6 and 7 is not measured; they need exporting again.

### B8b. Irreducible nd (added 2026-11-02, before B9)
Danielle asked for nd to be minimal, covering every case however rare.
Today nd is exact for the derivation the closure returns, but that
derivation goes through each component's root and the segment's own
record, so it can name segments no derivation needs (B8: the audit's
sketch A gets {h, s1} where {s1} suffices; four right angles name all
four sides where two suffice). This matters in two ways:
- **Certification.** The verdict proves every live drop's nd nonzero over
  the box. A segment that is zero at the solution but not needed would
  refuse a sketch that a shorter derivation certifies. No realistic case
  is known (the ways found to make such a segment zero make the system
  singular anyway), but none is ruled out.
- **The message.** "unless L12 has length 0" suggests collapsing L12 is a
  way out when the proof never needed it.

**The promise: irreducible, not fewest.** For each segment of a drop's or
a conflict's nd, no derivation (refutation) exists whose nd avoids it,
the way a conflict's support is irreducible. The fewest segments is a
sparsest-combination problem (NP-hard in general); when two different
sets each suffice, the solver reports one, and the other may be smaller.

#### The trusted part (spec/solve.bend)

```
# no derivation of c's equation i needs only segments among A
def NotDirDerivableIn(+sk, +cls, +red, +c, +d, +i, +A) -> Type:
  @dv: DR.Der -> DR.Valid(ents(sk), dfacts(sk, cls, red, c, d, i), ctx(sk, red, c), dv)
    -> Proves(ents(sk), dstat_of(ents(sk), kind_at(sk, c)), eqat(SK.Sketch.eqs(sk), i), DR.concl(ents(sk), dfacts(sk, cls, red, c, d, i), dv))
    -> {sub(DR.nd(ents(sk), dfacts(sk, cls, red, c, d, i), dv), A) == True{} : Bool} -> Empty

# each segment of nd is needed
def NdIrred(+sk, +cls, +red, +c, +d, +i, +nd) -> Type:
  @m: Nat -> {mem(m, nd) == True{} : Bool} -> NotDirDerivableIn(sk, cls, red, c, d, i, unmark(m, nd))

# no refutation of c with cs needs only segments among A
def NoDirRefIn(+sk, +c, +cs, +cx, +A) -> Type:
  @r: DR.DRef -> RefOk(sk, c, cs, cx, r)
    -> {sub(DR.ref.nd(ents(sk), rfacts(sk, Con{c, cs}), r), A) == True{} : Bool} -> Empty
```

- why_ok's WDer case gains `NdIrred(sk, cls, red, c, d, j, nd)`. WLin is
  unchanged (nd is Nil).
- DirRefutes gains: nd has no segment of an Angle among c and cs (those
  are free already; lib/dconflict.bend's ndclean leaves them out today),
  and for each m in nd,
  `NoDirRefIn(sk, c, cs, cx, cat(unmark(m, nd), angle_args(sk, Con{c, cs})))`.
  The degree-0 branch is unchanged (nd is Nil).
- A degree-0 reason is a direction derivation with nd Nil (DKAdd over
  solved equations), and a degree-0 refutation a Motzkin one with ref.nd
  Nil, so the new clauses also rule out a direction answer where a
  degree-0 one exists, with no separate statement.
- The laws read Honest, so no law statement changes; honest_unique's
  comment (nd may differ) stays true. ROADMAP's and the page's wording of
  nd can say "each one needed".

#### How the solver gets there: a deletion loop
For a drop with derivation dv and N = nd(dv): for each m of N in turn,
look for a derivation whose nd lies in N less m; if there is one, it
replaces dv and N shrinks. One pass suffices: a segment kept against a
larger N is still needed against the final one (sub is monotone). The
same for a conflict's refutation, with the Angles' segments always
allowed.

"Look for a derivation whose nd lies in A" is the closure run for a
**restricted calculus**: a node may be passed through (DThrough, DLine,
RColl) only if it is open and in A, and a fact may be used only if its
nd lies in A. Every other segment is endpoint-only: judgments can end
at it, nothing passes through it. That is how the closure already treats
collapsed segments (links, their sets, RFull when the direction is in K
squared). Where the closure's proofs read a non-open segment's collapse,
they use only that it is not Open (dcreprpf's coll_g, drefpf's iso_of),
which a forbidden segment gives too. One difference: an open segment
whose direction is in K squared is an explosion today, by passing
through it; a forbidden one is not (its set is full, as a collapsed
one's).

#### Order of work
- **C0. Spec draft.** The clauses above in spec/_draft13c.bend, with a
  test that type-checks them against today's answers' shapes. Danielle
  reads it before anything is proven against it.
- **C1. The restricted calculus in lib.** ValidA (Open replaced by open
  and in A); the facts with those whose nd is not in A replaced by
  placeholders (equation 0, nd Nil, no statement), so positions do not
  move. Bridging both ways: a Valid derivation with nd in A is ValidA
  over the placeholder facts with the same conclusion; a ValidA one is
  Valid with nd in A once placeholder premises become DZero. With A
  every segment, ValidA is Valid.
- **C2. The closure, restricted.** Decision first, after reading the run
  and its proofs: thread A through the closure and its proofs (today's
  closure is A = every segment, one closure to keep), or a parallel copy
  (today's proofs untouched, two closures). Recommendation: thread A,
  because the unrestricted run is literally the instance A = all and two
  closures would drift; the threading is mechanical (the open test gains
  mem(s, A), Open becomes Open_A in the closure theorem and the
  refutation decision). Both the reference run and the fast incremental
  one, so the loop's runs are fast.
- **C3. The loop in lib/dpass.bend,** for drops (after the closure finds
  the drop) and conflicts (after the support is irreducible).
  Optionally, a derivation simplifier first (cut a pass through b whose
  other premise is a real multiple of z_b, and the final pass through
  the root): it shortens N before the loop, so fewer runs; only if the
  cost asks for it.
- **C4. Proofs.** dcwpf: the drop's NdIrred from each run's "not held"
  by the restricted closure theorem and the bridging. dconflictpf: the
  same for conflicts. The rest of the pass's proofs see a Drop with a
  shorter nd and an extra clause.
- **C5. Switch,** as sk-13b's: the draft becomes Honest, the proofs move,
  the gate and the regression. `expected` changes where nd shrinks
  (vertical-twice, right-angles, parallels-closed, audit-a, angle-cycle;
  B8's sketches show which). Cost measured: one restricted run per
  segment of each direction drop's and conflict's nd.

**Exit:** Honest with NdIrred and the conflict clause, proven; the gate
and the regression green; audit-a's nd {s1}, right-angles' two sides,
parallels-closed's middle segment; the cost on vertical-twice and the
slow sketches Danielle exports next.

**Risks:**
- The threading in C2 touches most of the closure's proof files. It is
  mechanical, but large; a copy would be as large.
- A proof that reads more of a non-open segment than "not Open" (none
  found beyond coll_g and iso_of; C2 starts by confirming it).
- Cost: the loop multiplies the closure's runs by the size of nd.
- The explosion rule differs under restriction (above): the void check
  covers only segments in A.

### B9. Audit and sign-off
- An independent audit of the proven statements against this file. Gate
  and regression green. Danielle signs off.

**Exit:** the laws proven as restated; sketches 4, 8 and 9 and the new
ones as above; no other answer in the regression changes. The pass's
added cost is measured on sketches 6 and 7 (instruction counts). The
target is a few percent of the whole solve; if it is more, it gets looked
at before B9.

## Risks

- **B3's completeness proof**: "the final state is closed under every
  rule" over hulls (vector spaces of complex residuals) is the largest
  new proof. It builds on lib/indpf.bend and the echelon form.
- **The derivation type (B0/B1)**: an inductive type of derivations with
  nd in Bend; certificates by structural recursion over it.
- **Certificate degree**: it grows with nesting (∥-through within
  ∥-through). Measured on sketches 6 and 7; the normalizer checks each
  identity, so this is a cost, not a correctness risk.
- **`solve_complete` (B7)**: the C1–C6 proofs gain the nd sides; it
  should be a substitution, like sk-13a's S7.
- **Two spans (B2)**: the solved basis (for degree-0 drops) and the
  premises with derived rows (for the closure). They agree until the
  first direction drop.
- **Scope**: larger than v1, several sessions. Commit at each step with
  the gate green; check in after B0 and after B4.
