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
- **B4.3, refutability and the filter generalized** (lib/dconflict.bend).
  refutable2(c, cs) is sk-13a's degree-0 test, else the closure of
  rfacts(c:cs) in c's context with dref. Chinneck's filter runs it over
  every kept constraint, as sk-13a's does. A seed (only the constraints
  behind the refutation's facts) would need its own refutation proven by
  moving the derivation to a sublist of facts; it is left as a measured
  optimization. The conflict's nd: Nil when c with s refutes at degree
  0; else the refutation's nd, without the Angles' segments, each segment
  once. Proven: ConflictOk, the irreducibility by B4.1 and dref_complete.
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
- **B4.5, the pass** (lib/dpass.bend): one constraint is the degree-0
  test, else the direction refutation, then the conflict (B4.3), else the
  walk, then Over, Kept and Amber as now. The state is sk-13a's plus the
  classes so far. The closure is rerun from the facts for each test;
  "the tentative closure becomes the premises'" is an optimization to
  measure, not needed. Proven: the draft's Honest for it
  (lib/dpasspf.bend), with sk-13a's PInv and its generic lemmas.
- **B4.6, the certificates** (exec; their proof is B7's): a derivation's
  identity, composed with the dropped facts' certificates, over solved
  equations, with h = ndh(nd).
- **B4.7, a run**: sketches 4, 8 and 9 and proto/dclose_run's eleven,
  with the cost measured.
- The global theorem is not needed by Honest; it is taken up where a law
  needs it (B6).

### B5. The verdict and soundness
- `VD.exact` with h from nd. The nd sides are checked over the box by
  `check_sides`, for Kept and Amber drops.
- `solve_exists`, `solve_unique`, `solve_pins`, `solve_regular` and
  `solve_blame` re-proven.
- `fast_solve`: the generic `final` gains the nd sides. The fast solver's
  proof is generic, so this is a substitution.

### B6. Corollaries and uniqueness
- `solve_drop`, `solve_amber` and `solve_conflict` with nd.
- `honest_unique` re-proven with the extended cases.

### B7. `solve_complete` and `solve_refused`
- The pass's certificates pass the verdict (B1). The nd sides hold over a
  small enough box, from `Strict` at x*, like the other sides.

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
