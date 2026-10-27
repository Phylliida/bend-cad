# Plan: sk-13b, the direction layer (v2, 2026-10-26, for review)

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
- Nondegeneracy: `Long(x, s)`, s's endpoints differ at x (spec/geom.bend's
  `ne`). nd is a list of segments, and a segment may repeat (the
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
| K-lin | K(e₁), K(e₂), rationals λ₁, λ₂ | K(λ₁e₁ + λ₂e₂) | |
| ∥-premise | a direction statement cross(z_a, x) in P | ∥(a, x) | its own |
| ∥-self | | ∥(a, z_a) | |
| ∥-lin | ∥(a, x₁), ∥(a, x₂), rationals μ₁, μ₂ | ∥(a, μ₁x₁ + μ₂x₂) | |
| ∥-known | ∥(a, x), K(Re ℓ), K(Im ℓ) | ∥(a, x + ℓ) | |
| ∥-turn | ∥(a, conj(g)·z_b), b a segment | ∥(b, g·z_a) | |
| ∥-through | ∥(a, conj(g)·z_b), ∥(b, x), b a segment not collapsed | ∥(a, conj(g)·x) | b |
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
- Each rule's identity as `Ident`, by the ring normalizer on atoms.
- A derivation gives a certificate: Π_{nd}|s|²·e ≡ Σ q·g over P's
  equations, by induction on the derivation. Composed with dropped
  premises' certificates, it lands on solved equations only. That is
  well founded, since every fact refers to earlier positions.
- Semantics: wherever the solved equations hold and nd is nonzero, a
  derived e vanishes, in every ordered field.

### B2. The linear layer, extended (K)
- Rows for P's equations (the basis's rows, plus the dropped ones' until
  the first direction drop changes the span), and rows for derived
  linear forms, each with its nd.
- Residuals of every segment's direction parts, kept up to date as rows
  are added. Each residual is divided by its recorded scale before
  complex comparisons (the audit: the scales of x and y parts differ).
- Proven: K(e) holds iff e's residual is 0 (lib/indpf.bend's result,
  extended to the derived rows).

### B3. Components and hulls (∥)
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
