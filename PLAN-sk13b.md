# Plan: sk-13b, the direction layer (v1, 2026-10-26, for review)

This is PLAN-sk13.md's Phase 2 (DESIGN §8.11, "Directions"), worked out
against sk-13a as built. It has two halves: the trusted part (what the
answer means: the calculus, `Honest`, the classes, the laws), and the
order of work. Danielle asked for it on 2026-10-26 after slowsketches 8
and 9 ("the correct, proper way").

## Why

Today's layer sees only constant combinations (degree 0). Dependencies
among Parallel, Perpendicular and Angle need polynomial multipliers, so
the solver keeps every such constraint. The block is then singular at
every solution, Newton fails at all seven precisions, and the page says
"Not certified" with nothing red.
- sketch(4) (vertical-twice): seg 28 is made vertical twice, through #25
  ⊥, #27 ∥ and #38 ∥. Refused.
- slowsketches 8 and 9: #66 makes seg93 ∥ seg95 and #67 makes them ⊥.
  Refused after 54 s and 132 s. Dropping either one certifies in a few
  seconds.

## What sk-13b delivers

**The solver**, in the same single pass, also reasons about directions:
- **Implied**: an equation that a chain of directions implies is dropped,
  with a certificate. A constraint whose equations are all dropped is
  amber, as today.
- **Conflict**: a constraint that closes a cycle of directions that cannot
  hold is red. Its support is irreducible, as today.
- **Nondegeneracy is explicit.** Collapsed segments satisfy every
  direction relation (Q15), so each direction judgment names the segments
  it needs to have nonzero length. The verdict proves those lengths are
  nonzero over the certified box (ball arithmetic, like side conditions,
  §8.6).

**For your sketches:**
- slowsketches 8 and 9: #67 is red, "conflicts with #66, unless seg93 or
  seg95 has length 0", and the rest certifies, in about the time it takes
  without #67.
- sketch(4): #38 is amber ("redundant, holds anyway"), and it certifies.
- A rectangle with a fourth right angle, or a chain of parallels closed
  again, comes out amber. A Horizontal on a segment already parallel to a
  horizontal one comes out amber too. A Vertical there is red.

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
   - The vocabulary is one notion: *segment s has nonzero length*
     (its endpoints differ). The solver never picks a polynomial.
   - A conflict becomes: c and its support cannot all hold at any geometry
     where the named segments have nonzero length. An implied equation
     holds wherever the solved ones hold and the named segments have
     nonzero length.
   - Recommended: yes.
2. **The family: direction constraints over what the linear layer knows**
   (below). OnLine, Symmetric and Angle's orientation are not in it.
   - OnLine relates a segment to a point, not to another segment's
     direction.
   - Orientation ("this angle, not its opposite") is a sign question:
     sk-13s's layers.
   - Recommended: as stated.
3. **The layer reads all the kept constraints' equations, amber ones
   included, not only the system solved.**
   - Reading only the solved system breaks the calculus. A segment that
     the kept constraints force to length 0 can still look nonzero to the
     solved system (some equation that collapses it was dropped). A false
     cycle then stays in the graph, and every later constraint would be
     red.
   - Reading the premises keeps the graph consistent by construction:
     each kept constraint was checked against exactly that graph.
   - The cost: certificates compose. An edge that comes from a dropped
     equation brings that equation's certificate and its nondegeneracy
     along. Degree-0 drops still read the system solved, as in sk-13a.
   - Recommended: as stated.
4. **One limit of the order rule.** A judgment is made from the
   constraints before it.
   - Suppose a later constraint forces an interior segment of an earlier
     drop's chain to length 0 (merging its endpoints, say). That drop's
     nondegeneracy then fails at every solution, so the verdict refuses.
   - The laws stay true (law 10 asks for the nondegeneracy at the
     solution), but such a sketch is refused, not explained.
   - Rare: it needs a zero-length segment in a chain of directions.
     sk-13e's "every refusal explained" is where it gets a reason.
   - Recommended: accept for sk-13b, and note it in DESIGN.

## The trusted part

### The calculus

Fixed for a constraint c by its **premises** P: the equations of the kept
(not red) driving constraints before c, every one of them (dropped ones
too). Let L be the span of P with rational constants: what the linear
layer knows (degree 0). Every definition below is a function of P (and,
for a drop, of c's own earlier equations).

**Labels.** Gaussian rationals g = c + i·s, g ≠ 0. A label acts on a
direction as the rotation-and-scaling `rot(c, s)` (spec/geom.bend). Two
labels are *alike* when one is a real multiple of the other
(c₁s₂ − s₁c₂ = 0). They are compared as directions of lines, so
orientation is not part of it.

**Nodes.** Segments, plus one frame node F whose direction is (1, 0).

**Facts from L.** Segments a, b; constant u, g ≠ 0:
- *Collapsed(a)*: both components of a's direction are in L.
- *Frame(a, u)*: cross(u, dir a) ∈ L. a has the fixed direction u.
  Horizontal and Vertical are the cases u = 1 and u = i.
- *Tie(a, b, g)*: both components of dir b − g·dir a are in L.

These are exactly the ways linear facts can imply a direction relation.
cross(g·a, b), as a quadratic form in (a, b), has signature (2, 2). Its
2-dimensional totally isotropic subspaces are a = 0; b = 0;
b = λ·g·a for a fixed real λ; and a ∈ ℝu, b ∈ ℝ·g·u. A (linear or
affine) space of directions on which cross(g·a, b) vanishes lies in one
of them, so it gives a collapse, a tie, or two frame facts.

**Edges.** Each is a relation cross(g·dir u, dir v) = 0 between nodes u
and v, neither collapsed:
- *constraint edges*: the equation of a Parallel{a, b} (label 1), a
  Perpendicular{a, b} (label i, since dot(a, b) = −cross(i·a, b)), or an
  Angle with constant (c, s) (label c + is; reversals only flip signs);
- *frame edges*: Frame(a, u) gives F–a with label u;
- *tie edges*: Tie(a, b, g) gives a–b with label g.

**Walks.** A walk from u to v follows edges, forward with g and backward
with conj(g). Its product is the product of the labels, and its *interior*
is the segments it passes through (F needs nothing: |(1, 0)|² = 1).

**The path lemma**, proven once, by induction on the walk:
|b|²·cross(g₁g₂·a, c) = dot(g₁·a, b)·cross(g₂·b, c) + cross(g₁·a, b)·dot(g₂·b, c).
So a walk from u to v with product P gives
Π_{s∈interior} |s|² · cross(P·dir u, dir v) ∈ (the ideal of P's
equations), with polynomial multipliers built step by step.

**Derivations** (for equation e_i of c; Q = c's own earlier equations not
dropped, L' = span(P ∪ Q)):
- **D0**: e_i ∈ L'. Its nondegeneracy is that of the dropped equations
  used (for sk-13a's drops: none).
- **D-rel**: c is a direction constraint relating a and b with label g;
  there is a walk from a to b whose product is alike to g. Its
  nondegeneracy is the walk's interior.
- **D-frame**: for some segment a, constants u and λ ≠ 0,
  e_i − λ·cross(u, dir a) ∈ L', and there is a walk from F to a whose
  product is alike to u. A Horizontal on a segment's endpoints is the
  case u = 1.
- **D-void**: c is a direction constraint relating a and b, and a or b is
  collapsed. Then e_i is a combination of P's equations with polynomial
  multipliers (the other segment's coordinates). It holds wherever they
  do, with no nondegeneracy.

The walk is in the premises' graph, which has no conflicting cycle (a
theorem, below). So the products of all walks between two nodes are
alike, and "is there a walk" is a union–find question.

**Refutations** (for c with a set S of constraints before it): a
degree-0 refutation as today, or a **closed walk with a product not alike
to 1** whose edges come from the equations of S and c (their constraint
edges, and the frame and tie facts of their span).
- The walk may only pass through segments that are not collapsed in the
  *context*, span(P ∪ eqs(c)). So a constraint that merges a segment's
  endpoints removes that segment's edges and refutes nothing.
- Reading collapses from the fixed context, not from S, makes
  refutability monotone in S (more constraints, more edges, the same
  nodes). Chinneck's deletion filter needs that for irreducibility. It
  costs nothing in soundness: the walk's edges are S's and c's alone.
- `NoRefute` is the case S = all of P. Its nondegeneracy is every segment on the walk. The
reason: a closed walk at u with product P gives, by the path lemma,
Π|interior|²·cross(P·dir u, dir u) in the ideal, and
cross(P·dir u, dir u) = −Im(P)·|u|². Im(P) is a nonzero constant, so the
product of the walk's squared lengths is in the ideal: wherever the
equations hold, some segment on the walk has length 0. (At u = F,
|u|² = 1.)

### `Honest`, extended (spec/solve.bend)

The cases stay exclusive, in the same order:
- **Conflict iff refutable**: a degree-0 refutation *or* a direction
  refutation of c with its premises. `ConflictOk` reads "a refutation in
  either"; irreducibility reads "without any one member of s, a
  refutation in neither".
- **Drops**: each equation of c is dropped iff it has a derivation: D0
  over sk-13a's basis (unchanged, h = 1), *or* one of D0, D-rel, D-frame
  or D-void over the premises.
- **Over, Kept, Amber**: unchanged. They read the drops, and `NoRefute`
  now excludes both kinds of refutation.

`honest_unique` keeps its statement. Its induction goes through as
before: before c, the classes agree, so the premises and the basis agree,
so every definition above agrees at c.

New global theorem: **the premises' graph never has a conflicting
cycle.** By induction, each kept constraint had no direction refutation
against exactly the graph that the next constraint reads.

### The answer's shape

- `Drop{j, nd, qs}`: equation j, the segments nd its derivation needs
  nonzero, and multipliers on equations of the system solved, with
  Π_{s∈nd} |s|²·g_j ≡ Σ q_k g_{i_k} as polynomials. sk-13a's drops have
  nd = [] and h = 1, as now.
- `Conflict{s, nd}`: the support, and the segments whose nonzero length
  the refutation needs (nd = [] for degree 0).
- The verdict checks each identity with the ring normalizer (as now,
  with h built from nd). It also checks |s|² > 0 over the box for every s
  in a kept drop's nd, with ball arithmetic.

### The laws

A = `SO.solve_l(sk, g0, l)`, as in SK13A-REVIEW.md.
- **Unchanged statements**: `solve_exists`, `solve_unique`, `solve_pins`,
  `solve_regular`, `solve_blame`, `solve_honest` (its `Honest` extended),
  `honest_unique`, `solve_total`, `fast_solve`. The certified geometry
  still satisfies every constraint not red, because the verdict checks
  the nondegeneracy over the box.
- **`solve_drop`**: wherever the solved equations hold *and every segment
  in that drop's nd has nonzero length*, the dropped equation holds.
- **`solve_amber`**: deleting every amber constraint changes no solution
  *at which the amber drops' nd segments have nonzero length*.
- **`solve_conflict`**: a conflicting constraint and its support cannot
  all hold *at any geometry where its nd segments have nonzero length*.
- **`solve_complete`**: also needs, at the regular solution x*, |s|² > 0
  for every s in a kept drop's nd (a `Strict` side, like the others).
- **`solve_refused`**: if no level certifies, the drawing is not a
  regular solution of the system solved, or some drop's nd segment has
  length 0 there.

"Nonzero length" is stated in spec/geom.bend's terms (`ne` of the
endpoints), over every ordered field.

## Out of scope (later layers)

- **Orientation.** An Angle closing a cycle at θ + 180° has its equation
  implied but its side (dot > 0) failing. That is a sign question:
  sk-13s's layers, and sketch(5) is the same case.
- **OnLine as a direction**, Symmetric, LineDistance: the witness layer
  (sk-13d), or a later extension of the family.
- **Lengths** (EqualLength, Distance, OnCircle): sk-13c.

## Steps

### B0. Statements
- spec/dir.bend (new, trusted): labels, nodes, the facts, edges, walks,
  products, nondegeneracy (`Long(x, s)`: s's endpoints differ).
- spec/solve.bend: `Drop` and `Conflict` with nd, the derivations and
  refutations above, `Honest` extended.
- ROADMAP.bend: the five laws restated; `tools/stmtcheck.py` type-checks
  them.
- One independent audit of the statements (a fresh agent, like sk-13a's).
  It hunts for counterexamples to `honest_unique` and to the semantic
  laws. Then your read, then building. Per the standing rule: one audit,
  not a series. Proving is the stronger audit.

### B1. The geometry, proven once
- The path lemma, and cross(P·a, a) = −Im(P)·|a|², as polynomial
  identities (`Ident`), by the ring normalizer on atoms. Both were
  checked with sympy on 2026-10-26, along with dot(a, b) = −cross(i·a, b).
- Walk → certificate: the multipliers built along a walk, proven to give
  Π|interior|²·cross(P·dir u, dir v) ≡ Σ q·g.
- Ties, frames and collapses → their relation's multipliers.
- Semantics: a certificate with nonzero nd lengths implies its equation,
  in every ordered field. Q15's degenerate cases are exactly what nd
  excludes.

### B2. The linear facts, decided exactly
- Residuals of each segment's direction components against the
  premises' echelon form, kept up to date as rows are added. Each new
  row reduces each residual once; earlier pivots stay 0 because later
  rows are 0 at them.
- Collapsed, Frame and Tie read off the residuals: zero, linearly
  dependent, proportional as complex vectors. Normalize by the first
  nonzero coordinate and group.
- Proven complete: a fact holds iff the residuals say so, using sk-13a's
  "derivable iff residual 0" (lib/elimpf.bend) and the echelon form's
  uniqueness of residuals up to a positive scale.
- The premises' echelon form is the basis's until the first direction
  drop. After that it also has rows for the direction-dropped equations.

### B3. The union–find with labels
- Components as lists of (node, walk to the root). A merge re-walks the
  smaller side, and a collapse rebuilds. Sizes are small (at most a few
  hundred segments), so clarity beats asymptotics.
- Proven:
  - every edge seen lies inside one component;
  - each node's walk to its root has the stored product;
  - any walk stays inside a component, so different roots mean no walk
    (completeness);
  - same root and alike labels give an explicit walk (the witness);
  - same root and unlike labels give a conflicting closed walk.

### B4. The pass
- For each driving c:
  - the degree-0 check (unchanged);
  - the direction refutation on the tentative graph of P ∪ eqs(c),
    giving Conflict with the deletion filter generalized (refutable =
    degree 0 or directions; the cycle's own constraints seed the
    candidates);
  - then each equation's drop by D0 over the basis, else by the direction
    derivations;
  - then structure, Over, Kept, Amber (unchanged).
- If c is kept, the tentative graph becomes the premises' graph.
- Certificates: walks compose with the certificates of the dropped
  equations they use, so every multiplier is on a solved equation.
- Proven: `solve_honest` for the extended `Honest`. The global theorem
  above.

### B5. The verdict and soundness
- `VD.exact` with h from nd; nd sides over the box via `check_sides`.
- `solve_exists`/`unique`/`pins`/`regular`/`blame` re-proven (the drops'
  meaning now goes through the nd check).
- `fast_solve`: the generic `final` gains the nd sides. The fast solver's
  proof is generic, so this is a substitution.

### B6. Corollaries and uniqueness
- `solve_drop`, `solve_amber`, `solve_conflict` with nd.
- `honest_unique` re-proven with the extended cases.

### B7. `solve_complete` and `solve_refused`
- The pass's certificates pass the verdict (B1's identities). The nd
  sides hold over a small enough box (from `Strict` at x*), like the
  other sides.

### B8. The page, the CLI and the regression
- The CLI prints nd with drops and conflicts; serve.py parses it.
- The page:
  - "conflicts with #66, unless seg93 or seg95 has length 0";
  - amber constraints say what they assume when nd is not empty.
- The regression:
  - sketch(4) and slowsketches 8 and 9 join it;
  - new small sketches: four right angles; a chain of parallels closed;
    ∥ with ⊥ on one pair; Horizontal then Vertical across a ∥; a
    Coincident collapsing a segment in a direction (amber, no
    nondegeneracy); an Angle cycle;
  - `expected` is updated where answers change, and only there.

### B9. Audit and sign-off
- An independent audit of the proven statements against this file. Gate
  and regression green. Danielle signs off.

**Exit:** the laws proven as restated; sketches 4, 8 and 9 as above; no
other answer in the regression changes. The pass's added cost is
measured on sketches 6 and 7 (instruction counts). The target is a few
percent of the whole solve; if it is more, it gets looked at before B9.

## Risks

- **B2's completeness**: residual uniqueness up to scale, over the
  fraction-free elimination, is new proof work on top of lib/elimpf.
- **B3**: union–find invariants in Bend, with explicit walks. Moderate.
- **Certificate composition (B4)**: an edge from a dropped equation pulls
  in that equation's certificate. The bookkeeping is long, but each step
  is checked by the normalizer in the verdict anyway.
- **`solve_complete` (B7)**: the C1–C6 proofs gain the nd sides; it
  should be a substitution, like sk-13a's S7.
- **The two echelon forms (B2/B4)**: they share rows until a direction
  drop. If keeping them apart costs too much, the premises' form can be
  built lazily.
- **Scope**: large, several sessions. Commit at each step with the gate
  green; check in after B0 and after B4.
