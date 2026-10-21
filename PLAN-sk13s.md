# Plan: sk-13s, signs and proof layers (v2, 2026-10-21, for Danielle's review)

Signed dimensions, and refusals that are fast and explained: the solver
deepens its proof system only when it has to, and every layer is proven
once for all. Everything the solver does is proven, as in sk-13a: each new
behaviour comes with a law in ROADMAP.bend, restated with its proof in
tests/, and the page stays untrusted shaping only.

v2 replaces v1's "squares in every solve" (Danielle, 2026-10-21: fast,
verified, nothing hacky). v1 slowed every sketch and needed the honesty
laws re-proven for each new layer; v2 costs nothing on sketches that
certify and proves the laws once, for every layer.

## Why

slowsketches sketch(5): a right triangle (Perpendicular at P0) with a
directed Angle of 47° from P3→P0 to P6→P3. As directed it cannot hold:
the drawing has −133° = 47° − 180°, so the Angle's equation (a cross
product) holds and its side condition (dot > 0: the directions agree)
fails. The solver refused, honestly, after trying every precision (about
20 s), and could not say why: the contradiction needs one square, which
sk-13a's refutations do not have.

Danielle wants directed angles past 180° and negative dimensions as
orientation hints, so the meanings stay; the solver has to prove more, and
fast.

Typical CAD solves numerically from the drawing and judges by the
numerics (Jacobian rank with a tolerance, non-convergence, blaming the
newest constraint). It fails fast because nothing is certified. Here a fast
refusal has to be a theorem.

## What sk-13s delivers

- **Signed dimensions.** HDistance and VDistance are signed (q.x − p.x = d
  for any d); LineDistance is signed (d < 0: the other side of the line).
  Distance, Radius and Diameter stay nonnegative. Angles are already
  directed.
- **Proof layers.** Honest, and every law about it, are stated for a layer
  d: refutations at layer d may use extra premises that always hold
  (squares) and extra equations implied by the given ones (multiples).
  Layer 0 is sk-13a's degree-0 system. The laws are proven once, for
  every d.
- **Deepening on refusal.** The solver classifies at layer 0 and
  certifies. Only if that is refused does it reclassify at the next layer
  and try again, up to a last layer. The answer reports its layer, and its
  classification is honest for that layer.
- **Fast, explained refusals.** When the first certified box holds the
  only solution of the solved system near the drawing and a side condition
  fails throughout it, that attempt stops at once, with a proven reason.
  Each failed attempt is fast, and a final refusal says which constraint
  cannot hold near the drawing.
- **Sketch 5:** layer 0 is refused fast; layer 2 has the certificate; the
  Angle is red, "conflicts with #2" (the Perpendicular); the rest
  certifies. Under a second, and no other sketch slows down.
- **The page shows directions:** an arrow on each angle's arc, the sign on
  signed dimensions, the refusal reason, and the layer.

## Ground rules (standing)

- Prove the solver as it runs; no check-and-fallback to ease a proof.
- Verified and complete (D7). All limits proved, not stated: each layer's
  completeness is a law, and so is what a refusal reason means.
- Statements first: every spec change and new law is written down and read
  by Danielle before it is proven; an audit agent looks for loopholes
  (agents only audit; I implement).
- Drafts in `tools/drafts/*.draft`, expanded by `tools/expand.py`.
- The gate is `./check.sh`; the native regression is `tools/regress.sh`.
- Commit freely, each step green. No exact counts in docs.

## The design

### Layers

A layer is a Nat d. Its extensions are spec functions, uniform in d:
- `xsides(d, sk, c)`: side conditions that hold everywhere, for
  refutations about constraint c. At layer 0, none. From layer 2, squares
  `Ge0{q·q}` of a basis over c's variables (the variables its equations
  and sides mention): the degree-2 DSOS basis x_v, x_u ± x_v, x_v ± 1 at
  layer 2, wider bases at higher layers.
- `xeqs(d, sk, c, es)`: equations implied by the premise equations es. At
  layers 0 and 2, es itself; higher layers add multiples m·e of the
  premises by monomials m over c's variables.

The exact families, and the last layer, are settled in U0 from
measurements; the interface is what the proofs use, so a later family
change is one definition and its lemmas.

**The interface** (each a lemma about the definitions, for every d):
- every side of `xsides` holds at every point, in every ordered field
  (q·q ≥ 0);
- every equation of `xeqs(d, sk, c, es)` is 0 wherever es is (each is a
  multiple of one of es);
- `xeqs` grows with es: es a sublist of es' gives `xeqs(es)` a sublist of
  `xeqs(es')` (what the conflict supports and honest_unique's merges
  need);
- `xsides` depends on sk, c and d only, so both classifications in
  honest_unique, and c with any support, get the same list.

Refutations at layer d are degree-0 refutations of the extended lists:
`Refutes0(xeqs(d, sk, c, es), SK.cats(ss, xsides(d, sk, c)), ...)`. So
`refute` (S2's elimination and S3's exact simplex) decides every layer
exactly, a certificate or a point showing there is none (lib/satpf.bend),
with no new decision procedure. That exact decision is what honest_unique
needs.

### Honest at layer d

NoRefute, ConflictOk (both halves), Implied and NotImplied take d and
refute over the extended lists; Fate, Honest and every law about them take
d. At d = 0 they are sk-13a's statements (xsides empty, xeqs the
identity). Drops (DropsOk, Derivable) and Over are not layered.

What a layer is not: complete for real infeasibility. Stengle's
Positivstellensatz needs arbitrary sums of squares in every variable, and
an exact, verified search for those is research. Each layer is complete
for itself (no refutation of its form exists), as degree 0 is today, and
the laws say exactly that.

### Deepening

`solve_l(sk, g0, l)`: for each layer d in turn (0, 2, ...): classify at
d, then run the precision ladder at level l (with the stop below). The
first certified answer is returned, with its layer. If every layer is
refused, the answer is the last layer's, refused, with its reason.

Cost: a sketch that certifies at layer 0 does exactly today's work.
Deeper layers run only after a refusal.

### The stop, and refusal reasons

In the precision ladder (`ploop`), after a precision whose plan is POk but
whose verdict fails, check:
- the plan's block certificates pass (the verdict's own block checks), so
  the box holds exactly one solution of the solved system with the pins at
  their drawn values;
- some checked side condition is definitely violated over the whole box:
  its ball (`KB.kball`, as the verdict's side checks use) lies below 0 for
  a ≥ 0 side, or at or below 0 for a > 0 side.

If both hold, no precision can help this attempt: it stops, with
`SideFails{c, i}`. The stop is tried only after a failed verdict, so an
accepted plan is never cut short.

`Out` gains `layer` and `why` (`Unsolved`, or `SideFails{c, i}`: side i of
constraint c, or of an entity, fails near the drawing). The verdict reads
`layer` (amber refutations are checked over the layer's lists) and
ignores `why`.

A refusal reason is never a classification: the box only certifies a
solution, so "cannot hold near this drawing" says nothing about solutions
elsewhere (DESIGN §8.11, Q28). Red always means a refutation.

### The laws

- `solve_honest`: `Honest(sk, Out.layer, Out.cls)` at every level.
- `honest_unique`: for every d, two layer-d honest classifications agree.
- `solve_drop`, `solve_amber`, `solve_conflict`, `solve_blame`: for the
  answer's layer (they use the interface's "the extras hold").
- `solve_exists`, `solve_unique`, `solve_pins`, `solve_regular`: unchanged
  (about ok answers).
- `solve_complete` (law 10): at layer 0, as now. A sketch whose layer-0
  system has a regular solution near the drawing certifies at layer 0, so
  deepening never changes that answer. (Its proof takes acceptance at the
  first precision of its level, `pf_head`/`ploop_true`, and the stop only
  acts after a failed acceptance.) `solve_refused` from it, as now.
- **New: `solve_side_fails`:** if `why` is `SideFails{c, i}`, then in every
  complete ordered field the reported box holds exactly one geometry
  solving the solved system (pins at their drawn values), and side i of c
  fails at every geometry in the box.
- Signed dimensions change three meanings and no law.

## Steps

### U0. Statements, and the measurement that fixes the families

- A spike, not committed as design: `refute` with squares appended, on
  the regression sketches and sketch 5, at the candidate layer-2 family;
  the pass's time per layer. It fixes the families and the last layer.
- The spec diffs (spec/sketch.bend and spec/geom.bend for U1;
  spec/solve.bend for the layers; lib/solve.bend's Out) and the laws above
  written out with a note on each in SK13S-REVIEW.md; the laws as open
  laws in ROADMAP.bend (tools/stmtcheck.py type-checks them).
- Danielle reads them; an audit agent checks them against the sk-13a laws,
  for the loopholes the four sk-13a audits found (laws empty because a
  premise is unsatisfiable, box-relative claims, supports that are not
  irreducible), and for one new to v2: a reported layer that would let a
  dishonest answer through.

### U1. Signed dimensions

- **Spec.** `Constraint.sides`: HDistance and VDistance lose `Ge0{d}`;
  LineDistance keeps `Gt0{l}` (its aux length) and loses `Ge0{d}`.
  Meanings (spec/geom.bend): `hdist` and `vdist` lose `0 ≤ d`; `line_dist`
  is signed (p is |d| from the line, on its left when d ≥ 0, its right
  when d < 0: with f the foot of p, p − f = (d / l)·J(b − a), J the
  quarter turn). The `rev` flag stays, so old sketches mean what they
  meant. The equations do not change: they were already signed.
- **Proofs.** lib/meaning.bend's lemmas for the three kinds, re-proven;
  the gate re-checks the rest (generic over the side lists).
- **Page.** Signed measuring in the dimension dialog; new HDistance and
  VDistance no longer swap their points (old sketches' `swap` still
  works); labels show the sign.
- **Regression.** HDistance −3 and LineDistance −1 certify, mirrored;
  Distance −5 still cannot hold.

### U2. The stop and refusal reasons

- `Out.why`, the stop in `ploop`, `solve_side_fails` proven (from the
  block certificates, as solve_exists and solve_unique use them, and the
  ball's soundness), laws 10 and 11 re-checked.
- Regression: angle-lines (sketch 5) refused in under a second with
  `SideFails` at the Angle (layer 0 only, until U4).
- Page: "cannot hold near this drawing", the condition in words.

Independent of the layers, and the quickest win, so it comes first.

### U3. Honest at every layer (the large step)

- **U3a, spec:** `xsides`, `xeqs`; NoRefute, ConflictOk, Implied,
  NotImplied, Fate, Honest with d. The solver still classifies at d = 0
  only.
- **U3b, the interface lemmas** for the families U0 fixed.
- **U3c, the pass honest at every layer:** lib/pass.bend and the deletion
  filter (lib/conflict.bend) take d and refute over the extended lists;
  prepf, conflictpf, totalpf, passpf, ckpf (the amber refutations the
  verdict checks) generalized. refute decides any lists, so the pass's
  proofs change by carrying the lists; the supports' irreducibility uses
  xeqs's growth.
- **U3d, honest_unique at every layer:** agreepf, hreadpf, nrconfpf,
  overpf, uniqpf carry d. The Conflict-against-NoRefute step runs refute
  on NoRefute's extended lists, and `pt_back`'s merges take the same
  `xsides` list on both sides, plus xeqs's growth for the support's
  equations.
- **U3e, the semantic laws** (solve_conflict, solve_amber, solve_blame,
  solve_drop) for every layer, with "the extras hold".
- At the end of U3 every law holds at every layer, and the solver's answers
  are unchanged (still layer 0).

### U4. Deepening

- `solve_l` tries the layers in turn; `Out.layer`; the laws restated over
  `Out.layer` and re-proven (U3 did the work).
- Regression: sketch 5 certifies at layer 2 with the Angle red,
  "conflicts with #2"; every other sketch answers at layer 0 as before,
  in the same time; a new sketch for each layer the families define.

### U5. Page: directions visible

- An arrow on each angle's arc, from the first segment's direction to the
  second's, and the value as typed (any value).
- Signed dimensions with their sign, arrowed from p to q.
- Refusal reasons; the layer of the answer ("found with squares") in the
  hover text.
- gui/README.md updated.

### U6. Audit and sign-off

- An independent audit of the statements as proven (SK13S-REVIEW.md
  against ROADMAP.bend and the restatements).
- Gate and regression green; Danielle signs off.

**Exit:** signed dimensions; every law proven at every layer; deepening;
`solve_side_fails`; sketch 5 explained and certified in under a second.

## Order and size

1. U0 statements and measurements (small).
2. U1 signed dimensions (small).
3. U2 the stop (moderate: a field in Out, the stop, one law).
4. U3 Honest at every layer (large: it touches every honesty proof,
   mostly by carrying the extended lists; several sessions).
5. U4 deepening (moderate), U5 page, U6 audit.

U1 and U2 help on their own and can ship before U3.

## How it could bite, and what limits it

- **Classification depends on how far the solver had to look.** A sketch
  that certifies at layer 0 shows a constraint as kept even if a deeper
  layer would call it redundant. That is honest for the reported layer.
  Conflicts cannot differ this way: a certified sketch has no refutable
  kept constraint at any layer (refutations are sound).
- **A refusal costs one attempt per layer.** The stop keeps each failed
  attempt fast; the families and the last layer come from U0's
  measurements.
- **The stop can, rarely, refuse an attempt a finer precision would have
  certified,** if a coarse precision converged to a neighbouring solution
  (lib/solve.bend notes it can). Its law stays true for its box. With the
  relaxation on (the default), the drawing is within about 1e-13 of a
  solution and every precision converges to the same one.
- **Signed dimensions turn a stray minus sign into a mirror image,** and
  LineDistance has two ways to say "the other side" (`rev` and the sign).
  U5's visible signs and arrows are required, not polish.
- **Directed angles surprise** when typed as interior angles: now a proven
  conflict, explained, but only legible with U5's arrow.
- **U3's proofs grow the spec's surface.** The interface keeps later
  layers cheap; the audit at U6 covers the statements.

## Relation to the other plans

- sk-13b–d (PLAN-sk13.md, DESIGN §8.11): dependencies among equations
  (directions and lengths by lemma, then Gröbner bases), which find implied
  equations and conflicts of equations. Layers here find sign
  contradictions, which those do not see (sketch 5's equations are
  consistent). They complement each other; xeqs's multiples are where the
  two meet, and sk-13d's degrees could become layers.
- "Right after sk-13a: the exact linear presolve" (PLAN-sk13a) is
  independent; the order is Danielle's call. S9 (sk-13a's audit) can run
  before or alongside U0.
