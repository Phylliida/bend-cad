# Plan: sk-13s, signs (v1, 2026-10-21, for Danielle's review)

Signed dimensions, fast refusals with a reason, and refutations with
squares. Everything the solver does here is proven, as in sk-13a: each
new behaviour comes with a law in ROADMAP.bend, restated with its proof in
tests/, and the page stays untrusted shaping only.

## Why

slowsketches sketch(5): a right triangle (Perpendicular at P0) with a
directed Angle of 47° from P3→P0 to P6→P3. As directed it cannot hold.
The drawing has −133° = 47° − 180°, so the Angle's equation (a cross
product) holds and its side condition (dot > 0: the directions agree)
fails.
- The solver refused, which was honest, but only after trying every
  precision (about 20 s).
- It could not say why: the contradiction needs one square, and sk-13a's
  refutations have none.

Danielle wants directed angles past 180° and negative dimensions as
orientation hints, so the fix is not to reinterpret what she typed. It is
to make the solver say "this cannot hold" quickly, and prove it.

Typical CAD solves numerically from the drawing and judges by the
numerics: Jacobian rank with a tolerance for redundancy, non-convergence
for "over-defined", blaming the newest constraint. It fails fast because
nothing is certified. Here a fast refusal must be a theorem.

## What sk-13s delivers

- **Signed dimensions.** HDistance and VDistance are signed: q.x − p.x = d
  for any d, so −3 means q is 3 to the left. LineDistance is signed: d < 0
  means the other side of the line. Distance, Radius and Diameter stay
  nonnegative: a length has no direction, so −5 still cannot hold.
  Angles are already directed (any value, mod 360).
- **Fast refusals with a reason.** When the solver's first certified box
  holds the only solution of the solved system near the drawing, and a
  side condition fails throughout that box, the solver stops. It reports
  "#c cannot hold near this drawing" and names which condition fails.
  Sketch 5 is refused in under a second, naming the Angle.
- **Refutations with squares** (the Positivstellensatz's next layer). A
  constraint whose impossibility needs a square becomes red, "conflicts
  with #a, #b", with a proof and an irreducible support. Sketch 5's Angle
  conflicts with the Perpendicular.
- **The page shows directions:** an arrow on each angle's arc, the sign on
  each signed dimension, and the new refusal reason.

## Ground rules (standing)

- Prove the solver as it runs; no check-and-fallback to ease a proof.
- Verified and complete (D7). All limits proved, not stated.
- Statements first: every spec change and new law is written down and
  read by Danielle before it is proven, and an audit agent looks for
  loopholes (agents only audit; I implement).
- Drafts in `tools/drafts/*.draft`, expanded by `tools/expand.py`.
- The gate is `./check.sh`; the native regression is `tools/regress.sh`.
- Commit freely, each step green. No exact counts in docs.

## Steps

### T0. Statements

- The spec diffs for T1 and T3 (spec/sketch.bend, spec/geom.bend,
  spec/solve.bend), and the new law for T2, written out with a note on
  each in SK13S-REVIEW.md; the laws as open laws in ROADMAP.bend
  (tools/stmtcheck.py type-checks them).
- Danielle reads them; an audit agent checks them against the sk-13a
  laws, for loopholes of the kinds the four sk-13a audits found (laws
  that say nothing because a premise is unsatisfiable, a box-relative
  claim that is empty, a support that is not irreducible).

### T1. Signed dimensions

- **Spec.**
  - `Constraint.sides`: HDistance and VDistance lose `Ge0{d}`; LineDistance
    keeps `Gt0{l}` (l is the segment's length) and loses `Ge0{d}`.
  - Meanings (spec/geom.bend): `hdist` and `vdist` lose `0 ≤ d`.
    `line_dist` becomes signed: p is |d| from the line, on its left when
    d ≥ 0 and on its right when d < 0 (equivalently, with the foot f of p
    on the line, p − f = (d / l)·J(b − a), J the quarter turn). The `rev`
    flag stays (it reverses the segment, so old sketches mean what they
    meant).
  - The equations do not change: they were already signed.
- **Proofs.** lib/meaning.bend's lemmas for the three kinds (equations and
  sides give the meaning), re-proven for the new meanings. Everything else
  is generic over the side lists and re-checks: the gate, laws 1–11.
- **Page.** The dimension dialog measures signed values (q.x − p.x;
  signed distance to the line), new HDistance and VDistance no longer
  swap their points to keep the value positive (old sketches' `swap` still
  works), and labels show the sign.
- **Regression.** New sketches: HDistance −3 (certifies, q to the left),
  LineDistance −1 (certifies, the other side), and Distance −5 (still
  cannot hold).

### T2. Fast refusals

- **The stop.** In the search loop (lib/solve.bend: `ploop`), after a
  precision whose plan is POk but whose verdict fails, check:
  - the plan's block certificates pass (the verdict's own block checks),
    so the box holds exactly one solution of the solved system with the
    pins at their drawn values;
  - and some checked side condition is definitely violated over the
    whole box: its ball (`KB.kball`, as the verdict's side checks use) lies
    below 0 for a ≥ 0 side, or at or below 0 for a > 0 side.

  If both hold, no precision can help: stop and record why. The stop is
  tried only after a failed verdict, so an accepted plan is never cut
  short.
- **The answer.** `Out` gains a field `why`: `Unsolved` (no reason
  known, today's refusals) or `SideFails{c, i}` (side i of constraint c,
  or of an entity, fails near the drawing). The verdict ignores it.
- **New law, `solve_side_fails`:** if `why` is `SideFails{c, i}`, then in
  every complete ordered field the reported box holds a geometry solving
  the solved system (pins at their drawn values), exactly one, and side i
  of c fails at every geometry in the box. So the sketch has no solution
  in that box. It says nothing about solutions far from the drawing.
- **Law 10 (`solve_complete`)** keeps its statement. Its proof takes
  acceptance at the first precision of the level it picks
  (lib/completepf.bend: `pf_head`, `ploop_true`), and the stop only acts
  after a failed acceptance, so the proof should go through as is. Laws
  1–3 and 11 are unchanged.
- **Page.** "cannot hold near this drawing", with the condition in words
  (for an Angle: "its directions point opposite ways"; for a LineDistance:
  "the segment has length 0").
- **Regression.** angle-lines (sketch 5) refused in under a second with
  `SideFails` at the Angle; expected updated.

### T3. Refutations with squares

**The idea.** sk-13a's refutations are the degree-0 layer of the
Positivstellensatz (Krivine 1964, Stengle 1974; DESIGN §8.11's principle).
The next layer adds squares, which hold everywhere. Sketch 5's
certificate, with a = P0 − P3, b = P3 − P6 and (c, s) the Angle's
rotation:

  c·(angle's dot) + (c² + s²)·|P0 − P3|² = s·(angle's cross) − (c² + s²)·(perpendicular)

The left side is positive wherever the Angle's side holds, and the right
side is 0 wherever the equations hold. The only thing degree 0 lacks is
the square |P0 − P3|².

**The design: squares as premises.** A square is a side condition that
always holds (q² ≥ 0 in every ordered field). So the layer appends a list
of squares to the side premises of every refutation sk-13a states:
NoRefute, ConflictOk (both halves) and Implied/NotImplied. Everything else
stays degree-0 machinery:
- `Refutes0`, `refok` and `Ident` are unchanged;
- `refute` (S2's elimination and S3's exact simplex) decides the extended
  lists exactly, as it decides today's: a certificate, or a point showing
  there is none (lib/satpf.bend). That exact decision is what
  honest_unique needs, so it carries over.

**Which squares (to settle in T0).**
- The squares of the degree-2 DSOS basis over c's own variables V (those
  its equations and sides mention): x_v², (x_u ± x_v)², (x_v ± 1)² for u,
  v in V. c's variables only, so the list is small and depends on c
  alone. It is the same list in every premise order, and the same for c
  with any support, which keeps the support and uniqueness arguments as
  they are.
- That catches sketch 5 (|P0 − P3|² is a sum of two of them) and the like:
  angle and side facts in a triangle a constraint belongs to.
- Later layers grow the family: multipliers on the equations
  (x_v·e), products of sides, squares over neighbouring constraints'
  variables. Each layer is a spec parameter, decided exactly by the same
  simplex, with the same laws.
- What the hierarchy is not: complete for real infeasibility. Stengle's
  theorem needs arbitrary sums of squares, and finding those is
  semidefinite programming; an exact, verified search for them is
  research. Each layer is complete for itself, as degree 0 is today, and
  the laws say exactly that.

**Steps.**
- **T3a, spike (no commit to the design yet):** run `refute` with the
  squares appended on the regression sketches and sketch 5; measure the
  pass's time (the deletion filter calls refute once per candidate). If
  the cost is too high, the family shrinks (squares of differences of a
  point pair's coordinates only) before the spec is written.
- **T3b, spec:** `vars_of(sk, c)`, `squares(sk, c)` (the list of
  `Ge0{q·q}`), and NoRefute, ConflictOk and Implied with
  `SK.cats(..., squares(sk, c))` appended to their side lists.
- **T3c, the pass:** lib/pass.bend calls refute with the squares;
  conflict.bend's deletion filter likewise.
- **T3d, proofs.**
  - A square side holds at every point (`sq_holds`, one lemma); the
    semantic laws (solve_conflict, solve_amber, solve_blame) use it where
    sk-13a uses the entities' sides.
  - The pass's honesty (prepf's `no_refute` and `conflict`, conflictpf,
    totalpf) and honest_unique's step 4 (nrconfpf's `pt_back` merges)
    carry the extra list; it is the same list on both sides, so the
    merges extend by one `alls_cat`.
  - Laws 4–8, 10 and 11 re-proven over the new Honest; laws 1–3 and the
    drops are untouched.
- **Regression:** sketch 5 has the Angle red, "conflicts with #2" (the
  Perpendicular); the S8 sketches unchanged unless a square makes a
  difference (each change looked at).

### T4. Page: directions visible

- An arrow on each angle's arc, from the first segment's direction to the
  second's, and the value as typed (any value).
- Signed dimensions drawn with their sign, the arrow from p to q.
- The new refusal reason and conflicts in the list.
- gui/README.md "What the list says" updated.

### T5. Audit and sign-off

- An independent audit of the statements as proven (SK13S-REVIEW.md
  against ROADMAP.bend and the restatements).
- Gate and regression green.
- Danielle signs off.

**Exit:** signed dimensions, `solve_side_fails` and the squares layer
proven; sketch 5 explained in under a second, then red with its support.

## Order and size

1. T0 statements (small).
2. T1 signed dimensions (small: three meanings and the page).
3. T2 fast refusals (moderate: a new field in Out, the stop, one new
   law, law 10 re-checked).
4. T3 squares (the large one, gated by T3a's measurement; it touches
   every Honest-related proof, mostly by carrying one more list).
5. T4 page, T5 audit.

T1 and T2 are independent and help on their own; T3 can follow later.

## Relation to the other plans

- sk-13b–d (PLAN-sk13.md, DESIGN §8.11) are about dependencies among
  equations: directions and lengths by lemma, then Gröbner bases. Those
  find implied equations and conflicts of equations. T3 is about sign
  contradictions (inequalities), which those do not see: sketch 5's
  equations are consistent. They complement each other.
- "Right after sk-13a: the exact linear presolve" (PLAN-sk13a) is
  independent of this plan; the order between them is Danielle's call.

## Risks

- **T3's cost.** Squares add LP columns to every refutation the pass makes;
  the deletion filter multiplies that. T3a measures before any spec
  change.
- **T2's stop condition.** It must use exactly the verdict's block checks,
  so the new law can say "exactly one solution in the box". If the
  verdict's structure makes that awkward, the stop asks for the blocks
  separately (same lemmas).
- **Signed LineDistance's meaning.** The signed form must stay a meaning
  in every ordered field without square roots (hence the aux length l).
  The audit checks that it says what the page draws.
