# bend-cad — Design v0.13 (draft; exact by default; sk-06 done; sk-09: a verified proposer)

A formally verified 2D sketch constraint solver in Bend 2, aiming at Onshape /
FreeCAD sketcher parity, feeding an implicit-function (SDF) modeling pipeline.

This document is self-contained. It does not build on any existing project in
the workspace; external solvers and papers are cited as references only.
History: v0.1 was audited ([AUDIT-v0.1.md](AUDIT-v0.1.md)); v0.2 folded the
audit in; v0.3 makes exactness the default; v0.4 records Danielle's answers
to the open questions; v0.5 records the spec-number choices made in sk-01
(§3); v0.6 records the typed IR, equation forms and meaning statements of
sk-03 (§4, §5); v0.7 folds in Danielle's answers to the sk-03 review; v0.8
records the meaning lemmas proven in every ordered field (§5.5); v0.9
records the sk-04 library: rational order, ℚ in every ordered field,
vectors and matrices, gcd reduction, canonical ℚ (§3, §8.3, §19 changelog).

---

## 0. Goal and scope

**Entities:** points, segments, circles, arcs, ellipses and conic arcs,
B-splines and NURBS (control-point and fit), offset curves; construction
(reference-only) flag on any entity.

**Constraints:** coincident, concentric, horizontal, vertical, fix, parallel,
perpendicular, normal, tangent (curve–curve and at joins), G1/G2, equal,
midpoint, symmetric, block; distance (point–point, horizontal, vertical,
point–line, line–line, point–circle, circle–circle), radius/diameter, angle,
arc sweep, point-on-curve, offset; driven (reference) dimensions; dimension
expressions over named variables; trim, extend, split, fillet; drag.

**Downstream:** implicit / SDF modeling (extrude, revolve, CSG, sphere tracing).
No B-rep.

**Motivating stress case:** chains of 20–30 dependent circle∩circle
constructions.

**Out of scope for v1:** 3D constraints; B-rep topology; external references
(projecting model edges; an SDF model has no explicit edges); Snell's-law
constraint; certified global optimality of the nearest solution. Arc length is
designed for and built late (§7.4).

---

## 1. Decisions

| # | Decision |
|---|---|
| D1 | **Exact by default.** Every committed sketch state carries a proof, stated over ℚ, that an exact real solution exists within radius r of the displayed geometry and is unique there. Pinned, fixed and merged values and typed dimensions hold exactly for that solution. |
| D2 | **Displayed geometry is exact integers** at fixed per-kind scales; certificates use dyadic rationals at a working precision chosen per block. Denominators never grow across solves. |
| D3 | Coincident points, horizontal, vertical, fix, and concentric / equal radius between full circles are **variable merging / constants**. |
| D4 | **Every curve piece passes through its endpoints by construction** (segments, bulge arcs, clamped splines, conic arcs as rational Béziers). Profiles are exactly closed. |
| D5 | Contact points, trim/split points and curve parameters are **explicit variables**, with encodings chosen to be **regular** (nonsingular Jacobian) at the configurations users draw. |
| D6 | The **typed IR is the spec and the persisted source of truth**. Each constraint kind has an exact equation form, defined in LAWS.bend, with a **mandatory meaning lemma**. |
| D7 | **The proposer is verified** (Danielle, 2026-10-14: "trusted everything"): every answer the solver gives is a law about the sketch, and every stage is proven to succeed where it should (§10). (Was: one acceptance theorem over arbitrary proposals, the proposer outside the trust story.) |
| D8 | **Block-decomposed parametric certificates** keep exact certification near-linear in sketch size (§8). |
| D9 | **Dimension constants are exact**: rationals, certified algebraic roots, or constructive reals defined over ℚ (§7). Any measured quantity can be shown with guaranteed digits, more on demand (§9). |
| D10 | **Uncertifiable constraints are flagged red**, individually; the rest of the sketch stays exactly certified. Positional tolerance checks are used for drag previews and to report how far a flagged constraint is from holding (§6). |
| D11 | **Lipschitz bounds replace interval arithmetic** everywhere. |
| D12 | **Everything is written in Bend**, including the proposer and the prototype. |
| D13 | **"Change as little as possible" means least ink displacement**: the integral of squared displacement along every drawn curve (§10). |
| D14 | **Every bounded face of the arrangement of non-construction curves is a region** (Onshape-style); no fill rule (§12). |

---

## 2. Why this shape

**Exact symbolic numbers are infeasible at depth.** Each circle∩circle adjoins
a square root; k steps give a quadratic tower of degree up to 2^k (~10^9
coefficients per coordinate at k = 30), and exact zero tests via separation
bounds (BFMSS) need on the order of 2^k times the input bit-size. So exact
coordinates cannot be stored or displayed.

**What "exact" means here.** The exact solution is a real point we never
write down. We store a nearby integer point and a certificate proving the
exact one exists within r and is unique there. The certificate also yields any
number of further correct digits on demand: each exact coordinate is a
*constructive real* defined implicitly as the unique root in a certified ball.

**Relation to the Android calculator (Boehm, PLDI 2020).** Same family of ideas:
exact rationals where cheap; lazily refined reals with guaranteed digits
elsewhere; and the recognition that deciding equality is the hard part, solved
by structure rather than by numerics. Differences:
- Boehm's reals are explicit expressions (rational × tagged constructive real,
  with tags like π, √a, e^a, sin(πa)). Ours are mostly implicit: roots of
  polynomial systems, certified by contraction. Newton refinement converges
  quadratically, so extra digits are cheap.
- Boehm decides equality with cheap symbolic rules on tags. We get exact
  equalities from structure (merging, regular encodings) and from polynomial
  identity certificates (§8.7), which reach relations between deep algebraic
  quantities that tags cannot.
- The calculator can keep rationals exact because expressions are short. A
  sketch solve cannot (denominators grow with every step), so we round to a
  grid and carry certificates instead.
- Everything here is proven in Bend; the calculator library is engineered, not
  formally verified.
- We borrow two of its ideas directly: constants as rational × known constant
  (§7) and guaranteed-digit display (§9).

**Positional tolerance is not a mode** (D10). It is cheap and needs no
certificate, so it gives drag previews and tells the user how far a red-flagged
constraint is from holding (accidental singularities, coincidental redundancy).

---

## 3. Numbers

**Spec numbers (decided in sk-01; `spec/num.bend`).** Bend's checker evaluates
`Nat` in unary (`{==}` on `Nat.is_lt(10^6, 10^6+1)` took 1.3 s in the audit),
so closed facts about large constants cannot be decided by computation on
Peano `Nat`.
- Positives in **binary**, Coq's shape (`XH | XO p | XI p`); addition is one
  def with a carry bit (Bend has no mutual recursion). Meaning: `Pos.nat`,
  proven injective and a homomorphism.
- Integers `Z0 | Zpos p | Zneg p` (Coq's `Z`, canonical zero; approved by
  Danielle over `ofNat | negSucc`). Meaning: `Z.of_diff(a, b)` = a − b, with
  parts `Z.pnat`/`Z.nnat`; add/mul/neg/cmp are proven to act on differences
  as integer arithmetic does.
- **Rationals are unreduced** `Q{n: Z, d: Pos}` with `Q.eq` (cross-
  multiplication) as their equality; ℚ is proven a field under `Q.eq`. Reducing
  by gcd is a runtime choice, to be proven to keep `Q.eq` (sk-04). Rationale:
  no proof needs reduced fractions to be unique (which would need the gcd /
  Bézout theory), and every ℚ identity becomes a ℤ identity that the
  normalizer decides. Operations use the projections `Q.num`/`Q.den`, so they
  compute on unknown arguments.
- Dyadics `D{m: Z, e: Nat}` = m/2^e (exponent unary: it stays small), meaning
  `D.toq`; add aligns exponents by peeling common steps.
- **Order (sk-04):** `Q.lt` (`Q.cmp` says LT) is a strict total order up to
  `Q.eq`, respected by `Q.eq`, by adding a rational and by positive products,
  so ℚ is an ordered field under `Q.eq`. Proven through signs
  (`lib/zord.bend`): x < y exactly when a cross difference is positive, and
  positivity is closed under + and · by computation.
- **ℚ in every ordered field (sk-04):** `O.ofq` respects `Q.eq`, +, ·, −, 0
  and 1, and preserves and reflects the order. So a rational fact decided by
  computation holds in every ordered field: the bridge from a checker's
  arithmetic to the exact (real) solution.
- **Reduction (sk-04):** `lib/qreduce.bend` reduces by the gcd at runtime.
  Division and gcd are untrusted; the result is checked by multiplying back,
  so `Q.eq(reduce x, x)` needs no divisibility theory.
- **Canonical ℚ (sk-04):** `lib/qfield.bend`, 0 or a sign and a Stern–Brocot
  word (`lib/sb.bend`), so Bend's equality is equality of rationals; it is an
  ordered-field instance (`ofield_exists`): the axioms of `spec/field.bend`
  are consistent and every law stated for all ordered fields has content.
  Encoding is subtractive Euclid (about n/d + d/n steps): for proofs and
  small checks, not runtime.
- Binary `N` is not defined yet: no consumer needs it (exponents and variable
  indices are small unary `Nat`). Add it when one does.
- **Reflective normalizers** (`lib/zring.bend`, `lib/qring.bend`): ℤ ring
  identities with binary coefficients, one `ring_eq(env, e1, e2, {==})` call;
  ℚ identities (no division) by translating to numerator/denominator and
  cross-multiplying. Checker cost is small: (a+b+c+d)^7 ≈ 0.9 s. They are
  bootstrapped from a unary Nat normalizer and a ℤ-via-pairs tactic, so no
  binary carry reasoning is ever done by hand.

**Runtime numbers (built in sk-02; `rt/`, `spec/big.bend`).** Big integers are
signed lists of limbs in base B = 1 + bp, least significant first; limbs are
runtime `Nat` (native, capped at 2^48 − 1, fail-stop). The base is a
**parameter** of every operation and law: the checker unfolds a literal such as
`65536n` to unary (a stack overflow), so proofs are generic in B and the
runtime passes bp = 65535 at the top (instantiation checks; `tests/big_demo`).
Meaning `Big.val` into spec `Z`; well-formedness `Big.wf` = every limb ≤ bp.
Carries use `Nat.mod`/`Nat.div` (two native divisions per limb); subtraction
borrows by one comparison per limb so every limb is an exact `Nat.sub`. With
well-formed inputs every intermediate stays below B·B + B ≪ 2^48. Measured:
16-limb (256-bit) schoolbook product ≈ 12 µs native single-thread
(20000 in 0.25 s; the sk-P1 prototype took 0.35 s). Not `U32` limbs (`U32` is a
32-bit `Word` bit list in the theory; no `U64`).

**Scales.** Displayed variables are integers at a per-kind scale.
- Coordinates and lengths: **1 nm** (decided). Inch fractions are exact down to
  1/64" (25.4 mm = 2^6 · 127 · 5^5 nm).
- Curve parameters (t, bulge b): dyadic at scale 2^−s (shallow arcs need large
  s; §5.3).
- Certificates work at a per-block precision p (dyadic) chosen by the proposer;
  only the displayed result is rounded to the grid.

---

## 4. Typed IR (the spec input)

As built in sk-03: `spec/sketch.bend` (trusted). The rest of this section is
the plan; the bullets marked *as built* record what sk-03 fixed.

- *As built:* a sketch is `Sketch{vars, ents, cons}`. Unknowns are
  **variables named by index** into an environment. **Entities** have
  persistent IDs: a point `GPoint{x, y}` names its two coordinate variables,
  a segment `GSeg{p, q}` its endpoint points (directed p → q), a circle
  `GCirc{c, r}` its center point and radius variable, a bulge arc
  `GArc{s, e, b}` its end points and bulge variable. Merged points (D3) share
  variables.
- *As built:* **constraints reference existing entities by ID** (Danielle,
  Q14). The spec resolves each reference (`pt`, `seg`, `circ`), and
  `wf_refs` requires it to name an entity of the right kind. Orientation
  choices are explicit fields: a line distance's side (`rev`), an angle's
  direction on each segment (`ra`, `rb`); a horizontal/vertical distance's
  points are ordered.
- *As built:* each constraint kind has `eqs` (polynomials that must vanish),
  `sides` (polynomials that must be positive), `wf` (for merge kinds, the
  variable sharing that realizes them) and `means` (its geometric meaning in
  any ordered field, `spec/geom.bend`). Equations and dimensions are `QExpr`
  over the variables, so a dimension may be a rational, a named variable, or
  an expression.
- *As built:* `Sketch.eqs` (the system F: every driving constraint's
  equations), `Sketch.sides` (every entity's side conditions, then every
  driving constraint's), `Sketch.wf`, `Sketch.holds`, `Sketch.means`. **Geometry
  may degenerate** (Danielle, Q15): points and segments carry no conditions,
  so a segment may collapse to a point. Circles keep r > 0 and arcs b > 0.
  Driven constraints contribute nothing.
- *As built:* persistent IDs on entities and constraints (`Ent.id`, `Rec.id`);
  a variable's ID is its index. Deletion and renumbering policy: sk-21.
- **Persistent IDs** for every entity, variable and constraint. The typed IR is
  saved, loaded, and re-certified on load.
- **Variable kinds:** `coord`, `length`, `param`, `aux`.
- **Entities:** `Point`, `Segment(P, Q)`, `Circle(C, r)`, `Arc(S, E, b)` (bulge
  arc), `ConicArc(...)`, `BSpline(degree, knots, control points, weights)`,
  `Offset(base, d)`; each with a construction flag.
- **Constraints** are typed and reference entities by ID. Their exact equation
  forms (§5) and tolerance checks (§6) are produced *inside* the checker, so an
  untrusted front end cannot change what a constraint means.
- **Merging (D3)** is recorded as shared variable IDs. Merge conflicts are
  errors (two different constants; horizontal and vertical on one segment).
  *As built:* coincident, horizontal, vertical, and concentric / equal radius
  of full circles stay in the IR as records of intent; `wf` requires the
  referenced entities to share their variables. `Fix{v, k}` is an equation v − k = 0 in the spec;
  treating v as a constant is the certificate layer's optimization (§8).
- **Dimensions** are driving or driven. Driving values are exact constants (§7)
  or expressions over named sketch variables.
- **Evaluation** is a straight-line program over an environment (shared
  subterms computed once; Bend has no CSE). No expanded sparse polynomials.
- **Certification status** per constraint: `Exact` (default) or `Flagged`
  (shown red, with the reason and its positional deviation).

---

## 5. Exact equation forms (the default spec)

Each constraint kind has a polynomial equation form F = 0, plus strict side
conditions (signs, ranges, nondegeneracy) certified over the ball (§8.6).

**Regularity rules (D5):**
- Never use a squared form whose target is zero (a double root makes the
  Jacobian singular): zero distance is a merge, zero offset is point-on-curve.
  *As built:* the spec allows a zero distance (its meaning is p = q); the
  front end merges the two points, after which the equation vanishes
  identically and is discharged as redundant (§8.7). Left unmerged, it is
  singular and flagged (§8.8). Zero horizontal, vertical and point–line
  distances are linear and certify as they are.
- Signed forms with an aux length ℓ (ℓ² = \|w\|², ℓ > 0) where a square root
  would otherwise appear.
- Known singular patterns are rewritten by the compiler, e.g. a point placed on
  two tangent curves is merged into their contact point.

### 5.1 Core

| Constraint | Exact equations | Side conditions |
|---|---|---|
| coincident, horizontal, vertical; concentric / equal radius of full circles | merge (shared variable indices) | — |
| fix / block: variable v = k | v − k = 0 | — |
| distance(P, Q) = d | \|Q − P\|² − d² = 0 | d ≥ 0 |
| horizontal / vertical distance | (Qx − Px) − d = 0 (resp. y); Q right of / above P | d ≥ 0 |
| radius r = d; diameter | r − d = 0; 2r − d = 0 | — (the circle keeps r > 0) |
| equal length | \|u\|² − \|v\|² = 0 | — |
| perpendicular / normal | dot(u, v) = 0 | — |
| parallel | cross(u, v) = 0 | — |
| point on line AB (anywhere on the line through the segment) | cross(B − A, P − A) = 0 | — |
| point–line distance d, P left of A → B or on it | cross(B − A, P − A) − d·ℓ = 0, ℓ² − \|B − A\|² = 0 | ℓ > 0; d ≥ 0 |
| point on circle | \|P − C\|² − r² = 0 | — (the circle keeps r > 0) |
| midpoint M of segment PQ | 2M − P − Q = 0 | — |
| symmetric P, Q about AB | \|w\|²(Q − A) − R̂(P − A) = 0, w = B − A, R̂ = [[wx²−wy², 2wxwy], [2wxwy, wy²−wx²]] | — |
| angle from u to v given by rotation (c, s) | cross(R u, v) = 0, R = [[c, −s], [s, c]]; c = cos θ, s = sin θ exact constants (§7) | dot(R u, v) > 0 |

*As built (sk-03):* geometry may degenerate (Q15), so there are no ℓ_min
bounds and no nondegeneracy conditions on segments, and distances may be 0.
Side conditions are only dimensions (d ≥ 0) and choices the user made: the
side of a line, an angle's quadrant (dot > 0, which also makes both
directions and (c, s) nonzero). There is no bounded point-on-segment
constraint: a point on a segment's line may sit past its ends, as in other
sketchers; a bounded variant can be added if a use appears. A relation on a
collapsed segment holds vacuously, exactly as its equation does: a zero
vector is parallel and perpendicular to everything, any point is on a
collapsed line, and any pair mirrors in it (such a configuration is then
under-determined, so certification flags it, §8.8). A point–line distance
keeps ℓ > 0: it measures from a line, so the line must exist. The angle
needs no c² + s² = 1: any positive multiple of (cos θ, sin θ) names the same
rotation direction. Point–line distance puts P on the left (counterclockwise,
y up), matching the usual orientation sign; the front end orients the line.
Line–line, point–circle and circle–circle distances (§0) are not in the
table yet; they are added with sk-07.

### 5.2 Tangency and joins

| Constraint | Variables | Exact equations | Side conditions |
|---|---|---|---|
| line–circle tangent | contact T, param t | T − A − t(B − A) = 0; dot(T − C, B − A) = 0; \|T − C\|² − r² = 0 | r > 0 |
| circle–circle tangent | contact T, param s | T − C₁ − s(C₂ − C₁) = 0; s²D − r₁² = 0; (s − 1)²D − r₂² = 0, D = \|C₂ − C₁\|² | external: 0 < s < 1; internal: s > 1 or s < 0 |
| G1 join at merged endpoint | — | cross(t₁, t₂) = 0 (end tangent directions) | dot(t₁, t₂) > 0 |

The circle–circle form is regular: its Jacobian in (s, D) has determinant
−2sD(s − 1) ≠ 0 whenever s ∉ {0, 1} and D > 0.

### 5.3 Arcs (D4)

`Arc(S, E, b)`: S, E point variables, b = tan(sweep/4) > 0, counterclockwise
from S to E (a clockwise arc is stored with its ends swapped).
- Derived center C = (S+E)/2 + perp(E − S)·(1 − b²)/(4b); derived
  r² = \|E − S\|²(1 + b²)²/(16b²); both rational in the variables; equations
  clear the denominators.
- Tangent at S: R̂_b(E − S) with cos = (1 − b²)/(1 + b²), sin = 2b/(1 + b²).
- Passes through S and E exactly; loops close exactly.
- Concentric / equal radius involving arcs: equations on derived C and r².
- **Arc sweep dimension θ:** b − tan(θ/4) = 0, an exact constant (§7). The
  sweep is exact without any transcendental function of a variable.
- Quantization: the displayed b at scale 2^−s; the certificate works at higher
  precision regardless.
- **Creation tools** map to bulge arcs plus constraints:
  - *3-point arc:* the middle point is a creation hint (as in Onshape) that
    sets the initial b. An exact arc through three grid points generally has
    an irrational bulge; b is then a variable certified like any other.
  - *Center-point arc:* bulge arc plus a "center of this arc = point C"
    constraint (two equations on the derived center).
  - *Tangent arc:* bulge arc plus a G1 join at its start.

### 5.4 Curves

| Constraint | Variables | Exact equations | Side conditions |
|---|---|---|---|
| point on B-spline span j | param t | P − C_j(t) = 0 | knot_j < t < knot_{j+1} (or knot-straddle rule for C¹ splines) |
| point on NURBS span j | param t | w(t)·P − N(t) = 0 | span range; weights > 0 |
| curve–spline tangent | contact params | contact equations; cross(C′(t), other tangent) = 0 | \|C′(t)\| > 0 |
| offset point at distance d > 0 | param t | dot(P − C(t), C′(t)) = 0; \|P − C(t)\|² − d² = 0 | \|C′(t)\| > 0; side as drawn |
| G2 join | aux lengths ℓᵢ, ℓᵢ² = \|Cᵢ′\|² | curvature equality written with the aux lengths (no squaring of the whole relation), exact form fixed in sk-15 | ℓᵢ > 0 |
| conic arcs | — | rational quadratic Bézier through end control points | weights > 0 |
| trim / extend / split / fillet | new point variables | point-on equations on both curves | ranges |

C_j(t) is evaluated in Bernstein form per span.

### 5.5 Meaning lemmas

Mandatory, one per kind, connecting the equation to its geometric meaning
(e.g. \|Q − P\|² = d² with d > 0 ⇔ the distance is d; the symmetric equation ⇔
Q = mirror(P); the tangency equations ⇔ the curves touch at T with the stated
side). Exact forms make these much shorter than the tolerance versions.

*As stated in sk-03 and proven in sk-07* (`LAWS.bend`, `lib/meaning.bend`):
the meanings are
`Constraint.means`, one case per kind, in the textbook vocabulary of
`spec/geom.bend`. For example: parallel means one direction is a multiple
of the other;
perpendicular is parallel to a quarter turn; a point on line AB makes B − A
and P − A parallel; a mirror image has its midpoint on the line and its
offset perpendicular to it; the point–line distance is the distance to the
foot of the perpendicular. Two laws cover every kind:
`means_sound` (wf, eqs = 0 and sides > 0 ⇒ means) and `means_complete` (the
converse: the form asks for nothing more). `ent_sound`/`ent_complete` do the
same for entities, and `sketch_sound`/`sketch_complete` lift both to a whole
sketch: a solution of F = 0 with every side condition positive is exactly a
sketch where every circle and arc is proper and every driving constraint
holds.

**In every ordered field** (Q13, Danielle: "it should be possible to do it
usably"; it is). A sketch's exact solution is real and usually irrational,
and a statement proven only for rational points can fail at real ones
(x² = 2y² ⇒ x = 0 holds over ℚ only). So the meanings are stated for every
ordered field F (`spec/field.bend`: carrier, operations and the textbook
ordered-field axioms in one record), which includes the reals: no meta-level
step is needed for them. F is a **template parameter** (`for ~F: OField`):
Bend checks a template with its parameters opaque, and a template's axioms
may be used any number of times, which an ordinary function argument could
not (it is affine). Equality in F is Bend's own `{==}`, so proofs rewrite
with `%` as usual. Equation constants enter F through `ofq` (n/d built from
1, +, −, inverse), and expressions are evaluated by `eval`.

**Proofs (sk-07).** All six laws are proven for every ordered field, from
the axioms alone. The machinery, all untrusted: `lib/flaws.bend` (ring laws
from the axioms), `lib/fring.bend` (the ℤ normalizer's soundness re-proven
in F, with integer coefficients entering through `ofz`), `lib/ford.bend`
(order facts and *certificates*: x = 0 from relations rᵢ = 0 and one
normalizer call x = Σ cᵢ rᵢ; a division enters as an atom i with the
relation n·i − 1 = 0). Each kind is proven by value against
`lib/mforms.bend` (generated from the spec arms), matching on the resolved
points so both sides compute to the same coordinates. The deep cases: the
parallel family splits on |u|² (zero, or v = (dot/|u|²) u); the mirror uses
four-relation certificates; the point–line distance builds the foot of the
perpendicular and uses Lagrange's identity, with uniqueness of nonnegative
square roots for the converse. Drafts and generators: `tools/`.

`tests/sketch_demo.bend` checks every form over ℚ on a rectangle with a
known rational solution, including a collapsed segment and zero distances,
plus failing cases (a wrong angle, the wrong side of a line, a negative and
a reversed distance), and that references resolve. `tests/field_demo.bend` proves the
Fix case of `means_sound` in every ordered field from the axioms. Concrete
checks of the meanings at the rectangle need an ordered-field instance:
canonical (gcd-reduced) ℚ would be one, and building it would also show the
axioms consistent (proposed for sk-04).

---

## 6. Tolerance checks (previews and explicit fallback)

Positional checks on the displayed integer geometry, decided exactly. Used for
drag previews and to report, for each red-flagged constraint, how far it is
from holding (e.g. coincidental redundancy, accidental singularities).

**Meaning template:** the constraint can be made exactly true by moving one
designated point by at most cε. Direction checks measure the deviation as a
displacement of the shorter entity's far endpoint, e.g. perpendicular:
dot(u, v)² ≤ ε²·max(\|u\|², \|v\|²).

| Constraint | Check |
|---|---|
| distance d | (d − ε)² ≤ \|u\|² ≤ (d + ε)² (lower bound vacuous if d ≤ ε) |
| equal length | (A − B − ε² ≤ 0 ∨ (A − B − ε²)² ≤ 4ε²B), and with A, B swapped; A = \|u\|², B = \|v\|² |
| perpendicular / parallel | dot² (resp. cross²) ≤ ε²·max(\|u\|², \|v\|²) |
| point on line / segment | cross(P − A, B − A)² ≤ ε²\|B − A\|² (segment: plus 0 ≤ dot ≤ \|B − A\|²) |
| point on circle | (r − ε)² ≤ \|P − C\|² ≤ (r + ε)² |
| midpoint | \|2M − P − Q\|² ≤ 4ε² |
| symmetric | \|\|w\|²(Q − A) − R̂(P − A)\|² ≤ ε²\|w\|⁴ |
| angle θ | positional check with rational enclosures of cos θ, sin θ, tightened by the enclosure width |
| tangency, curves | contact checks with bands and positional direction checks |

**Rounding lemma** (per kind): a configuration satisfying the check within ε/2
at a finer resolution rounds to a grid point satisfying it within ε, given
ε ≥ c_k·grid and ℓ_min bounds.

---

## 7. Exact constants (Boehm-style)

Every driving dimension value is exact, represented as **rational × known
constant**, with three kinds of constant:

**7.1 Rationals.** Decimal mm, inch fractions, expressions over rationals.

**7.2 Algebraic constants** of small degree: √2, √3, √5, the golden ratio, etc.
(Q17: these may instead be computed exactly, with the checker running on
K = ℚ(√d); the minimal polynomial then becomes a hypothesis on F.)
Each is an aux variable in its block with its minimal polynomial (s² − 3 = 0)
and a sign condition (s > 0). The block certificate then proves the variable is
exactly that root. Angles that are multiples of 15° or 18° only need these.

**7.3 Transcendental constants** (π, cos θ and sin θ for arbitrary typed θ,
tan(θ/4) for arc sweeps): defined in the spec as **constructive reals over ℚ**,
i.e. a function from precision k to a rational, with a proven error bound
(alternating / Taylor series remainders after argument reduction). They enter a
block as **parameters** whose ball radius is the proven error bound (§8.3).
The theorem then says the exact solution satisfies the constraint for the true
constant, the limit of the approximations. No abstract real field is needed.
This replaces v0.2's rational rotations: typed angles are now exact.

**7.4 Transcendental functions of variables** (arc length L = r·4·atan(b);
spline length as an integral): need a constructive function together with proven
slope / Lipschitz bounds (e.g. atan′ = 1/(1 + b²), rational). Circular arc
length is within reach with a small verified atan library; spline length needs
verified quadrature (e.g. Taylor models). Built late (sk-18).

---

## 8. Exact certification (default)

### 8.1 Pinning

Under-constrained sketches are made square by **pinning** free degrees of
freedom at their displayed grid values. The proposer chooses the pins; a bad
choice just fails to certify and is retried. Pinned values are exact by
construction.

### 8.2 Block decomposition

The proposer orders variables and equations into a **block lower-triangular**
form (Dulmage–Mendelsohn / DR-planning style): each block's equations involve
only its own unknowns and earlier blocks' variables. The checker verifies the
triangular structure. A depth-30 circle chain becomes 30 blocks of 2 unknowns.

### 8.3 Parametric block certificate

*Done (sk-05, 2026-10-14).* Defined in `lib/certdef.bend`, the six
`cert_*` statements proven in `lib/certpf.bend` (laws in `LAWS.bend` until
the sk-06 review, when the trusted claim moved to the sketch level and
these became lemmas); the checker is `lib/cert.bend`. `tests/cert_demo.bend`
(gated) runs the checker inside Bend's own checker on a real circle-circle
block over the dyadics: it accepts the certificate and rejects an
off-center one. Natively it also rejects six other bad certificates
(q = 1, Y = I, a center too coarse for its radius, a negative radius, one
equation for two unknowns, a stray variable). Replacing any of the
checker's conditions by an unrelated one, or the whole checker by "accept",
makes the proofs fail. (While the laws were open, `tools/stmtcheck.py`
type-checked their statements: checking a file with open laws stops at the
count of open laws before type-checking.)

**The block.** Equations `eqs` that must vanish (`QExpr`) and the number n
of unknowns (as many as equations). A block numbers its own variables:
0..n−1 are the unknowns and n, n+1, ... the parameters, so f(y; z) is the
equations evaluated at y (fitted to n entries) followed by z. Composition
(§8.4) maps a block's numbering to the sketch's with one substitution law
(replacing each local variable by its sketch variable gives the same value
at the gathered assignment). This replaced global indices in the reviewed
draft (2026-10-14): same meaning, a smaller trusted spec, no `setv`, no
index-overlap checks, and `cert_local` holds by construction.

**The certificate,** in the checker's numbers K (Q17): a center ỹᵢ and a
radius rᵢ for each unknown, a factor q, Y ≈ J_y⁻¹ (a row per unknown), and
a center and radius for each parameter. Per-unknown radii make B
a box, as in interval Newton methods, so blocks that mix scales still
certify. A point of B has exactly as many entries as the center (and a
radius past the end of the list is 0), so B has exactly the block's
dimension. (Stating the length, rather than relying on zero radii past the
end, keeps every vector inside the proofs at length n, so vector identities
are plain list equalities; 2026-10-14.) (The first draft used one radius and plain list norms; the audit
showed `cert_contract` was then false: a coordinate past the unknowns
passes through N unchanged and never contracts.)

**The laws.** For every ordered field F and every map H : K → F (a ring map
with sound comparisons), if `check(b, c)` passes, then for every z in the
parameters' box (`pinned`), with N(y) = y − Y·f(y; z) and
B = {|yᵢ − ỹᵢ| ≤ rᵢ} (all certificate numbers sent through H):
- `cert_factor`: 0 ≤ q < 1;
- `cert_center`: ỹ ∈ B (B is not empty);
- `cert_self`: N maps B into itself;
- `cert_contract`: if s ≥ 0 and |y₁ᵢ − y₂ᵢ| ≤ s·rᵢ for all i, then
  |N(y₁)ᵢ − N(y₂)ᵢ| ≤ q·s·rᵢ for all i (contraction in the r-weighted
  infinity norm, stated without division);
- `cert_fix`: a fixed point of N in B is a zero of f;
- `cert_unique`: B holds at most one zero of f.

In a complete ordered field these give exactly one zero of the block in B
for each choice of the parameters: Banach's theorem, proven in Bend (Q18,
§8.4).

**The checker (proposed; it is not part of the statement).**
1. *Shape (each line is a way a naive checker would accept a bad
   certificate; the audit has the counterexamples):*
   - n = len(`eqs`); Y has n rows of at most n entries; every
     identity matrix has size n, never len(Y);
   - len(ỹ) ≤ n, len(r) ≤ n, every rᵢ ≥ 0, every parameter radius ≥ 0;
   - len(pc) = len(pr);
   - every constant is held by K (`ofq` returns `Some`, Q19); never
     rounded. K = ℚ holds all of them; K = D holds those with a
     power-of-two denominator.
2. *Slopes (Q12, proposed):* for each equation, a telescoping slope s with
   f(X₁) − f(X₂) = s·(X₁ − X₂), built over the expression tree by
   ab − a′b′ = a(b − b′) + b′(a − a′). It is exact for any polynomial and
   any degree, and needs no change to the IR. At X₁ = X₂ = X̃ it is the
   Jacobian J₀.
3. *Ball arithmetic in K:* each slope entry is evaluated with both arguments
   ranging over the box (unknowns within rᵢ, parameters within their radii),
   as a center and a radius: (a, ρ) + (b, σ) = (a + b, ρ + σ),
   (a, ρ)·(b, σ) = (ab, |a|σ + |b|ρ + ρσ). This is exact in K (no rounding)
   and gives J₀ and Δ with |S − J₀| ≤ Δ entrywise over the box.
4. *Conditions,* exact in K, componentwise (entries combined before any
   maximum is taken, which is never looser than a sum of norms and saves
   bits, §8.5). With G = |I − Y·J₀,y| + |Y|·Δ_y:
   - (G·r)ᵢ ≤ q·rᵢ for every i, and q < 1;
   - |Y·f(X̃)|ᵢ + (|Y|·(|J₀,z| + Δ_z)·ρ)ᵢ + (G·r)ᵢ ≤ rᵢ for every i, the
     sensitivity form the spike found tighter than ‖Y‖·L_z·ρ (1–1.5 bits
     per step);
   - ‖I − J₀,y·Y‖ < 1 with I of size n, so Y is injective (for `cert_fix`).
   The checker is a conjunction of small Bool tests, each with its own
   soundness lemma in the `dcmp_sound.go` pattern, so a proof is not stuck
   on comparisons in an opaque K.

Slopes rather than selective quadratization, because they are as tight on
quadratics (the slope of x² is x₁ + x₂, the Jacobian at the midpoint), need
no aux variables for the cubic mirror form, and each proof is a short
induction over expressions: the slope identity (ring algebra in F) and
ball soundness (order algebra in F). The certificate carries q rather than
the checker computing it, so the laws can name it. Proof notes from the
audit: injectivity of Y and `cert_unique` need a lemma that a finite vector
in F has a largest weighted entry (built with `lt_total`); the qᵏ argument
would need an Archimedean F.

*Linear algebra as built (sk-04, `spec/mat.bend`):* vectors are lists read
with trailing zeros and matrices lists of rows, so (AB)v = A(Bv), (A + B)v,
(−A)v and Iv = v hold with no shape conditions. Two parallel copies: over
every ordered field F (where the contraction argument lives) and over the
dyadics (what the checker computes, exactly); `ofd` maps the second into the
first as a ring map, and every dyadic vector and matrix operation becomes
F's. Norms are computed on dyadics (‖A‖∞ = largest row sum of |aᵢⱼ|); in F
there are only bounds: `vbnd(v, s)` is ‖v‖∞ ≤ s, and `mmaj(M, B)` says M's
entries are at most |B|'s. The product law: ‖Mv‖ ≤ ‖B‖·s for M majorized by
B and ‖v‖ ≤ s, so a field matrix bounded entrywise by a dyadic one (the
Taylor bounds of J over the ball) is handled like a dyadic one.

### 8.4 Composition theorem (Q16, Q18)

Everything is proven in Bend (Q18). In every ordered field, by induction
over the blocks in order: each block's parameter balls contain the earlier
blocks' certified boxes (a comparison in K) and the pinned values, so the
`cert_*` laws apply to every assignment the earlier blocks allow, and
a block reads only its own unknowns and parameters, mapped to the sketch's
variables by substitution. In a *complete* ordered
field (an ordered field that is Archimedean and in which every Cauchy
sequence with a modulus converges; up to isomorphism only ℝ), Banach's
theorem, proven in Bend, gives each block exactly one zero in its box for
each choice of its parameters, and the induction gives exactly one exact
solution of the whole system in the product of the boxes. Cauchy
completeness alone is not enough: some non-Archimedean fields have it, and
there qⁿ never drops below an infinitesimal.

No complete ordered field can be built in Bend (ℝ has no decidable order),
so a mis-stated completeness axiom could make the theorem vacuous. Guard:
state the axioms in textbook form and check them against mathlib's ℝ in
Lean.

*As built (sk-05b, 2026-10-14).* `spec/real.bend` (trusted) states
completeness in Skolem form, the way `OField` states inverses: a
`Complete<F>` record holds `arch(x)`, a natural number above x, and
`lim(s, m)`, the limit of a sequence s that is Cauchy with modulus m
(|sᵢ − sⱼ| ≤ 1/(k+1) for i, j ≥ m(k)), which it approaches with the same
modulus. Sequences and moduli are Bend functions; proofs pass them, and
families of per-index facts, as template parameters (reusable, unlike plain
function arguments). The law `cert_exists` (LAWS.bend, proven in
`lib/banach.bend`): in every complete ordered field, a checked certificate's
box holds a zero of its block for every choice of the parameters in their
box. The proof iterates the Newton map from the center (cert_self keeps the
iterates in the box; cert_contract brings any two points of the box, which
are within 2 radii, q^k closer after k steps), so each coordinate is Cauchy
with an explicit modulus (Bernoulli's inequality and the Archimedean
property, `lib/real.bend`); the limits form a point of the box (closed
bounds pass to limits), within 2qᵏ radii of the k-th iterate, which the
Newton map moves by at most qᵏ·4q·rᵢ for every k: a fixed point, so a zero
(cert_fix). With cert_unique: exactly one. Weakening either completeness
axiom (the limit bound k+1 instead of 1/(k+1), or a trivial Archimedean
law) breaks the proof.

The Lean guard (`lean/`, run by `lean/check.sh`): `BendCad/Axioms.lean`
transcribes `OField` and `Complete` (and `sub`, `le`, `bnd`, `nat`, `eps`,
`cauchy`) and proves that mathlib's ℝ satisfies every axiom
(`axioms_consistent`), and that ℚ with its usual operations has no
`Complete` structure (`rat_not_complete`, via rational approximations of
√2), using only Lean's standard axioms. `tools/axcheck.py` parses both
sides into one normal form and compares them field by field (planted
transcription errors are caught); `nat`, a two-case match, is compared by
eye. `tests/sqrt5_demo.bend` (gated) uses the law: from the circle-circle
certificate, every complete ordered field has a positive b with b² = 5. (The first plan here, approximate solvability in every F with the
step to ℝ on paper, is replaced; it would need two more laws: a
quantitative `cert_fix` and a bound on how N moves with the parameters.)

*Composition as built (sk-06, 2026-10-14; statements reviewed by Danielle
the same day, now in `LAWS.bend`).* The
composed claim mentions only the system's equations, a box (a center and a
radius per variable in K; radius 0 pins a variable) and the side
conditions (`spec/box.bend`: `inbox`); the plan is input to the untrusted
checker and never appears in it. Three laws, in `LAWS.bend`, proven in
`lib/planpf.bend`:
- `plan_exists`: in every complete ordered field the box holds a solution;
- `plan_unique`: in every ordered field it holds at most one (list
  equality of the two assignments);
- `box_sides`: every point of the box meets the side conditions the
  checker certified (ball enclosure of each side over the box, its lower
  end > 0 or ≥ 0, compared in K).

The checker (`lib/plan.bend`) reads the system in block order: variables
0..np−1 pinned, then each block's n unknowns and n equations in turn;
parameters are a sparse list of earlier variables, renumbered locally
after the unknowns. Per block it checks: the equations use only earlier
variables and its own unknowns; the renumbered block's certificate passes
`check`; the certificate's box is the plan's box on the block's unknowns;
each parameter ball contains the plan's box on that variable
(|c_v − pc_k| + r_v ≤ pr_k); blocks end within the box, and blocks,
equations and variables run out together. Proofs: a substitution law
(renumbered equation at y ++ z equals the original at p ++ y), prefixes
(later blocks leave earlier equations' values), and induction over the
blocks with cert_exists / cert_unique. Tested on a two-block chain
(`tests/plan_demo.bend`, gated; six malformed plans rejected natively).
A system in any other order is read through two lists in the plan: vp
names its variables in block order and ep its equations. The checker
requires every variable and equation to appear in its list, every listed
one to exist, and every equation to use only the box's variables; the
lists need not be permutations. Existence reads the block-ordered solution
back (variable v is the solution at v's position in vp); uniqueness maps
both solutions into block order. Tested on the chain renumbered (Q, A, P,
B; equations shuffled): accepted, and rejected with identity lists.

At the sketch level (two more laws in `LAWS.bend`): for a
well-formed sketch whose exact system `Sketch.eqs` has a checked plan and
whose `Sketch.sides` are checked over the box,
- `sketch_exists`: in every complete ordered field some x in the box has
  `Sketch.means(x, sk)` (circles and arcs proper, each driving constraint
  meaning what it says, sk-07);
- `sketch_unique`: in every ordered field at most one x in the box does.
Both also require the box to cover every variable the sketch names
(`spec/box.bend`: `Sketch.within`), since a lookup past the end of x reads
0: without it an empty box "certified" a sketch of two free points, both
put at the origin (found by an independent audit, 2026-10-14). Both are a
few lines from the plan laws with `sketch_sound` and `sketch_complete`
(`lib/meaning.bend`). "Exactly one" is given the radius-0 coordinates
(pins may be free degrees of freedom, §8.1); accept_sound (§11) reports
pins separately. These are the statements the end-to-end claim will
cite. While they were drafts, `tools/lawsync.py` (in the gate) checked
that ROADMAP's statements matched their gated restatements in `tests/`;
it does so for every future draft.

### 8.5 Precision and its cost

Each block's ball radius feeds the next block's parameter radius, so radii grow
down a chain: a 30-deep chain that roughly doubles error per step needs ~60
extra bits; ill-conditioned chains need more. This costs **bits, not size**.
Where it is too expensive the proposer **merges blocks**: a single centered
certificate over a merged block has no wrapping growth. Total certification
cost is near-linear in sketch size for typical sketches; the worst case is one
large cyclic block (O(k³) on k unknowns).

*Measured with the verified checker (sk-06, `proto/RESULTS.md`):* the
spike's depth-30 chains built as sketches (driving `Distance`
constraints), checked by `PL.check` on `Sketch.eqs` natively over the
spec's binary dyadics: 0.24–0.70 s, under 1 nm at depth 30 from P = 64
(well conditioned, ~0.8 bits per step) and P = 96 (flat, ~2.8 bits per
step); depth 300 in 14 s. Halving any one radius is refused, so the
generator's radii are within 2× of what the checker certifies. A limb K is
a speedup, not a blocker.

### 8.6 Side conditions over balls

*As built (sk-03, sk-06):* a side condition is e > 0 or e ≥ 0. The checker
(`check_sides`) encloses e over the box in a ball and compares its lower
end with 0 in K: > 0 for e > 0, ≥ 0 for e ≥ 0 (exact when e has no
variables, e.g. a dimension constant).

Signs, ranges and nondegeneracy (branch side, external/internal tangency, span
ranges, anchor orientations) are certified over the balls with exact Lipschitz
lower bounds, e.g. for quadratic g:
g(x) ≥ g(x̃) − ‖∇g(x̃)‖₁·r − ½·Σⱼₖ \|∂²g/∂x_j∂x_k\|·r². So the exact solution
has the same branches and orientations as the displayed one.

### 8.7 Redundancy

The independent subset is certified by §8.3. Each redundant constraint g needs
a **polynomial identity certificate** g·dᵐ = Σ hᵢfᵢ (d certified nonzero over
the balls), checked by the reflective normalizer.
- A library covers common structural cases (rectangle closure; parallel
  transitivity: cross(a,c)·\|b\|² = cross(a,b)·dot(b,c) + cross(b,c)·dot(a,b),
  with b ≠ 0).
- An offline Gröbner search (untrusted) finds rarer ones.
- Coincidental redundancy (two dimensions that merely agree) has no such
  identity. The constraint is dropped from the exact system and **flagged red**;
  the user deletes it, marks it driven, or fixes the sketch.

### 8.8 Singular configurations

Regular encodings and rewrite rules (§5) handle drawn configurations.
Near-singular blocks need more precision (radius shrinks) but still certify.
Exactly singular configurations cannot be certified. The proposer finds the
smallest dependent set of constraints in the failing block (rank analysis); those
are **flagged red** with the reason, and the rest of the sketch is certified.

### 8.9 Incrementality

Certification runs on commit (mouse-up, edit, load). Drag frames show the
proposer's output with the tolerance check (§6). Untouched blocks come back
bit-identical, so their certificates are reused; only touched blocks are
re-certified.

### 8.10 Nearest-ness (quality, optional certificate)

The proposer aims for the nearest solution (§10). Nearest-ness is a quality
property, not part of exactness. An optional certificate per touched component
proves an exact KKT point with positive curvature on the tangent space, in
Finsler/Debreu form: Tᵀ(H_L + ρJᵀJ)T strictly diagonally dominant with
positive diagonal (dyadic unit-triangular T, entries ~100–150 bits).

---

## 9. Guaranteed digits (Boehm-style display)

Any measured quantity (driven dimension, distance, coordinate, area) is shown
with digits that are guaranteed correct for the exact solution, and more
digits are available on demand by refining the relevant block certificates
(Newton steps at higher precision, smaller radius). Display never shows a digit
that might change; truncation is exact.

---

## 10. Proposer (verified)

Danielle, 2026-10-14: "we don't want untrusted proposer, we want trusted
everything". The solver is Bend code with two kinds of law:

- **What it says is true (soundness).** Every answer is a law about the
  sketch, never about the solver's internals. *Certified:* the sk-06 laws
  hold for the returned box and the sketch with its red constraints made
  driven. *Red:* each red constraint comes with an over-determination
  witness (below). *Pins:* reported; uniqueness is given them (§8.4).
- **It says it when it should (completeness).** Each stage is proven to
  succeed where it should: the structure stage never fails; exact linear
  algebra returns an inverse or a kernel vector; and certification
  succeeds, at some precision, for a regular solution near the drawing.
  Completeness laws are drafted in ROADMAP.bend as open laws until they
  are proven, so a gap is visible rather than assumed.

Inside a stage, an algorithm may compute an answer and a checker verify
it (as `q_reduce` does), but only with a law that the check always passes
(a totality law), open in ROADMAP.bend until proven. The proposer is not
in the trusted base (§14): it is verified, and nothing it computes is
believed without proof.

### 10.1 Stages (sk-09)

1. **Front end.** `wf` is decided by a Bool function proven equivalent to
   `Sketch.wf` (sound for the claim, complete so that a well-formed
   sketch is never refused); coverage is `Sketch.within`.
2. **Structure** (§8.1, §8.2). Incidence is syntactic occurrence of a
   variable in an equation. Matching by augmenting paths (Kuhn): a failed
   search from equation j visits equations S_j and variables W_j, every
   variable of S_j lies in W_j, and |W_j| = |S_j| − 1. That is a Hall
   violator, a fact about the equations alone, so it stays true however
   the matching changes afterwards: the equations S_j constrain fewer
   unknowns than they have equations. Each unmatched equation's constraint
   is flagged red (made driven) with its S_j; unmatched variables are
   pinned at their displayed values. *As built:* the search is
   depth-first recursion whose fuel bounds only its depth (each level
   visits a new matched variable, so 1 + nv suffices, by pigeonhole); the
   red stage walks the constraint records as `Sketch.eqs` and `owners`
   do, matching each constraint's equations as a unit; the pins are the
   variable side's failed searches (latest variables first, so the
   earliest are pinned) over the equations the red stage matched, worked
   out in the sketch's numbering and renumbered for the kept system. Each
   failed search's visited equations stay visited in every later search
   (dead: no augmenting path passes through them), which changes no
   answer and makes the variable side's maximality provable: its pins
   always make the kept system square (`lib/maxpf.bend`).
   Blocks are the strongly connected
   components of the matched dependency graph, in dependency order. Each
   block is validated as it is emitted (its equations use only earlier
   variables and its own unknowns, as many as its equations), and
   anything left over merges into one block, so the stage is total
   whatever the component search does; the search only decides block
   sizes, i.e. cost and precision.
3. **Numbers** (§8.3, §8.5). Per block, in order: dyadic Newton at a
   working precision P from the displayed values, with the parameters at
   their centers; J⁻¹ by exact Gauss–Jordan over ℚ, which returns either
   an inverse (J·Y = I, checked) or a kernel vector (J·v = 0, v ≠ 0,
   checked: a singular block, flagged with its evidence, §8.8); Y rounded
   to ~32 significant bits; radii from the §8.3 conditions with the
   parameters' radii from earlier blocks (what `tools/gen_plan_chain.py`
   computes today, in Bend). On failure the whole plan is redone at 2P, up
   to a bound. No F32 on this path: completeness cannot rest on F32,
   which is axiomatic; F32 may later supply first guesses.
4. **Check.** The plan, the side conditions, wf and coverage go through
   the verified checkers; only then is the answer Certified.

### 10.2 Laws (drafts in ROADMAP.bend, for review)

*As built (2026-10-14).* `solve(sk, g0)` (`lib/solve.bend`) is
`seal(search(sk, g0))`: `search` runs the stages, and `seal` recomputes the
verdict from the answer alone (every pin held at its drawn value with
radius 0; every red constraint explained; the sketch less the red
constraints well formed, covered by the box, its plan and side conditions
checked). The laws follow from the verdict and the sk-06 sketch laws, so
they hold whatever the search did (`lib/solvepf.bend`; restated with
proofs in `tests/solve_laws.bend`). Trusted additions: `spec/solve.bend`
(`mark`: constraints at given positions made driven; `owners`; `overdet`,
a Hall violator: distinct equations of the system whose variables all lie
in a shorter list; `explained`; `held`).
- `solve_exists` / `solve_unique`: when ok, the conclusions of
  `sketch_exists` / `sketch_unique` for `mark(red, sk)` and the returned
  box, read through any ring map H from the dyadics into F (`KI.demb` is
  one; `e_ofq` makes all agree on every dyadic).
- `solve_red`: each red constraint owns an equation of an over-determined
  set made only of its own and kept constraints' equations, so restoring
  any one red constraint over-determines what was kept: no red flag is
  spare.
- `solve_pins`: each pin has radius 0 and its center is its drawn value.
- `solve_total` (**proven 2026-10-14**, `lib/totalpf.bend` over
  `lib/dfspf.bend`, `lib/redpf.bend`, `lib/wfcpf.bend`, `lib/covpf.bend`,
  `lib/maxpf.bend`, `lib/listpf.bend`; restated in `tests/solve_laws.bend`;
  the pins fallback removed the same night, once `lib/maxpf.bend` proved the
  variable side's matching maximum): for a well-formed, covered
  sketch, whatever the drawing and budget, the reported red constraints,
  reasons and pins are the sketch's own (`red_of`, `why_of`, `pins_of`
  depend on the sketch alone); the red ones are explained; the marked
  sketch passes the solver's wf check; the pins are distinct variables;
  and the kept system is square once the pins are held.
- `solve_complete` (open, drafted 2026-10-14; the hard one): in a complete
  ordered field, a point x with one entry per variable that is the drawing
  g0 at the pins, solves the sketch less its red constraints, meets its
  side conditions strictly (a variable-free ≥ 0 may hold with equality),
  and is a regular point in the free variables (`spec/deriv.bend`: the
  Jacobian of symbolic derivatives has a two-sided inverse, entrywise),
  for a sketch whose constants are dyadic: there are d > 0 and a budget b
  such that from every drawing within d of x that agrees with g0 at the
  pins, `solve_b` certifies with x in its box. A Newton–Kantorovich
  argument with rounding, stated qualitatively. `tests/regular_demo.bend`
  shows `Regular` holds (in ℚ, at a 3-4-5 point): the first draft compared
  matrices as lists, and `M.ident` omits trailing zeros, which made the
  law vacuous; caught before review.
- The completeness audit (fresh agent, 2026-10-14) found the first draft
  false, with two counterexamples run natively: side conditions were
  checked only after the precision loop (a circle of radius 2⁻⁷⁰ rounded
  to 0 at 64 bits and was never retried), and every budget began at 64
  bits, where rounding lost the drawing's detail and certified a
  neighbouring root 2⁻⁶⁵ away. Fixed: the loop takes the first precision
  whose answer passes the whole verdict, and a *level* replaces the
  budget (`solve_l(sk, g, l)`: seven precisions from the l-th; `solve` is
  level 0, 64 .. 512 bits; a higher level is "try harder" and never tries
  the coarse ones). Both counterexamples now behave (the root at level ≥
  3, the radius at level 0). solve_total: nothing found. Its note, now in
  the law's comment: regularity is in the free variables the solver
  chose structurally (a point on a vertical line whose only unknown is
  the line's far end is singular there though the sketch is fine); pins
  chosen numerically would close that.
- To make `solve_complete` true the solver also changed: a level (as
  above); Newton settles within 4 ulps (an
  exact fixed point can be missed forever near a rounding midpoint) and
  fails a precision on a step longer than 2⁴⁰ nm; elimination at P + 32
  bits and Y at P/2 bits, so both grow with P; every failure moves to the
  next precision (stopping at a low precision broke completeness for
  ill-conditioned blocks). The price: refusing an impossible sketch costs
  every precision of the budget (the 3-point demo: 0.4 s at budget 2,
  11 s at 7). Faster refusal would need a proven infeasibility
  certificate (§8.7, sk-13) or a smaller interactive budget with "try
  harder".

How the stages meet the laws: red constraints are found by matching
constraints as units, in order (all of a constraint's equations or none;
a failure rolls the matching back), so a witness passes only through kept
constraints and the red one; the first version matched equation by
equation and over-flagged (the independent audit found a midpoint sketch
where it dropped a user's `Fix` beside the redundant midpoint; regression
in `tests/solve_demo.bend`). Pins are the variables a second matching
(variables to the kept equations, latest variables first) leaves free:
the earliest-drawn variables.

Measured: the depth-30 chains certify end to end in Bend from a drawing
rounded to whole nm, as tightly as the Python generator (well P = 96:
last radius 2⁻⁷⁴ nm; flat P = 96: 2⁻¹¹ nm), ~2 s per precision
natively; inside Bend's checker, solving the circle demo takes ~4 s.
Not yet claimed: where the box lies relative to the drawing (a mirrored
branch is possible), a red constraint's deviation at the solution (sk-19),
a witness for each pin (a variable-side Hall violator: the same
machinery), and which solution (§10.3).

### 10.3 Which solution (ink metric, a later stage)

v1 solves with the free degrees of freedom pinned at their displayed
values and Newton started from the drawing. Least ink displacement (D13)
replaces that with a KKT solve, verified in the same way, with the
optional nearest-ness certificate of §8.10:

- **Objective: least ink displacement (D13).** Each drawn curve, construction
  geometry included, is treated as ink; the cost is ∫ \|γ_new − γ_old\|² over
  the old curve's arc length, with points matched by their natural parameter.
  Closed forms:
  - segment: L·(\|ΔP\|² + ΔP·ΔQ + \|ΔQ\|²)/3, L the old length;
  - circle: 2πr·(\|ΔC\|² + Δr²);
  - B-spline: a quadratic form in the control-point moves (mass matrix
    ∫BᵢBⱼ), weighted by the old curve's speed at fixed quadrature nodes;
  - bulge arc: fixed quadrature along the arc;
  - standalone point: \|ΔP\|² times a nominal length (default 1 mm).

  The total is a convex quadratic in the displacements, so W becomes a
  block-sparse positive definite matrix instead of a diagonal. Consequences:
  long things cost more to move; sliding a curve along itself still costs
  (points are matched by parameter; a shape-only metric would be nonconvex).
- **KKT** with an active set and LM damping. Generically nonsingular; known
  singular cases (drag target at a circle's center; rank lost exactly at the
  solution) are handled by damping.
- **Aux variables** (contact points, parameters, aux lengths) carry no ink; they
  get a tiny positive weight (e.g. 2^−20 relative) for nonsingularity. Drag:
  cursor target with a large weight, or a hard equality (option).
- **Outputs:** displayed grid geometry, pins, block order, per-block (ỹ, Y, r),
  red constraints with witnesses, redundancy certificates, partition and
  anchors.
- **Projected continuation** for large edits; flips detected by anchor signs.
- **Reference (not a dependency):** neoscad/sketch-solver.

### 10.4 Proving `solve_complete` (plan, 2026-10-14)

**Shape.** Choose the level l first, so that its first precision P is
large, then d ≤ 2^-P. At P the plan succeeds and the whole verdict passes,
so the loop stops at its first precision and the answer is P's. x is then in
the box by local uniqueness: `lib/solvepf.bend`'s `exists_of` gives a
solution x' in the box, the box agrees with x at the pins and lies within
O(2^-P) of it elsewhere, and a solution that close to a regular one with the
same pins is that one (with Z the Jacobian's inverse,
0 = f(x') − f(x) = S (x' − x) gives |x' − x| ≤ |Z| |S − J| |x' − x|, at most
half of |x' − x|). `Complete` is used twice: `exists_of` (Banach) and
`arch` (to choose P).
*(Superseded by C5, 2026-10-17: `block_ok` puts x_b in each block's box
directly (|yc − x_b| ≤ (65/64) S ≤ r), so C6 needs neither local
uniqueness nor `exists_of`; `Complete` is used only through `arch`.)*

**Ingredients.**
1. *Structure (the sketch alone).* vp lists the pins and then each block's
   unknowns, a permutation of the variables; ep lists the kept equations
   block by block, a permutation; a block's equations use only pins,
   earlier unknowns and its own (blocks are checked as they are emitted,
   and what is left becomes one block, which is valid because Tarjan's
   components partition the kept equations: (6)); a block's pars are
   exactly the earlier variables it uses. So every non-numeric part of `PL.check`
   holds by construction, as do `held`, `within` and the shape checks;
   `explained` and `wf_dec` are solve_total's.
2. *Linear algebra in F.* Gauss–Jordan over F, deciding pivots with
   `lt_total`, proves the finite-dimensional dichotomy: a square matrix is
   either invertible on both sides or has a nonzero kernel vector. From it:
   the Jacobian in block order is invertible (Regular permuted; injectivity
   does not see the order); a block lower triangular invertible matrix has
   invertible diagonal blocks (the last one is injective directly; for the
   first, a kernel vector extends to one of the whole by solving the rest);
   a matrix near an invertible one is invertible, with at most twice its
   inverse's norm.
3. *One block at P.* Let x_b be the block's unknowns at x, which solve its
   equations at x's parameters x_z, and let Z_b be its Jacobian's inverse
   there. The parameters' centers pc are earlier centers, within τ of x_z.
   Write θ = 2^-P/2.
   - Newton: every inverse A it uses has |I − A J| ≤ θ (5).
     From the drawing (within 2^-P), one step lands within
     O(τ) + 2^-P-1 + O(θ 2^-P) of x_b. The next step moves at most
     2^-P + O(θ (τ + 2^-P)), so Newton has settled by its second step,
     never singular and never far.
   - Y is J at the center, inverted the same way and rounded to P/2 bits:
     |I − Y J| = O(θ).
   - Radius: the checker's Jacobian centers are exactly J at the box's
     center (a ball product multiplies the centers), and its radii are
     O(r + ρ). So any small r ≥ 2 s0 (s0: the self-map bound at radius 0)
     passes contraction, self-map and injectivity. The twelfth radius
     tried, ≥ r0 (17/16)^12 > 2 s0, is one, so the search returns a radius
     no larger, and the block's center error and radius are both
     O(τ + 2^-P).
   - Blocks in turn: τ for a block is the largest earlier center error, so
     after the last block everything is within C 2^-P for a C fixed by x
     and the sketch, and `arch` gives a P that makes every "small" true.
4. *Side conditions.* Each holds strictly at x (Strict). A side
   condition's ball is its value at the box's center, give or take
   O(radius), so it passes once the box is small; a variable-free ≥ 0 is
   computed exactly.

5. *Rounded elimination, analysed.* The dyadic Gauss–Jordan at w = P + 32
   bits, partial pivoting and all. By induction over the columns, the
   computed rows are T [J | I] up to δ, where T is the exact product of the
   row operations it performed (its own reciprocals and multipliers). The
   entries stay below G, T has an inverse of norm at most H, and the
   finished columns are unit vectors up to δ. The pivot stays at least μ: if
   every candidate in the column were smaller, e_c minus the finished
   columns' entries would be a near-kernel vector of J, and J is invertible
   with |J⁻¹| ≤ β. So elimination never meets a zero column. At the end
   |I − A J| ≤ n δ (2 + |J|), with δ ≤ K 2^-w for a K explicit in n, |J|
   and β. No Schur complements and no growth-factor theorem: partial
   pivoting is used only to say the pivot is the column's largest entry.
6. *Tarjan partitions.* Every equation reached is either on the component
   stack or in exactly one emitted component. The fuel covers one step per
   root, per edge and per finish. When a search from a root finishes, the
   root's low is its own index (everything above it on the stack is
   younger), so it pops the whole stack. Hence the components partition
   the kept equations.

**The solver as it runs.** No changes. (An earlier draft of this plan
proposed two: a residual-checked inverse with an exact fallback in place of
(5), and a partition check in place of (6). Danielle preferred proving the
solver as it stands, and both are provable.)

**Milestones** (each one a checked file with the gate green):

| | file | contents |
|---|---|---|
| C1 | lib/gjpf.bend | **done 2026-10-14**: Gauss–Jordan over F (the dichotomy), injective ⇒ invertible, Regular's inverse of any shape ⇒ one with n rows, block triangular; on lists of rows, with the row operations kept as a history so injectivity is a lemma (permutation moves to C2, perturbation to C3) |
| C2a | lib/tarjanpf.bend | **done 2026-10-14**: Tarjan partitions (6), the solver's tarjan unchanged (`comps_part`: the components are distinct and hold exactly the equations they start from); gated via tests/struct_laws.bend |
| C2b | lib/structpf.bend | **done 2026-10-15** (`struct_ok`): the variable side's end: it saturates the kept equations, and pins and matched variables are all the variables, disjoint; blocks: their equations are the components' (`alleqs = cats`), each block valid (checked ones by the check, the rest by the partition); vp and ep permutations; `swalk`: PL.walk's structural conjuncts for the solver's skeleton (sizes, `pars_ok`, `eqs_below`, every variable a block uses is its own unknown or a par, the end at nv) |
| C2c | lib/keptpf.bend | **done 2026-10-15** (`kept_good`, `kept_len`, `kept_reorder`; lib/redpf.bend's end result now also says no matched equation is owned by a red constraint, and all are below the equation count): kept vs good: the kept system is the full system at the indices good (the red stage matched exactly the equations whose constraint is not red: `pre` at the end plus the count) |
| C2d | lib/permpf.bend | **done 2026-10-15** (`regular_blocks`: InvN of jac(x, full picked at alleqs bs, allvars bs)): Regular in block order: a kernel vector of the Jacobian with permuted rows and columns gives one of the original (sums reindexed over a permutation), so with C1 the block-order Jacobian has an inverse |
| C3a | lib/bndpf.bend | **done 2026-10-15** (`mcen_jac`, `kball_grade`, `ksl_grade`, `eval_lip`, `sl_lip`, `deriv_rnv`, `deriv_rename`; gated via tests/bnd_laws.bend): balls: centers are values (slope at equal points = deriv), ball tightness, Lipschitz bounds for expressions and slopes; renaming commutes with deriv (plan below) |
| C3b | lib/roundpf.bend | **done 2026-10-15** (`div_ok`, `zfloor_ok`, `dround_err`, `dsig_err`, `qsig_err`, `dsigup_ok`; gated via tests/round_laws.bend): rounding in F: dround, dsig, qsig, dsigup (plan below) |
| C3c | lib/normpf.bend | **done 2026-10-15** (`mv_n`, `InvB`, `lowb`, `pert`; gated via tests/norm_laws.bend): norms and the perturbation lemma (plan below) |
| C4 | lib/dgjpf.bend | **done 2026-10-15** (`dinverse_ok`, `pivot_ok`, `kern`, `col_full`, `dgj_ok`; gated via tests/dgj_laws.bend): the rounded elimination (5), the solver's dinverse as it runs: Newton's and Y's inverses are good (plan below) |
| C5 | lib/apxpf, nwtpf, radpf, blockpf.bend | **done 2026-10-17** (`newton_ok`, `window_ok`, `rs_init`, `inbox_ok`, `block_ok`; gated via tests/block_laws.bend): one block at P (3), the solver's block as it runs (plan and "C5 as built" below) |
| C6 | lib/completepf.bend | the blocks in turn (each block's rb is later blocks' ρ; pins radius 0), the plan check and the verdict, choosing l (then d ≤ 2^-(P_l+1)): `solve_complete`. C5 puts x_b in each box directly, so no uniqueness or Banach step is needed here. Needs (2026-10-17 audit): block_ok's smallness hypotheses in scale form (d ≤ h, ρ ≤ R h), per-block InvB from regular_blocks, SK.Zeros → fvals = zeros, balls through dpick/zmap, kle(|c − c| + r, r) for pcont, arch for 2^-p |

**C3 plan** (2026-10-15). One idea carries C3a: F is its own computing
numbers. `fnum(F)` compares by `lt_total` and holds every rational, and
the identity is an `Emb<fnum(F), F>`, so every K-generic ball lemma
(kball.bend's `ball_ok`, `sl_ok`) also holds for balls centered at points
of F, such as the solution x. Tightness is then proved once, generically
in K, and serves both the checker's dyadic balls and the Newton analysis.

- C3a, lib/bndpf.bend:
  - `fnum`, `femb`, `held_f` (every expression's constants are held in F).
  - Centers: `kball_c` (H of kball's center is e at the box's centers),
    `ksl_c` (H of ksl's center is sl(i, X, X, e)), `sl_deriv`
    (sl(i, X, X, e) = eval(X, deriv(e, i))). So the checker's slope
    centers are exactly the Jacobian at the box's center, whatever the
    radii; numer's `jac` is the radius-0 case.
  - Grades: F values mj(B, e), lp(B, e) (an expression's magnitude and
    Lipschitz constant) and ms(B, e), ls(B, e) (its slopes'). A ball (c, r)
    has grade (M, L) at ρ when 0 ≤ r, |c| + r ≤ M and r ≤ L ρ. badd, bneg
    and bmul combine grades. A box whose balls have |c| + r ≤ B and r ≤ ρ
    gives kball(e) grade (mj, lp) and every ksl(i, e) grade (ms, ls)
    (`kball_grade`, `ksl_grade`: ball tightness).
  - Lipschitz, in fnum(F): for X1 and X2 in an F-box of grade (B, ρ) with
    centers X*, |e(X1) − e(X*)| ≤ lp ρ and
    |sl(i, X1, X2, e) − sl(i, X*, X*, e)| ≤ ls ρ, with |e(X1)| ≤ mj and
    |sl| ≤ ms.
  - Renaming: deriv commutes with PL.rnv (vp distinct, v in vp) and with
    PL.rename (v an unknown, pars distinct).
- C3b, lib/roundpf.bend, in F through ofd:
  - |dround(x, p) − x| ≤ 2^-(p+1).
  - |dsig(x, b) − x| ≤ 2^-b |x|.
  - |qsig(q, b) − q| ≤ 2^-b |q| (so dsdiv too).
  - x ≤ dsigup(x, b) ≤ x + 2^(1−b) |x| (any sign).
  - From integer facts: Euclid's division (QRD.div), the size bounds
    2^(size p − 1) ≤ p < 2^(size p), and pshr as a floor.
- C3c, lib/normpf.bend:
  - Norms as F values: ‖v‖ the largest |entry|, ‖A‖ (over n columns) the
    largest row sum of |entries| among the first n columns, so
    ‖A v‖ ≤ ‖A‖ ‖v‖ for v of length n (`mv_n`).
  - "J has an inverse of norm at most c" is Data (`InvB`: the inverse, its
    n rows, the bound), reusable as ‖v‖ ≤ c ‖J v‖ (`lowb`).
  - Perturbation (`pert`): with InvB(J, n, β), ‖J' − J‖ ≤ δ and 2βδ ≤ 1,
    ‖v‖ ≤ 2β ‖J' v‖, so J' is injective, so by C1 invertible; each row of
    its inverse, read against the signs of its own entries, sums to at
    most 2β (rows walked as `mdrop(k, Z')`), so InvB(J', n, 2β).

**C4 plan** (2026-10-15). `dinverse(n, w, a)` for a dyadic n × n matrix
J = a (rows of n entries) that is invertible in F, InvB(J, n, β) (C3c),
with entries |J_ij| ≤ g, returns some A with ‖I − A J‖ ≤ K 2^-w, for an
explicit K from n, g and β, once 2^-w ≤ ε for an explicit ε > 0.

- One column step (dgj at column c, pivot row r): swap rows c and r; s =
  the rounded reciprocal of the pivot (qsig); the pivot row becomes
  p = rounded s · row c; every other row i becomes rounded(row_i −
  rounded(m_i p)) with m_i = row_i[c]. Exactly: S' = O (P S) + E, with P
  the swap, O the elementary operation (row c times s; row i minus
  m_i s row c), and E bounded entrywise by 2^-w times the entries' sizes
  (C3b's dsig_err and qsig_err).
- Invariant after c columns, with constants G_c, Δ_c, φ_c, H_c defined by
  recursion on c. The rows are [L | R] (left n entries, right n).
  - (a) Every entry is at most G_c in size.
  - (b) The defect L − R J is at most Δ_c entrywise. The same operations
    act on it, plus the rounding.
  - (c) The finished columns are nearly unit vectors:
    |L_ij − [i = j]| ≤ φ_c for j < c.
  - (d) InvB(R, n, H_c). We have (O P R)^{-1} = R^{-1} P O^{-1} with O^{-1}
    explicit (row c times 1/s; row i plus m_i row c), and C3c's pert
    absorbs the rounding.
- Pivot. Partial pivoting takes the largest |S_rc| over r ≥ c. Suppose
  every candidate were below μ_c. Then v = e_c − Σ_{j<c} L_jc e_j has
  |L v| = O(μ_c + φ_c G_c), because the finished columns are nearly unit.
  Also R J v = L v − D v and |v| ≥ 1, so 1 ≤ |v| ≤ β |J v| ≤
  β H_c (|L v| + n Δ_c |v|), which is false once μ_c and the errors are
  small. So the pivot is at least μ_c > 0, elimination never meets a zero
  column, and |s| ≤ 2/μ_c.
- End (c = n): A = R, and |I − A J| ≤ |I − L| + |L − R J| ≤ n (φ_n + Δ_n).
  Every error constant is K_c 2^-w and every "small" is 2^-w ≤ ε_c.
  solve_complete reaches w = P + 32 with P large through arch.
- Split:
  - C4a: the exact step algebra (swap, O and O^{-1} as matrices; how the
    defect and the finished columns transform).
  - C4b: one rounded step's errors (dscale, daxpy and dsdiv through dsig
    and qsig).
  - C4c: the pivot bound.
  - C4d: the induction over columns and the end bound for dinverse.

**C4 as built** (2026-10-15, lib/dgjpf.bend, ~2200 lines, ~3 s).
- Rows carry `rowinv(x, i, c, G, Δ, φ)`: length 2n, entries ≤ G, the
  defect x_k − R_x · J_col k ≤ Δ for k < n, and |x_j − [i = j]| ≤ φ for
  j < c. `rinv` holds it for every row (running index).
- The right halves R = `rmat(n, ·)` keep `InvB(R, n, H)`. The swap is
  `swap_invb`. The elimination step is `col_low`: inverting the step by
  hand gives |u| ≤ H |R u| ≤ H (A |R' u| + B |u|), where the pivot row
  needs |z| ≤ 2G |s z| (`piv_low`). A lower bound alone then gives InvB
  (normpf's `invb_of_low`).
- Pivot: `pivot_ok` shows dpivot returns a row bounding every
  candidate, or None only if all are 0. `kern` gives
  1 ≤ βH((cφG + m) + nΔ(1 + G)) from the near-kernel vector
  v = (−L_0c, …, 1, 0, …). So the pivot is ≥ 1/(2βH), |q| ≤ 2βH and
  σ = 4βH bounds the rounded reciprocal.
- Constants: `kst(n, g, β, c)` = (G_c, H_c, KD_c, KP_c), u-free, with
  Δ = KD u and φ = KP u. Each column needs u A_c ≤ 1 (`acoef`: the
  pivot, 2G|q|u ≤ 1, 2HB ≤ 1, u ≤ 1).
- `dinverse_ok`: dinverse(n, w, a) = Some A with n rows and every entry
  of I − A J at most (KD_n + KP_n) 2^-w (`dinv_res`/`agood`). The
  vector form |v − A J v| ≤ n(KD_n + KP_n) u |v| is left to C5.

**C5 plan** (2026-10-17). One block, in its own numbering (unknowns
0..n−1, then m parameters), the solver's `block(eqs, n, pc, pr, y0, p)`
as it runs. No completeness of F is needed here: x_b is shown to be in
the box directly, so C6 uses `Complete` only to choose P (arch).

- *Statement* (`block_ok`). Given x_b (n entries) and x_z (m entries)
  with f(x_b; x_z) = 0, InvB(J(x_b; x_z), n, β) for the Jacobian in the
  unknowns, the parameters' balls holding x_z (|x_z − pc| ≤ pr ≤ ρ
  entrywise), the drawing within d (|y0 − x_b| ≤ d), a magnitude bound bb
  (|x_b ++ x_z| + 1 ≤ bb), and constants Λ ≥ ls(bb, e), M ≥ ms(bb, e) for
  every equation e (C3a's slope grades), and the smallness hypotheses
  below: block returns BOk of a certificate (yc, r, Y, pc, pr) that the
  block checker accepts, with |yc − x_b| ≤ E_N, 0 ≤ r ≤ R and x_b in
  [yc ± r]. C6 feeds r back as the next blocks' ρ (pins have radius 0).
- *Notation.* h = 2^-(p+1) (Newton's rounding), u = 2^-(p+32)
  (elimination), v = 2^-⌊p/2⌋ (Y's rounding). P(y) = y ++ pc, g(y) =
  f(P(y)), J_y = J(P(y)). Every point visited lies within δ = d + ρ + E_N
  of x_b ++ x_z, so with 2βnΛδ ≤ 1, C3c's pert gives InvB(J_y, 2β), and
  |J_y entries| ≤ M. Each elimination at a visited point (C4) returns A
  with |I − A J| ≤ ε_A entrywise, ε_A = (KD_n + KP_n) u at (n, M, 2β).
- *Approximate inverses* (C5a). Vector form: |w − A J w| ≤ n ε_A |w|.
  Norm: J = J Z w-wise (Z the exact inverse), so |A w| ≤ α |w| with
  α = (1 + n ε_A) 2β; and by sign vectors (normpf's row walk, as a
  template "every |M s| ≤ c for |s| ≤ 1"), mnorm(A) ≤ α. Right defect:
  (I − J A) w = J (Zw − A J Zw), so mnorm(I − J A) ≤ nM n ε_A 2β. Y:
  |Y − A| ≤ v |A| entrywise (dsig_err), so mnorm(I − Y J) ≤ θ_L =
  n ε_A + v α n M and mnorm(I − J Y) ≤ θ_R = nM (n ε_A 2β + v α).
- *Newton* (C5b). Step k: y_{k+1} = y_k − A_k g(y_k) + ε_k, |ε_k| ≤ h.
  - Step 0. Since f(x_b; x_z) = 0, g(y0) = S0 (y0 − x_b) + T0 (pc − x_z)
    (slopes, unknown part then parameter part), so |g(y0)| ≤ G0 =
    nM d + mM ρ and |y1 − x_b| ≤ E1 = n ε_A d + α nΛ d² + α mM ρ + h
    (A0 S0 = A0 J0 + A0 (S0 − J0), |S0 − J0| ≤ nΛ d by C3a's sl_lip).
  - Step 1 settles even when ρ is many ulps: the parameter offset is
    common to both steps and cancels. With g0 = J0 w (w = Z0 g0),
    g(y1) = (J0 − S1) w + S1 (w − A0 g0) + S1 ε0, so |y2 − y1| ≤
    2h + n ε_A h + α nΛ Δ0 h + α (nΛ Δ0 + n² M ε_A) 2β G0 (Δ0 = α G0 + h),
    at most 8h = 2^-(p−2), the settle test, once the second-order terms
    are below 6h. So newton returns y1 or y2, within E_N = 8h + E1.
  - Control flow: nstep is Some (dinverse_ok), the 2^40 guard passes,
    and the settle test is decided by the bound (K-level comparisons are
    complete for dyadics: kle(a, b) = True from ofd a ≤ ofd b, by the
    embedding's cmp law and trichotomy).
- *Radius* (C5c). s0 = the checker's self-map vector at radius 0 (what
  r0 reads), S = max s0, r0 ∈ [(65/64) S, (65/64)(129/128) S].
  - Window: every r with 2S ≤ r ≤ U passes the checker, U =
    ((65/64)(129/128) + 2 (17/16)(129/128)) S. Centers of the checker's
    slope balls are the Jacobian at the box center (mcen_jac), so
    |I − Y J0y| ≤ θ_L; their radii are at most Λ (r + ρ) (ksl_grade);
    a new pair-grade lemma (radius over the radius-r box minus radius
    over the radius-0 box ≤ ls · r, same induction as ksl_grade) bounds
    svec(r) ≤ s0 + (2α mΛ ρ + θ_L + 2α nΛ (r + ρ)) r. Contraction (q =
    1/2), self-map and injectivity (θ_R < 1) follow.
  - Search: the first passing radius is reached by step 12
    ((65/64)(17/16)^12 ≥ 2); a radius that fails is below 2S (it is at
    most U), so the next is below 2 (17/16)(129/128) S ≤ U. So rsearch
    returns r ≤ U =: R.
- *In the box* (C5c). With e = yc − x_b, g(yc) = T δ + S' e, T the
  parameter slopes between yc ++ pc and yc ++ x_z (both in the radius-0
  box, so |T| ≤ |J0z| + Dz0 entrywise) and S' the unknown slopes from
  x_b ++ x_z: |e| ≤ s0 + κ |e| with κ = θ_L + 2α nΛ (E_N + ρ) ≤ 1/65,
  so |e| ≤ (65/64) S ≤ r0 ≤ r.
- *Smallness* (hypotheses of block_ok, discharged in C6 for large p):
  δ ≤ 1/4, U ≤ 1/4, 2βnΛδ ≤ 1, u acoef ≤ 1 per column (dinverse_ok),
  n ε_A ≤ 1, v ≤ 1, the settle inequality, the window inequality
  2α mΛ ρ + θ_L + 2α nΛ (U + ρ) ≤ 1/2, θ_R < 1, 65 κ ≤ 1, p ≥ 2.
- Split:
  - C5a lib/apxpf.bend: the vector form, |A w| ≤ α|w|, template
    operator bound → mnorm, right defect, Y's rounding, θ_L, θ_R; F-boxes
    for fnum (a center and one radius: gbox, inbox, cen); slope matrix vs
    Jacobian at the center (nΛ ρ), slope and Jacobian norms (nM); the
    dyadic Jacobian, values and dmatvec in F; complete comparisons
    (kle/klt/kvle/kvlt from F inequalities); every visited point's
    elimination (pert + dinverse_ok at J_y).
  - C5b lib/nwtpf.bend: nstep in F, steps 0 and 1, newton's control
    flow: `newton_ok`.
  - C5c lib/radpf.bend: pair grades, the window, r0 and grow bounds,
    rsearch, in the box.
  - C5d lib/blockpf.bend: `block_ok`.

**C5 as built** (2026-10-17; lib/apxpf.bend, lib/nwtpf.bend,
lib/radpf.bend, lib/blockpf.bend, ~11 s together; tests/block_laws.bend
restates pieces of each and block_ok in full, so the gate checks them).
- C5a and C5b as planned; `newton_ok` returns yc within E_N = 8h + E1.
- C5c, in lib/radpf.bend:
  - *Pair grades* (`kb_pd`, `ks_pd`): over two boxes with the same
    centers, radii r0 ≤ r1 ≤ r0 + dl, each ball's radius grows by at most
    lp·dl (values) or ls·dl (slopes); `mz_mn`: the parameters' |J0z| + Dz
    grows by at most m Λ r when the unknowns' radius goes from 0 to r.
  - *Window* (`window_ok`): every dyadic r with S ≤ r/2 and r ≤ r_b passes
    `okr` (shape, factor 1/2, contraction, self-map, injectivity), given
    |Y| ≤ y_n, |I − Y Jc| ≤ θ_L, |I − Jc Y| ≤ θ_R < 1, the box's grade at
    r_b (|Pc| ≤ bb − r_b, ρ ≤ r_b), and cw = θ_L + y_n n Λ r_b + y_n m Λ r_b
    ≤ 1/2. The self-map is compared entry by entry with radius 0:
    svec(r) ≤ s0 + (B(r) − B(0)) + G(r) − G(0), G(0) = 0, so every entry is
    at most S + cw·r ≤ r. The plan's α-form constants became y_n and r_b.
  - *Search* (`rs_init`): from r0 the solver's `rsearch` returns a passing
    r with (65/64) S ≤ r ≤ U = (17/16)(1 + 2^-7)·2S (given U ≤ r_b). The
    proof carries m, the steps still needed (R + m·S/16 ≥ 2S, m ≤ fuel,
    m = 16 at the start); a failing radius is below 2S by the window's
    contrapositive (`lt_total`), so the next is below U. Dyadic constants
    are compared in K (`kle_ok`); 16·(1/16) = 1 and 17/16 = 1 + 1/16 by
    @CERTEQ, so no large numeral enters F.
  - *In the box* (`inbox_ok`): |yc − x_b| ≤ (65/64) S given
    (65/64)(θ_L + y_n n Λ rad) ≤ 1/64, with rad bounding the distances of
    yc ++ x_z and x_b ++ x_z from Pc. The path is two-step: the parameters
    move first, inside the radius-0 box, so their slopes are bounded by
    exactly B(0)'s entries; then the unknowns move with the parameters at
    x_z, slopes S' within n Λ rad of Jc (`smat_lip_mn`). Per entry,
    |e_k| ≤ S + |e − Y S' e|.
- C5d, in lib/blockpf.bend: `block_ok`, following the solver's own
  matches (newton → block.y → dinverse → block.y2 → ysig → block.ym →
  rsearch → block.r), each computed result passed to a lemma that
  matches it. Its outcome predicate `bgood(n, eqs, x_b, rb, ·)`: BOk of a
  certificate the block checker accepts, |x_b − yc| ≤ yr entrywise,
  0 ≤ yr ≤ rb. The constants are explicit in the given ones (yn =
  (1 + v) α, θ_L = n ε_A + v α nM, θ_R = nM (n ε_A 2β) + nM v α, S̄ =
  yn (nM E_N + mM ρ) + yn mM ρ bounds S, r_b = (17/16)(1 + 2^-7) 2S̄ + ρ),
  and the smallness hypotheses beyond C5b's are w1 dx + r_b ≤ 1, w2 θ_R <
  1, w3 the window's cw ≤ 1/2, w4 (65/64)(θ_L + yn nΛ dx) ≤ 1/64.
  C6 discharges them for large p.

**C6 plan** (2026-10-17). The solver as it runs: solve_l = seal(search_lw);
at level l the loop's first precision is P = P_l (64, 96, 128, 192, ...),
and if P's answer passes the whole verdict the loop returns it and ok is
that verdict. So it is enough to show plan(kept, nv, skel_of(sk), g, P)
is POk and accept is True at P, for every g within d of x.
- *Scales.* h = 2^-(P+1), u = 2^-(P+32) ≤ h, t = 2^-⌊P/2⌋ (Y's v) with
  h ≤ t ≤ 1. Take d ≤ h. Every block constant of C5 is a polynomial with
  nonnegative coefficients in the small quantities (d, ρ, h, u, v) and
  fixed ones (n, m, β, Λ, M, C4's KD and KP, dyadic constants), and every
  smallness hypothesis is "such a polynomial with no constant term is at
  most a constant".
- *C6a, scale form* (lib/pmono.bend, lib/scalepf.bend). Monotone
  polynomials, reflected: an expression type over atoms with `peval` in
  F; with each atom 0 ≤ a_i ≤ c_i (fixed) or ≤ c_i t (small), 0 ≤ t ≤ 1:
  peval(P, a) ≤ peval(P, c), and ≤ t peval(P, c) when every monomial has
  a small atom, t² peval(P, c) when two. One induction each; each C5
  constant is peval of a reflected expression by conversion. Then
  `block_sc`: block_ok with the smallness hypotheses replaced by
  d ≤ h, ρ ≤ T h and t Q(T) ≤ 1 (Q explicit in the block's fixed
  constants and T), and r_b ≤ Φ(T) h with Φ(T) ≥ T. Two scales: t for
  the w's, s1, s2 and C4's acoef (u ≤ t); h for the radius and the settle
  test (settle ≤ h² Q').
- *C6a as built* (2026-10-17; lib/pmono.bend ~330 lines, lib/scalepf.bend
  ~560, gated via tests/scale_laws.bend). Atoms are records (value,
  bound, small?) in one list (`PM.Atm`, `Bnd`); `pe_mono`, `pe_lin`,
  `pe_quad` by induction, the flag cases passed as lambdas. Each C5
  constant converts to its reflection by `{==}` (`cv_*`; a swapped atom is
  refused). `qblk` sums the parts each hypothesis needs (w3 twice for the
  1/2, 64 w4 for the 1/64 = 65/64 − 1, C4's acoef over the columns), so
  `block_sc` takes one hypothesis t qblk < 1; `rb_sc` r_b ≤ h phib,
  `phib_ge` phib ≥ T. The scales: u ≤ h ≤ t ≤ 1 (`pw_le`, 2^-b ≤ 2^-a
  for a ≤ b; ⌊p/2⌋ ≤ p + 1 from natord's divb_le).
- *C6b, per-block inverses* (lib/binvpf.bend). regular_blocks gives InvN
  of the block-order Jacobian; it is [[A, 0], [C, D]] as a list once the
  upper-right entries are rewritten to 0 (an equation that does not use
  a variable has derivative 0 there, propositionally), so GJ.block_inv
  peels block by block. Each A is the block's local Jacobian
  (deriv_rename, deriv_rnv, kept_reorder), and InvN gives InvB with
  β = its inverse's mnorm.
- *C6c, the blocks in turn* (lib/pblkpf.bend). The induction over
  pblocks (accumulator moved out: pblocks(.., acc) = pbacc(acc,
  pblocks(.., Nil))). Invariant at offset o: the box so far (gc, gr) has
  length o, holds X = x in block order (planpf's pbox), radii in
  [0, T_k h]. Per block, block_sc's inputs: lengths, equations held and
  below n + m (dyadic, swalk's ecov), x_b's equations zero locally
  (zeros_unsubst), the drawing within d (Near, the block's unknowns are
  not pins), the parameters' balls from pbox. Result: PBOk with
  walk(final box) (block_ok's conjuncts transported along the prefix;
  pcont from kle(|c - c| + r, r)), pbox over all nv, radii ≤ T_K h.
  T_0 = 0, T_(k+1) = Φ_k(T_k).
- *C6d, the verdict and the top* (lib/completepf.bend). held (pins: radius
  0, centers g's), explained and wf_dec (solve_total), within, check.r's
  permutations (vp from sfacts, ep from alleqs vs good), kperm of unperm,
  check_sides (Strict at x: center within lp T h of the value, radius
  ≤ lp T h; a variable-free Ge0 has radius 0), inbox (unperm of pbox).
  Choosing: Q = Σ_k Q_k + the sides' 4 lp T_K / σ, l = arch(Q) (P_l ≥ 2l,
  so t ≤ 2^-l < 1/Q), d = h.

**Risks.** Size: several thousand lines over several sessions (C4 is the
largest single piece). Checker time on long inequality proofs: keep the
files small. Rounding lemmas on binary positives. (Lists read with
trailing zeros turned out manageable in C1: index facts as Data
predicates over "every row below k", list equality by extensionality.)

---

## 11. Acceptance: the core theorem

*To restate in sk-08:* with the proposer verified (D7, §10), the theorem
is about `solve` itself rather than an arbitrary proposal `p`; the clauses
below keep their meaning.

```
law accept_sound:
  for +s:  Sketch      # typed IR and geometry before the edit
  for +e:  Edit
  for +p:  Proposal    # arbitrary data
  for +r:  Accepted
  where {Sketch.accept(s, e, p) == Ok{r} : Result<...>}
  Certified(apply(s, e), r)
    & Untouched(s, e, p.partition, r.geometry)
    & FlipsReported(s, p.anchors, r, r.flips)
```

- **Certified:** the §8.4 statements hold for the edited sketch minus the
  constraints listed in r.flagged, with r.geometry within grid/2 of the
  certified centers; side conditions (§8.6) hold over the balls. Every
  flagged constraint is reported with its §6 positional deviation.
- **Untouched:** the proposal's partition is closed (each constraint's
  variables lie in one part), edited entities lie in touched parts, and every
  untouched variable is bit-identical (persistent IDs). Untouched blocks keep
  their certificates.
- **FlipsReported:** anchor triples lie within one part; r.flips lists exactly
  the anchors whose orientation changed (certified over the balls, so it holds
  for the exact solution too).
- **check_is_spec:** the limb-bigint implementation equals the spec.
- **Meaning lemmas** (§5.5) connect equations to geometry.

---

## 12. Profiles and the SDF bridge

- **Regions (D14):** every bounded face of the arrangement of all
  non-construction curves is a selectable region, as in Onshape. No fill rule.
- **Arrangement (core):** line–line intersections are rational; line–arc and
  arc–arc need one square root each, compared exactly in ℚ(√D). Spline
  intersections need exact real-root isolation, so this is core work, not an
  extra. Face boundaries run between exact intersection points, so faces close
  exactly on the displayed geometry.
- **Certified topology:** each "cross / touch / miss" decision is a side
  condition certified over the balls (§8.6), so the exact solution has the same
  regions as the displayed one. A near-touch too close to decide is flagged red.
- **Point location** at rational points: orientation signs; bulge arcs via
  scaled \|p − C\|² vs r² plus angular range; splines via root counting along
  a ray (Sturm, or Descartes/Bernstein).
- **SDF generation** from the displayed parameters, converted to F32; shader
  numerics are not verified (F32 is axiomatic in Bend). With an
  L-Lipschitz-in-parameters SDF, the displayed shape is within
  L·(r + grid/2) of the exact one everywhere.
- **Optional laws** over an abstract Euclidean-field record: sign agreement;
  1-Lipschitz; min, max, polynomial smooth-min, extrude, revolve preserve it.
- **Rendering:** Lipschitz pruning (Barbier et al. 2025) and Keeter's
  point-sample pseudo-intervals; both need a true Lipschitz constant ≤ 1.

---

## 13. Bend engineering notes

- Checker `Nat` arithmetic is unary: binary spec numbers (§3).
- No CSE, affine values: straight-line programs over an environment.
- Geometry values are `Data` (`+`); closures and arrays are affine `Type`.
- Fuel `Nat` first (termination reads arguments left to right).
- No tactics: reflective ring normalizer (rewrite with its soundness lemma,
  then `{==}`) for bigint refinement, slope/midpoint identities, redundancy
  certificates, Finsler identities, meaning lemmas.
- No `if`; matches only on parameters / pattern variables.
- Runtime limits: `Nat` literals cap at 4294967295n; JS lane single-core with
  deep-recursion overflow (#798); no native library target (#813), so host
  integration uses the JS lane or a standalone binary.
- Gate: fail on "relies on unsafe or foreign code"; roadmap laws live in
  ROADMAP.bend, not imported by PROOF.bend.
- Optionally mirror top-level statements in Lean (bend.lean lags bend.ts).

---

## 14. Trusted base

**Trusted:** the Bend checker (bend.ts) and its logic (Type : Type with the
live/dead wall); comp.ts emitters and runtimes, including native mappings of
Base operations (README: "99% AI-written and has not been fully audited");
clang or the JS engine; base.bend; LAWS.bend (spec numbers, typed IR, exact
equation forms, constant definitions, tolerance checks, meaning-lemma
statements, `accept_sound`) and the spec files it rests on (`spec/num.bend`,
`spec/ring.bend`, `spec/big.bend`, `spec/field.bend`, `spec/geom.bend`,
`spec/sketch.bend`, `spec/mat.bend`; with sk-05/sk-06, `spec/knum.bend`,
`spec/real.bend` and `spec/box.bend`). The block certificate's definitions
(`lib/certdef.bend`) left the trusted base at the sk-06 review: the laws
no longer mention blocks, certificates or Newton maps.
optionally Euclidean-field axioms for SDF laws.

**Not trusted, and not needed for any claim:** the UI; F32 rendering. The
proposer is not trusted either: it is verified (§10).

**Boundary:** JS-supplied values are unchecked; the typed IR and proposals are
parsed and validated inside Bend. Differential testing of the JS and C lanes on
random sketches.

---

## 15. Milestones (risk-first)

| ID | Milestone | Depends on | Exit criterion |
|---|---|---|---|
| sk-00 | Scaffold: LAWS / PROOF / ROADMAP; gate rules | — | gate green on empty law set |
| sk-P1 | **Prototype spike in Bend (untrusted):** ink-metric proposer with F32 + exact refinement, pinning, block decomposition, certification cost and precision on the depth-30 chain (well- and ill-conditioned) and on one large cyclic block | — | report feeding Q12; go/no-go on §8.5 and on F32 refinement |
| sk-01 | Spec numbers (binary N, Int, rationals, dyadics), reflective normalizer | sk-00 | soundness law closed — **done** (2026-10-13; N deferred, §3) |
| sk-02 | Limb bigints refining the spec | sk-01 | refinement laws; 256-bit mul benchmark — **done** (2026-10-13; §3) |
| sk-03 | Typed IR, exact equation forms, meaning-lemma statements; LAWS review | sk-01, sk-P1 | LAWS reviewed by Danielle — **done** (2026-10-13; Q13–Q15 and follow-ups folded in) |
| sk-04 | Rational, dyadic and matrix library (∞-norms, products); Q order laws; canonical ℚ as an ordered-field instance (optional) | sk-02 | laws closed — **done** (2026-10-13; 37 laws: ℚ order, ℚ in every ordered field, gcd reduction, canonical ℚ, vectors and matrices; runtime bigint dyadics deferred to sk-05, §16) |
| sk-05 | Parametric block certificate (§8.3), mean-value method (Q12): generic K matrix library, slopes, ball arithmetic, checker, the six `cert_*` laws | sk-04 | **done (2026-10-14): 98 laws, gate green (~15 s)** |
| sk-05b | Complete ordered fields (Q18): template (Archimedean + Cauchy with a modulus), axioms cross-checked against mathlib's ℝ in Lean, Banach's theorem; exactly one zero per block | sk-05 | **done (2026-10-14): `cert_exists`, 99 laws; Lean cross-check passes** |
| sk-06 | Composition theorem (§8.4, exactly one solution in a complete ordered field), side conditions (§8.6), optional denominator clearing for D (Q19) | sk-05, sk-05b | **done (2026-10-14, reviewed)**: plan_exists, plan_unique, box_sides, sketch_exists, sketch_unique in LAWS (97 laws; the block laws became lemmas); denominator clearing optional (Q19) |
| sk-07 | Core vocabulary §5.1 + meaning lemmas | sk-03, sk-06 | laws closed — **meaning lemmas proven** in every ordered field (2026-10-13); §8.6 for the vocabulary covered by `box_sides` + `check_sides` (`tests/sides_demo.bend`, every kind, 2026-10-14); remaining: line–line / point–circle / circle–circle distances |
| sk-08 | `accept_sound`: certified, untouched, flips, diagnostics | sk-07 | law closed |
| sk-09 | Proposer v1, verified (§10): front end, structure (pins, red flags with Hall witnesses, blocks), exact numerics and the precision loop, all in Bend | sk-P1, sk-07, sk-06 | `solve_exists`/`solve_unique`/`solve_red`/`solve_pins`/`solve_total` proven, **drafts awaiting review (2026-10-14)**; `solve_complete` drafted, open; the depth-30 chains and the demos certify end to end in Bend (no Python in the path) |
| sk-10 | Bulge arcs, tangency, joins, trim/split (§5.2–5.3) | sk-07 | laws closed |
| sk-11 | Exact constants: algebraic roots, constructive π / cos / sin / tan (§7.1–7.3) | sk-06 | laws closed; typed angles exact |
| sk-12 | Guaranteed-digit queries (§9) | sk-09, sk-11 | demo |
| sk-13 | Redundancy certificates: library + verified check (§8.7) | sk-07 | laws closed |
| sk-14 | Proposer v2: drag previews (§6 checks), continuation, incremental re-certification | sk-09 | interactive drag; commit within target |
| sk-15 | Splines, NURBS, conic arcs, offsets, G2 (Q6) | sk-07 | laws closed |
| sk-16 | Regions: arrangement with exact intersections (incl. spline root isolation), certified topology, point location | sk-10, sk-15 | region laws closed |
| sk-17 | SDF bridge and renderer | sk-16 | render demo |
| sk-18 | Arc length (atan library; spline length via verified quadrature) | sk-11 | design + law |
| sk-19 | Positional deviation reports for flagged constraints + rounding lemmas (§6) | sk-07 | laws closed |
| sk-20 | Optional nearest-ness certificate (§8.10); certified continuation (Duff–Lee 2024, Lee 2025) | sk-08 | design + prototype |
| sk-21 | Integration: UI, persistence, host (#813) | sk-14, sk-17 | end-to-end sketch → solid demo |

sk-02 and sk-03 can run in parallel after sk-01.

---

## 16. Decisions and remaining questions

**Decided (Danielle, 2026-10-13):**
- **Q1** Exact by default.
- **Q2** "Change as little as possible" = least ink displacement (D13, §10).
- **Q3** Grid 1 nm. ℓ_min, preview ε and parameter scales from sk-P1.
- **Q4** Everything in Bend, prototype included (D12).
- **Q5** Every enclosed face is a region; no fill rule (D14).
- **Q6** G2 with auxiliary lengths (well-behaved form).
- **Q8** Binary spec numbers.
- **Q9** Bulge arcs, with 3-point, center-point and tangent arc creation tools.
- **Q10** No external references in v1 (likely feasible later).
- **Q11** Uncertifiable constraints are flagged red individually (D10).

**Assumed defaults (object if wrong):**
- **Q7** Flip detection is automatic: each step's certified side condition,
  plus any user-marked triples.
- Construction geometry does not bound regions, but counts as ink in the
  displacement metric.
- Standalone points count as 1 mm of ink.

**Decided in sk-01 (approved by Danielle, 2026-10-13):**
- Spec rationals are unreduced, with `Q.eq` as their equality (§3). DESIGN
  v0.4 said "normalized integer pairs"; reduction moves to the runtime layer,
  proven to preserve `Q.eq`, and is used only where sizes would grow (R10).

**Decided in the sk-03 review (Danielle, 2026-10-13):**
- **Q13** Meanings are stated for every ordered field, via a template
  parameter (§5.5), not over ℚ with a meta-level step.
- **Q14** Constraints reference existing entities by ID (§4).
- **Q15** Geometry may collapse to zero length: no ℓ_min, no nondegeneracy
  conditions on segments (§5.1). Circles keep r > 0 and arcs b > 0;
  distance dimensions may be 0 (d ≥ 0); a point–line distance needs its line
  (ℓ > 0); no bounded point-on-segment constraint (point on line covers the
  common case).

**Mine to decide:**
- **Q12** Mean-value method: telescoping slopes per variable, evaluated in
  ball arithmetic (§8.3); built and proven in sk-05.

**Decided after sk-04 (Danielle, 2026-10-13):**
- **Q16** The block certificate (§8.3) and composition (§8.4) are stated
  for every ordered field F, like the meanings (Q13). The contraction then
  holds in ℝ itself, where Banach's fixed point gives the exact solution, and
  ℚ is the instance `ofield_exists` builds. The matrix library already is.
- **Q17** The checker runs on the same numbers as everything else, "so it
  can deal with irrationals" (Danielle, stated twice; Claude first misread
  it as "fixed dyadics"). Shape: the checker is written once, generic over
  its computing numbers K, a template record like `OField` (whose
  `lt_total` returns `Or`, so on a concrete K it decides comparisons). The
  soundness law: for every ordered field F and every order-preserving ring
  map e : K → F, a passing certificate gives the contraction in F around
  e(ỹ). Instances of K:
  - the dyadics D (fast path; e = `ofd`, exists for every F);
  - ℚ (e = `ofq`, every F);
  - ℚ(√d) and small towers, for exact algebraic constants: e exists exactly
    when F has a positive √d, so the theorem covers ℝ and every field with
    the constants, and §7.2's "unknown pinned by its minimal polynomial"
    becomes a hypothesis on F instead of a box in the certificate.
  §2 does not rule this out: it rules out exact *solution coordinates*
  (nested towers of degree 2^k), not a few exact constants. Transcendental
  constants (π, cos θ) keep §7.3's balls; no exact computable field holds
  them in general.
  Claude's call within this (Danielle agreed it seems right): K carries no
  laws at all, only data and operations (zero, one, add, mul, neg, and a
  comparison returning `Cmp`). All laws live in F, on the map: e is a ring
  map (e(a + b) = e(a) + e(b), ...), and the comparison is sound through it
  (LT gives e(a) < e(b) in F, and so on). This is how D already works: D is
  m/2^e, not canonical, and `ofd_add` etc. are stated in F. So no K needs
  canonical forms, and ℚ(√d) is pairs over ℚ with e(a, b) = a + b·s, its
  laws proven in F from s² = d and s > 0 (much lighter than proving
  ℚ(√d)'s own field laws). §8.3 never divides (Y is certificate data), so
  no inverse is needed. `dmat` becomes the D instance of the generic
  matrix code rather than a parallel copy.
  Order of work: the generic shape with the D instance in sk-05; ℚ next
  (`ofq` exists); ℚ(√d) later, as its own milestone.
- **Q18** (Danielle, 2026-10-13) Existence is proven in Bend, not argued on
  paper: a complete-ordered-field template (Archimedean + Cauchy with a
  modulus) and Banach's theorem, with the axioms cross-checked against
  mathlib's ℝ in Lean (§8.4). The sk-05 laws stay over every ordered field.
- **sk-05 draft audit** (independent agent, 2026-10-13): one blocker
  (`cert_contract` false for vectors longer than the block; fixed by
  per-unknown radii that are 0 past the last unknown), should-fixes applied
  (`cert_center`, `cert_local`, `cert_unique`, the stub's comment, §8.4,
  parameters as one list of triples, componentwise conditions), and the
  checker's shape requirements listed in §8.3.

- **Q19** (Danielle, 2026-10-14, Claude's recommendation) Constants in the
  checker: `Num` has a partial `ofq : ℚ → Maybe K` (which rationals K holds
  exactly) and `Emb` one law, `e_ofq`: when `ofq(q) = Some k`, H(k) is q in
  F. K = ℚ and ℚ(√d) hold every rational; K = D holds those with a
  power-of-two denominator (`lib/kinst.bend`: `qnum`/`qemb`,
  `dnum`/`demb`, each with all eight map laws checked by Bend;
  `tests/kinst_demo.bend` gates them). A block with a constant K does not
  hold fails on that K; clearing denominators is an optional speedup for D,
  no longer required.
- **Irrational and transcendental values** (Danielle asked, 2026-10-14):
  `ofq` covers exact rationals only. Algebraic constants (√2) go either
  exactly, with K = ℚ(√d) plus named constants in the expression language
  (a constant symbol, a partial map from symbols into K, and one `Emb` law
  that the symbol lands on F's value, the field being one with a positive
  √d), or as parameters in a ball, which the `cert_*` laws already cover.
  π and cos θ go as parameters in balls whose radius the constants library
  proves (§7.3); π itself is defined in the complete-field template (Q18),
  so the final theorem speaks about the true π.

**Decided in the sk-06 review (Danielle, 2026-10-14):**
- The five sk-06 statements (`plan_exists`, `plan_unique`, `box_sides`,
  `sketch_exists`, `sketch_unique`, with the audit's coverage hypothesis)
  and `spec/box.bend` are approved and moved to LAWS.bend.
- Smaller trusted base: the `cert_*` laws and `cert_exists` are library
  lemmas now; the certificate's definitions moved to `lib/certdef.bend`,
  and `rbnd` and `vsub` (which `inbox` uses) to `spec/box.bend`.
- **The proposer is verified, not untrusted** ("we don't want untrusted
  proposer, we want trusted everything"). D7 and §10 are rewritten for
  sk-09: every answer the solver gives is a law, and every stage is proven
  to succeed where it should (§10).

**Decided (Danielle, 2026-10-14, sk-09):**
- A red constraint is dropped whole (constraints are what the user sees),
  and shown all red by default; expanding it in the UI shows which of its
  equations is the over-determined one (the `Why`'s equation j, labelled
  as the k-th equation of its constraint, e.g. a midpoint's y equation).

**Open for Danielle:**
- **sk-09 statements** (ROADMAP.bend): `solve_exists`, `solve_unique`,
  `solve_red`, `solve_pins`, and `spec/solve.bend` (`mark` by constraint
  position, `owners`, `overdet`, `explained` with its no-spare-flag
  condition, `held`). All four are proven; an independent audit found no
  blocker, and its two fixes are in (§10.2).


---

## 17. Risks

- **R1** Bend is young: checker/emitter bugs; checker speed on reflection.
- **R2** Proposer convergence on ill-conditioned blocks (F32 refinement stalls
  around κ ≈ 10^5–10^7).
- **R3** Certification failures on accidental singularities and coincidental
  redundancy need clear UX.
- **R4** Large cyclic blocks cost O(k³) per certification.
- **R5** Bigint sizes for spline/NURBS equations and high-precision blocks.
- **R6** Constructive transcendental library proofs (series bounds, argument
  reduction, atan slopes).
- **R7** Spline inside tests and intersections need verified real-root
  isolation.
- **R8** No native library target (#813) constrains host integration.
- **R9** No external references is a visible parity gap.
- **R10** Unreduced rationals could grow along long chains of rational
  arithmetic. Hot paths use dyadics at a fixed per-block precision and grid
  integers, so this should stay local (dimension expressions, meaning-lemma
  constants); watch sizes and reduce by gcd at runtime where they grow.

---

## 18. References

- Boehm, *Towards an API for the Real Numbers*, PLDI 2020 (the Android
  calculator's arithmetic). https://research.google/pubs/towards-an-api-for-the-real-numbers/
  Summary: https://blog.acolyer.org/2020/10/02/toward-an-api-for-the-real-numbers/
- Barbier et al., *Lipschitz Pruning*, CGF 44(2), Eurographics 2025.
  https://diglib.eg.org/handle/10.1111/cgf70057
- Keeter, *Gradients are the new intervals*, 2025.
  https://www.mattkeeter.com/blog/2025-05-14-gradients/
- Hubert-Brierre et al., *Accelerating Signed Distance Functions*, CGF 44(7), 2025.
- Duff, Lee, *Certified homotopy tracking using the Krawczyk method*, ISSAC 2024.
- Lee, *A priori bounds for certified Krawczyk homotopy tracking*, arXiv
  2512.01355. https://arxiv.org/abs/2512.01355
- Burr, Hauenstein, Lee, *Certified surface approximations using the interval
  Krawczyk test*, arXiv 2602.07718. https://arxiv.org/abs/2602.07718
- Krawczyk, 1969; Rump, *Verification methods*, Acta Numerica 2010.
- Hauenstein, Sottile, *alphaCertified*, ACM TOMS 38(4), 2012.
- Burnikel, Funke, Mehlhorn, Schirra, Schmitt, *A separation bound for real
  algebraic expressions*, ESA 2001 / Algorithmica 2009.
- Carson, Higham, mixed-precision iterative refinement, SISC 2017, 2018.
- Wan, 2006; Saunders, Wood, Youse, ISSAC 2011 (exact-residual linear solving).
- Draisma et al., *The Euclidean distance degree of an algebraic variety*,
  FoCM 2016.
- Guibas, Salesin, Stolfi, *Epsilon geometry*, SoCG 1989.
- Fornjot (fj-core docs), "robustness through explicitness".
- Zou et al., *A review on geometric constraint solving*, 2022.
  https://arxiv.org/abs/2202.13795
- neoscad/sketch-solver (reference only). https://github.com/neoscad/sketch-solver

---

## 19. Changelog

**v0.12 → v0.13 (sk-06 reviewed; the proposer becomes verified):**
- §8.3, §8.4, §14: the sk-06 laws are in LAWS.bend; the block laws are
  lemmas and the certificate's definitions left the trusted base
  (`lib/certdef.bend`; `rbnd`, `vsub` in `spec/box.bend`).
- D7, §10, §14, §15: the proposer is verified, not untrusted (Danielle):
  stages, the `solve_*` laws, completeness as open laws until proven;
  §11 to be restated about `solve` in sk-08.
- §10.2 as built: `solve` = `seal(search)`, the four `solve_*` laws
  proven (drafts), `spec/solve.bend`; the audit's two fixes (no spare red
  flag; pins reported and held).

**v0.11 → v0.12 (sk-06 proven, awaiting review):**
- §8.4: composition as built (box claim, block-ordered checker,
  substitution law); §15: sk-06 status; §16: sk-06 review and the
  trusted-base recommendation.
- §8.4: the sketch-level laws sketch_exists / sketch_unique (same review);
  `tests/sketch_plan_demo.bend`. §8.5: the verified checker measured on
  the spike's chains.

**v0.10 → v0.11 (sk-05b done):**
- §8.4: complete ordered fields as built (`spec/real.bend`, Skolem form),
  the law `cert_exists` and its Banach proof, the Lean cross-check against
  mathlib's ℝ (and ℚ shown not complete), the √5 demo. §15: sk-05b done.

**v0.9 → v0.10 (sk-05 done):**
- §8.3: the parametric block certificate as built and proven: the checker
  generic over computing numbers K with maps into every ordered field
  (Q17, `spec/knum.bend`, `lib/kinst.bend` for D and Q), blocks numbering
  their own variables, per-unknown radii, ball arithmetic and telescoping
  slopes per variable, six laws (`cert_factor`, `cert_center`,
  `cert_self`, `cert_contract` with s >= 0, `cert_fix`, `cert_unique`).
  §8.4: the Banach route (Q18). §16: Q16-Q19 decided; independent audit
  recorded. §15: sk-05 done, sk-05b added.

**v0.8 → v0.9 (sk-04 library):**
- §3: rational order (`q_lt_*`), ℚ in every ordered field (`ofq_*`), checked
  gcd reduction (`q_reduce`), canonical ℚ as an ordered field
  (`ofield_exists`). §8.3: vectors and matrices as built (`spec/mat.bend`,
  20 laws). §14: `spec/mat.bend` trusted. §15: sk-04 done (92 laws). §16:
  Q16 (certificates in every ordered field) decided yes; Q17 decided: the
  checker is generic over its computing numbers K (D, ℚ, ℚ(√d), ...) with a
  map into every F.

**v0.7 → v0.8 (meaning lemmas proven):**
- §5.5: the six meaning laws are proven in every ordered field (moved from
  ROADMAP to LAWS/PROOF; 55 laws, gate green); proof machinery and the
  certificate technique described. §15: sk-03 done; sk-07's meaning half
  done.
- `spec/field.bend`: order facts are Data; `spec/sketch.bend`: `Zeros` and
  `Sides` are reusable (`Both`), `dseg` factored through `Seg.rev_if`
  (kind and factoring changes only, same meaning).

**v0.6 → v0.7 (Danielle's sk-03 answers):**
- §5.5, `spec/field.bend`: meanings in every ordered field via a template
  parameter (Q13); `tests/field_demo.bend` proves one case from the axioms.
- §4: constraints reference entities by ID, with kind checks (`wf_refs`) and
  explicit orientation flags (Q14); segments name their endpoint points.
- §4, §5.1: geometry may degenerate (Q15): segment conditions dropped;
  parallel, perpendicular, on-line and mirror hold vacuously on collapsed
  segments; distances may be 0 (side conditions are > 0 or ≥ 0, §8.6);
  radius needs no side condition; point-on-segment removed.

**v0.5 → v0.6 (sk-03 drafted):**
- §4: typed IR as built: variables by index, geometry by value, merge kinds as
  index sharing (`wf`), `Fix` as an equation, entity side conditions, driven
  flag.
- §5.1: the table as built: > 0 nondegeneracy side conditions (Q15), point–line
  distance on the left, angle by any nonzero (c, s), fix as an equation;
  §5.3: b > 0 (counterclockwise).
- §5.5: meaning statements (sound/complete per constraint, entity and sketch)
  and the ℚ-to-real question (Q13).
- §14: the spec files are listed in the trusted base. §16: Q13–Q15 await
  review.

**v0.5, sk-02 done:** §3 runtime numbers as built (base-parametric limbs,
compare-based borrow, ≈ 12 µs per 256-bit product).

**v0.4 → v0.5 (sk-01 done):**
- §3: spec numbers as built: binary Pos/Z (Coq shape), unreduced ℚ with
  `Q.eq`, dyadics m/2^e, binary N deferred; ℤ and ℚ reflective normalizers.
- §15: sk-01 marked done; §16 records the unreduced-ℚ decision.

**v0.3 → v0.4 (Danielle's answers):**
- D10: per-constraint red flags replace the `ToleranceOnly` mode.
- D12: everything in Bend, including the prototype.
- D13: least-ink-displacement metric with closed forms (§10).
- D14: every enclosed face is a region; arrangement and certified topology are
  core (§12, sk-16).
- 1 nm grid; G2 via aux lengths; arc creation tools mapped to bulge arcs.
- §16 now records decisions and assumed defaults.

**v0.2 → v0.3 (exact by default):**
- D1: exactness is the default guarantee; tolerance checks become previews and
  an explicit `ToleranceOnly` fallback (D10, §6).
- New §8: pinning, block decomposition, parametric block certificates,
  composition theorem, precision cost, redundancy certificates (moved from
  optional), singular-configuration policy, incremental re-certification.
- New §5: exact equation forms with regularity rules; regular circle–circle
  tangency encoding.
- New §7 (Boehm-style constants): rational × known constant; algebraic roots;
  constructive transcendental constants over ℚ. Typed angles and arc sweeps are
  now exact; rational rotations removed.
- New §9: guaranteed-digit display.
- Nearest-ness certificate (Finsler form) stays optional (§8.10).
- Milestones reordered: the exact layer is on the critical path; sk-P1 now
  measures certification cost.
- Q1 resolved; Q11, Q12 added.

**v0.1 → v0.2 (audit):** see the v0.2 changelog in git history
(commit ebff628) and [AUDIT-v0.1.md](AUDIT-v0.1.md).
