# bend-cad — Design v0.2 (draft; audit of v0.1 folded in)

A formally verified 2D sketch constraint solver in Bend 2, aiming at Onshape /
FreeCAD sketcher parity, feeding an implicit-function (SDF) modeling pipeline.

This document is self-contained. It does not build on any existing project in
the workspace; external solvers and papers are cited as references only.
The v0.1 audit is in [AUDIT-v0.1.md](AUDIT-v0.1.md); §16 maps each finding to
its resolution here.

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

**Out of scope for v1:**
- 3D constraints and B-rep topology.
- **External references** (projecting model edges into a sketch). An SDF model
  has no explicit edges; slicing the zero set gives only approximate curves.
  This is a real parity gap and is accepted for v1.
- Certified global optimality of the nearest solution.
- Snell's-law constraint, arc-length dimensions (designed for, built last).

---

## 1. Decisions

| # | Decision |
|---|---|
| D1 | The core guarantee is **positional tolerance satisfaction on exact geometry**: every merge-based constraint holds exactly; every other constraint can be made exact by moving one designated point at most ε; this is decided exactly. |
| D2 | Core geometry and checks use **exact integers** at fixed per-kind scales. Rationals (integer pairs) appear only in tier E and in derived quantities that are scaled back to integers inside a check. |
| D3 | Coincident points, horizontal, vertical, fix, and concentric / equal radius between *full circles* are **variable merging / constants**: exact by construction. |
| D4 | **Every curve piece passes through its endpoints by construction**: segments by endpoints, arcs as bulge arcs, clamped splines through merged end control points, conic arcs as rational Béziers through end control points. Profiles are exactly closed. |
| D5 | Contact points, trim/split points and curve parameters are **explicit variables**. |
| D6 | The **typed IR is the spec and the persisted source of truth**. `Sat` is defined per constraint kind in LAWS.bend, and each kind has a **mandatory meaning lemma**. |
| D7 | **One acceptance theorem over arbitrary proposals.** The proposer is outside the trust story and may run anywhere. |
| D8 | The proposer's objective is the **nearest solution** to the current sketch. Nearest-ness is a quality goal, not part of the core guarantee. |
| D9 | **Exact existence/uniqueness** (and exact nearest-point certification) is an opt-in **tier E**, stated and proven over ℚ only. |
| D10 | **Lipschitz bounds replace interval arithmetic** everywhere. |

**Tier S** = the core guarantee (D1–D7). **Tier E** = the opt-in exact layer (D9).

---

## 2. Why this shape

**Exact algebraic numbers are infeasible at depth.** Each circle∩circle adjoins
a square root; k steps give a quadratic tower of degree up to 2^k (~10^9
coefficients per coordinate at k = 30), and exact zero tests via separation
bounds (BFMSS) need on the order of 2^k times the input bit-size.

**Exact-real semantics with interval arithmetic** (an earlier iteration: abstract
complete ordered field, Krawczyk certificates, slope transformers, adaptive
precision, ideal-membership certificates) is sound but heavy, and its precision
cost grows with chain depth.

**Positional tolerance satisfaction (D1)** removes most of that:
- The `Sat` check evaluates each constraint against the actual rounded
  geometry, so **checking** precision depends only on local conditioning, not
  on chain depth. (The **proposer's** work still grows with conditioning; see §6.)
- Redundant-but-consistent constraints are just checked like any other.
- The spec lives in ℤ; the checker is exact integer evaluation.
- Tolerances are **positional** (one length ε), never pure angles, because a
  fixed angular tolerance is unsatisfiable on a grid for short segments
  (a grid direction on length L has resolution ≈ 0.7·grid/L).

**Relation to epsilon geometry.** Guibas–Salesin–Stolfi's ε-predicates come with
warranties ("exact for a perturbed input"), which is close in spirit to D1's
meaning lemmas. The difference is where tolerance lives: here predicates on the
stored geometry are exact and two-valued; only constraint satisfaction carries a
band. Topology (loop closure, inside/outside) is exact. Fornjot's "robustness
through explicitness" principle is the same idea on the B-rep side.

**What tier S does not give** (tier E does, where it applies): it accepts a
sketch that is inconsistent but consistent within ε, and it does not prove a
sketch is fully constrained or its solution locally unique.

---

## 3. Numbers

**Spec numbers (decide in sk-01; recommendation below).** Bend's checker
evaluates `Nat` in unary: `{==}` on `Nat.is_lt(10^6, 10^6+1)` took 1.3 s in the
audit's measurement. So closed facts about constants like 2^16, the mm→nm
factor, or dyadic scales cannot be decided by computation on Peano `Nat`.
- **Recommended:** spec naturals in **binary** (positive / N style, as in Coq),
  so constants are small terms and the checker computes with them cheaply.
- Spec `Int` as `ofNat n | negSucc n` (canonical zero).
- The reflective normalizer's coefficients are binary.
- Where a constant must stay opaque, it is an erased parameter with a defining
  equation.

**Runtime numbers.** Limb bigints refining spec `Int`. Limbs are runtime `Nat`
values < 2^16: runtime `Nat` is native but capped at 2^48 − 1 (fail-stop on
every lane: CPU exits, GPU posts `ERR_NATS`, JS throws), so 16-bit limbs keep
schoolbook column sums under the cap; limb-bound laws make the cap unreachable.
Not `U32` limbs: `U32` is a 32-bit `Word` bit list in the theory, and there is
no `U64`.

**Scales.** Every variable kind has a fixed scale; values are integers at that
scale.
- Coordinates and lengths: 1 unit = 1 nm or 1 pm (Q3). With nm, inch fractions
  are exact down to 1/64"; with pm, down to 1/512"
  (25.4 mm = 2^9 · 127 · 5^8 pm).
- Curve parameters (t, bulge b): dyadic, 1 unit = 2^−s, with s chosen so
  quantization stays below ε (shallow arcs need large s; see §5.3).
- Angle dimensions: a rational rotation stored as an integer pair (a, b).

**Magnitudes.** ±1 km at 1 nm ≈ 2^40. Quadratic checks ≈ 2^80–2^160; spline
checks a few hundred bits. Bounded and benchmarked in sk-02 / sk-09.

---

## 4. Typed IR (the spec input)

- **Persistent IDs** for every entity, variable and constraint; the typed IR is
  what is saved, loaded, and re-checked on every load and save.
- **Variables** with kinds: `coord`, `length`, `param`, `aux`.
- **Entities:** `Point`, `Segment(P, Q)`, `Circle(C, r)`,
  `Arc(S, E, b)` (bulge arc, §5.3), `ConicArc(...)`, `BSpline(degree, knots,
  control points, weights)`, `Offset(base, d)`; each with a construction flag.
- **Constraints** are typed: `Distance(P, Q, d)`, `Perpendicular(L1, L2)`,
  `Tangent(A, B, contact, side)`, and so on, referencing entities by ID.
  `Sat` is defined per kind in LAWS.bend. Polynomial forms are produced
  *inside* `check`, so an untrusted front end cannot change what a constraint
  means.
- **Merging (D3)** is recorded in the IR as shared variable IDs. Merge
  conflicts are errors: two different constants merged; horizontal and vertical
  on one segment (a zero-length segment).
- **Dimensions** are driving or driven (reference). Driving values may be
  expressions over named sketch variables; expressions are polynomial/rational
  and evaluated exactly.
- **Evaluation** is a straight-line program over an environment: shared
  subterms (e.g. a spline's span evaluation) are computed once. No expanded
  sparse polynomials (they blow up for spline checks), and no recursion over
  DAGs (Bend has no CSE).

---

## 5. Tier S: constraint vocabulary and checks

Notation: u, v are direction vectors; ε is the positional tolerance (one global
value, overridable per constraint); ℓ_min > ε is the nondegeneracy length.

**Meaning template.** Each kind's meaning lemma has the form: *the constraint
can be made exactly true by moving one designated point by at most cε*, with
c = 1 unless stated. Checks are exact equivalences where cheap, otherwise
sufficient conditions (stricter than the meaning).

**Direction checks are positional.** For directions u, v the deviation is
measured as a displacement of the *shorter* entity's far endpoint:
dot(u,v)² ≤ ε²·max(\|u\|², \|v\|²) means min(\|u\|, \|v\|)·\|cos θ\| ≤ ε, i.e.
moving the shorter segment's tip by ≤ ε makes the pair exactly perpendicular.
(max is a disjunction of two polynomial checks.)

### 5.1 Core

| Constraint | Encoding | Exact Int check | Meaning |
|---|---|---|---|
| coincident, horizontal, vertical, fix; concentric / equal radius of full circles | merge / constant | — | exact |
| distance(P, Q) = d | — | (d−ε)² ≤ \|u\|² ≤ (d+ε)² (lower bound vacuous if d ≤ ε) | \|\|u\| − d\| ≤ ε (equivalence) |
| horizontal / vertical distance | — | \|Δx − d\| ≤ ε (resp. Δy) | equivalence |
| radius r = d (circle) | — | \|r − d\| ≤ ε | equivalence |
| equal length | — | for A = \|u\|², B = \|v\|²: (A − B − ε² ≤ 0 ∨ (A − B − ε²)² ≤ 4ε²B), and the same with A, B swapped | \|\|u\| − \|v\|\| ≤ ε (equivalence) |
| perpendicular / normal | — | dot(u,v)² ≤ ε²·max(\|u\|², \|v\|²) | positional, as above |
| parallel | — | cross(u,v)² ≤ ε²·max(\|u\|², \|v\|²) (optionally dot > 0) | positional |
| point on line AB | — | cross(P−A, B−A)² ≤ ε²·\|B−A\|² | dist(P, line) ≤ ε (equivalence) |
| point on segment | — | line check, and 0 ≤ dot(P−A, B−A) ≤ \|B−A\|² | implies dist(P, segment) ≤ ε |
| point–line distance d | — | band on cross(P−A, B−A)² against (d ± ε)²·\|B−A\|² | equivalence |
| point on circle | — | (r−ε)² ≤ \|P−C\|² ≤ (r+ε)² | radial error ≤ ε |
| midpoint M of PQ | — | \|2M − P − Q\|² ≤ 4ε² | \|M − (P+Q)/2\| ≤ ε (equivalence) |
| symmetric P, Q about line AB | — | with w = B − A, R̂ = [[wx²−wy², 2wxwy], [2wxwy, wy²−wx²]]: \|\|w\|²(Q−A) − R̂(P−A)\|² ≤ ε²\|w\|⁴ | \|Q − mirror(P)\| ≤ ε (equivalence) |
| block | constants for the block's variables | — | exact |

Every check involving a direction also requires that direction's length ≥ ℓ_min.

### 5.2 Angles as rational rotations

An angle dimension is an integer pair (a, b), t = a/b ≈ tan(θ/2),
R̂ = [[b²−a², −2ab], [2ab, b²−a²]] = (a²+b²)·R(θ′), θ′ = 2·atan(a/b).
Positional check: cross(R̂u, v)² ≤ ε²·(a²+b²)²·max(\|u\|², \|v\|²) and
dot(R̂u, v) > 0. The spec is about θ′ exactly; degrees are display, and the UI
picks (a, b) with \|θ′ − θ\| far below ε/ℓ_max.

Circular patterns of n copies accumulate n·\|θ′ − θ\| of angle error relative to
the typed degrees; patterns should use a rotation whose n-th power is exact
(e.g. derive copies from one stored rotation, compare against θ′ only).

### 5.3 Arcs (D4)

`Arc(S, E, b)`: S, E are point variables (grid), b = tan(sweep/4) is a dyadic
parameter, b ≠ 0.
- Derived center C = (S+E)/2 + perp(E−S)·(1 − b²)/(4b); derived
  r² = \|E−S\|²·(1 + b²)²/(16b²). Both rational; checks scale denominators back
  to integers.
- Tangent direction at S is R̂_b(E − S), the chord rotated by half the sweep
  (cos = (1−b²)/(1+b²), sin = 2b/(1+b²)): rational, no center needed.
- The arc passes through S and E exactly, so loops close exactly.
- Concentric / equal radius involving arcs are checks on derived C and r²
  (positional bands), not merges.
- Quantization: for shallow arcs r ≈ \|E−S\|/(4b), so the scale 2^−s of b must
  satisfy 4r²/\|E−S\|·2^−s ≪ ε (radius tolerance); the proposer picks s per arc
  kind or a global s ≥ 64 (Q3).

### 5.4 Tangency and joins (D5)

| Constraint | Variables | Check |
|---|---|---|
| G1 join at a merged endpoint | — | end tangent directions parallel (positional) and dot > 0 |
| line–circle/arc tangent (not at an endpoint) | contact T | T on line (§5.1); T on circle/arc band; (T − C) ⊥ line direction (positional) |
| circle–circle/arc tangent | contact T | T in both radius bands; C₁, T, C₂ collinear (positional); sign of dot(T−C₁, T−C₂) selects external (< 0) or internal (> 0) |
| full circle – full circle tangent (no contact needed) | — | (r₁ + r₂ ∓ ε)² band on \|C₁ − C₂\|² (internal: \|r₁ − r₂\|) |

Meaning lemmas give the exact-tangent configuration within cε (c to be derived
in sk-03; the audit derived \|dist(C, line) − r\| ≤ 2ε + r(1 − cos α) for the old
angular form).

### 5.5 Curves

| Constraint | Variables | Check |
|---|---|---|
| point on B-spline span j | param t | \|P − C_j(t)\|² ≤ ε², knot_j ≤ t ≤ knot_{j+1} |
| point on NURBS span j | param t | \|w(t)·P − N(t)\|² ≤ ε²·w(t)², knot_j ≤ t ≤ knot_{j+1} (w(t) > 0 follows from positive weights) |
| curve–spline tangent | contact params | contact checks plus tangent directions parallel (positional) |
| offset point at distance d | param t | (P − C(t)) ⊥ C′(t) (positional), distance band on \|P − C(t)\|, \|C′(t)\| ≥ ℓ_min·(scale). Local (foot-point) meaning, not a global distance. |
| G2 join | — | **open (Q6)** |
| conic arcs | — | rational quadratic Bézier through end control points (sk-09) |
| arc sweep, arc length | — | sweep via the bulge (exact rational relation); arc length is the one kind needing real analysis (rational enclosures), built last |
| trim / extend / split / fillet | new point variables | point-on checks against both curves; pieces end exactly at the new points |

C_j(t) is evaluated exactly in Bernstein form per span.

### 5.6 Rounding lemma (completeness w.r.t. the grid)

For each kind, prove: if a rational configuration satisfies the constraint
within ε/2 (at any finer resolution), its rounding to the grid satisfies it
within ε, under stated conditions (ε ≥ c_k·grid, ℓ_min bounds, parameter
scales). Consequence: the grid never makes a sketch that is solvable at finer
resolution unsatisfiable. Stated over ℚ; by density it covers exact real
solutions at the meta level.

---

## 6. Proposer (untrusted): nearest-solution solving

**Objective.** Minimize Σ wᵢ(xᵢ − x₀ᵢ)² subject to the constraint equations
F(x) = 0 (targets as exact equalities; bands only for acceptance) and the
inequalities (segment ranges, arc ranges, tangency side, dot > 0).

- **KKT** with an active set for inequalities: W(x − x₀) + J(x)ᵀλ = 0, F(x) = 0.
  Square in (x, λ); **generically** nonsingular. Known singular cases: drag
  target at a circle's center (every circle point is stationary); rank lost
  exactly at the solution (near-tangent intersections). LM damping handles both.
- **Weights:** user geometry carries weight; contact points, parameters and aux
  variables get a tiny positive weight (e.g. 2^−20 relative), not zero, to keep
  the system nonsingular. Dragging: cursor target with a large weight, or as a
  hard equality (option).
- **Precision:** Bend has only F32. Linear solves in F32, residuals computed
  exactly in Int (scaled before conversion; F32 → Int via `F32.bits` decoding,
  since `F32.to_u32` returns 0 for negatives and values ≥ 2^32). Each refinement
  step gains roughly 24 − log₂(c·n·κ) bits, so this stalls around κ ≈ 10^5–10^7;
  beyond that, use exact/dyadic elimination in the style of exact-residual
  solvers (Wan 2006; Saunders–Wood–Youse 2011).
- **Components** solved independently (fork-join).
- **Projected continuation** for large edits; flips detected by anchor signs.
- **Redundancy:** rank-revealing QR drops dependent rows for the optimization;
  acceptance still checks every constraint. Conflicts are reported per
  constraint.
- **DOF reporting:** untrusted (QR) in v1.
- **Location:** anywhere (D7): Bend F32, or an external JS f64 proposer through
  Bend's JS interop.

**Reference (not a dependency):** neoscad/sketch-solver (deterministic LM,
continuation from drawn to target dimensions, QR diagnostics, flip detection;
created 2026-10-07).

---

## 7. Acceptance: the core theorem (tier S)

```
law accept_sound:
  for +s:  Sketch      # typed IR and geometry before the edit
  for +e:  Edit
  for +p:  Proposal    # arbitrary: geometry, partition, anchors
  for +r:  Accepted    # accept's output
  where {Sketch.accept(s, e, p) == Ok{r} : Result<...>}
  Sat(apply(s, e), r.geometry)
    & Untouched(s, e, p.partition, r.geometry)
    & FlipsReported(s, p.anchors, r.geometry, r.flips)
```

- **Sat:** every constraint of the edited sketch, checked on the whole result.
  No assumption that the previous geometry satisfied anything.
- **Untouched (L1):** the proposal supplies a partition of variables. The
  checker verifies it is closed (each constraint's variables lie in one part),
  that every edited entity lies in a touched part, and that every variable in an
  untouched part is bit-identical to before (matched by persistent ID). A
  partition that marks everything touched is allowed but gives nothing; the UI
  can show which parts were touched.
- **FlipsReported (L2):** anchor triples lie within one part; `r.flips` lists
  exactly the anchors whose orientation sign changed. ("No flips" is really
  "flips are reported, never silent.") Default anchor policy: Q7.
- **check_is_sat:** `check` (limb bigints) equals `Sat` (spec).
- **Meaning lemmas** (mandatory, one per constraint kind) connect `Sat` to the
  table's meaning column.
- **Diagnostics:** per-constraint results are returned for the UI.

The proposer does not appear in this law, so it is outside the trust story.

---

## 8. Tier E (opt-in): exact existence, uniqueness, nearest point, over ℚ

### 8.1 Quadratization

Aux variables make every equation quadratic: √a → s with s² = a, s ≥ 0;
a/b → q with q·b = a, b ≠ 0; higher-degree products → y = x·z. The
second-derivative tensor T (T_ijk = ∂²f_i/∂x_j∂x_k) is then constant.

### 8.2 Midpoint identity

For quadratic f, in integer form: 2(f(x) − f(y)) = (2·J₀ + T(x + y))·(x − y),
where J₀ is the constant part of the Jacobian. Proven by induction over terms
with the ring normalizer.

### 8.3 Certificate

Rational data (x̃, Y, r) from the proposer; the checker computes
q₀ = ‖I − Y·J(x̃)‖∞, κ = maxᵢ Σⱼ Σₖ \|T_ijk\| (so ‖J(x) − J(x̃)‖∞ ≤ κ‖x − x̃‖∞),
and checks exactly:
1. q = q₀ + ‖Y‖∞·κ·r < 1;
2. ‖Y·f(x̃)‖∞ ≤ (1 − q)·r;
3. q′ = ‖I − J(x̃)·Y‖∞ < 1 (a formal convenience for the residual bound).

Then g(x) = x − Y·f(x) contracts by q on B = B∞(x̃, r) and maps B into B
(Krawczyk/Rump-style test in contraction form).

### 8.4 Theorems (ℚ only)

- **Approximate solvability:** ∀k. ∃x ∈ ℚⁿ ∩ B with ‖f(x)‖∞ ≤ 2^−k (witness:
  simplified-Newton iterates; ‖f(xₙ)‖ ≤ ‖J(x̃)‖·qⁿ·‖Y·f(x̃)‖/(1 − q′)).
- **Approximate uniqueness:** ∀x, y ∈ B: ‖x − y‖ ≤ (‖Y·f(x)‖ + ‖Y·f(y)‖)/(1 − q).

Meta-level (documented, not formalized): these **imply** exactly one real root
in B (compactness plus continuity). After quadratization, uniqueness holds in
the lifted (x, aux) box.

### 8.5 Side conditions over the ball

For quadratic g: g(x) ≥ g(x̃) − ‖∇g(x̃)‖₁·r − ½·Σⱼₖ \|∂²g/∂x_j∂x_k\|·r² on B.
Exact constants; no intervals.

### 8.6 Scope

- **Well-constrained sketches:** the system itself.
- **Under-constrained sketches:** the KKT system of §6 (a KKT root has
  F = 0), which also certifies the nearest-point stationarity exactly.
- **Redundant sketches:** rows dropped to make the system nonsingular are not
  certified to hold exactly, unless a **redundancy certificate** is supplied: a
  polynomial identity F_k = Σ cᵢFᵢ (possibly times a nondegenerate factor,
  certified nonzero by §8.5), checked by the normalizer.
- x̃ may refine the displayed integer geometry; ‖x̃ − displayed‖ is reported.
- With an L-Lipschitz-in-parameters SDF, the displayed shape is within L·r of
  the exact one everywhere.

### 8.7 Second-order (strict local minimum of the nearest-point problem)

Finsler/Debreu form, which keeps certificate entries at ~100–150 bits: the
proposer supplies ρ ≥ 0 and a dyadic unit-triangular T; the checker verifies
that Tᵀ(H_L + ρJᵀJ)T is strictly diagonally dominant with positive diagonal,
with a margin covering the variation of H_L and J over the certified ball
(§8.5-style bounds). Soundness: if Jv = 0 then vᵀ(H_L + ρJᵀJ)v = vᵀH_Lv, and a
symmetric strictly diagonally dominant matrix with positive diagonal is
positive definite (Gershgorin); T is invertible. (Replaces v0.1's exact LDLᵀ,
whose entries grow to ~10^5 bits on 120-constraint components.)

### 8.8 Cost

Precision ≈ log₂(conditioning) bits, additive in chain depth. Tier S never
pays it.

---

## 9. Profiles and the SDF bridge

- **Exact closure (D4):** loops are sequences of pieces sharing endpoint
  variables, and every piece passes through its endpoints. The winding number is
  well defined everywhere off the curves.
- **Arrangements:** curves that cross without trimming need intersection points
  for region detection. Line–line intersections are rational; line–arc and
  arc–arc need one square root each, and comparisons in ℚ(√D) are exact
  (compare a² with b²D, with signs). Spline intersections need real-root
  isolation (later).
- **Inside tests at rational points:** orientation signs for segments; for bulge
  arcs, \|p − C\|² vs r² (scaled) plus angular-range signs; for splines,
  root counting of the span polynomial along a ray (Sturm, or
  Descartes/Bernstein on [0, 1]). Fill rule: Q5.
- **SDF generation** from exact parameters, converted to F32 for shaders; F32 is
  axiomatic in Bend, so shader numerics are not verified.
- **Optional laws** over an abstract Euclidean-field record: sign agreement with
  the exact inside test; 1-Lipschitz; min, max, polynomial smooth-min, extrude
  and revolve preserve 1-Lipschitz.
- **Rendering acceleration:** Lipschitz pruning (Barbier et al. 2025) and
  Keeter's point-sample pseudo-intervals. Both need a true Lipschitz constant
  ≤ 1: scaling, or min/max of non-normalized fields, breaks it (Keeter also
  reports mixed performance against interval arithmetic).

---

## 10. Bend engineering notes

- **Checker arithmetic is unary on Peano `Nat`** (§3): keep constants binary or
  opaque in proofs.
- **No CSE and affine values:** straight-line programs over an environment
  (§4); never recurse over a DAG.
- Geometry values are `Data` (`+`); closures and arrays are affine `Type`.
- **Termination:** fuel `Nat` first (arguments are read left to right).
- **No tactics:** a reflective ring normalizer over spec `Int` proves polynomial
  identities (rewrite with its soundness lemma, then `{==}`): bigint refinement,
  §8.2, Finsler identities, meaning lemmas, redundancy certificates.
- No `if`; matches only on parameters / pattern variables.
- **Runtime limits:** `Nat` literals cap at 4294967295n; the JS lane is
  single-core and deep non-tail recursion overflows it (#798); there is no
  native library target yet (#813), so Bend cannot be embedded in a C/C++ host
  today. Host integration must use the JS lane or a standalone binary.
- **Gate:** `bend PROOF.bend` exits 0 even when it prints "relies on unsafe or
  foreign code"; the gate script fails on that line. Roadmap (open) laws live in
  ROADMAP.bend, which PROOF.bend does not import, so the gate stays meaningful.
- Optionally mirror top-level statements in Lean (the README notes bend.lean
  lags bend.ts).

---

## 11. Trusted base

**Trusted:**
- the Bend checker (bend.ts) and its logic (Type : Type, kept consistent by the
  live/dead wall; the Lean model lags);
- the emitters and runtimes in comp.ts, including the native mappings of Base's
  operations (README: "99% AI-written and has not been fully audited");
- clang (native lanes) or the JS engine;
- base.bend;
- LAWS.bend: spec numbers, typed IR, `Sat` per kind, meaning-lemma statements,
  `accept_sound`;
- optionally the Euclidean-field axioms for SDF laws.

**Not trusted:** the proposer; the UI; F32 rendering.

**Boundary:** values crossing from JS are unchecked (a negative BigInt as `Nat`,
malformed constructors). The typed IR is parsed and validated inside Bend
before `accept`.

**Mitigation:** differential testing of the JS and C lanes on random sketches.

---

## 12. Milestones (risk-first)

| ID | Milestone | Depends on | Exit criterion |
|---|---|---|---|
| sk-00 | Scaffold: LAWS / PROOF / ROADMAP layout; gate fails on open laws in PROOF and on "unsafe or foreign" | — | gate green on an empty law set |
| sk-P1 | **Prototype spike (untrusted, any language):** nearest-solution proposer, depth-30 chain (well- and ill-conditioned), grid rounding experiments for ε, ℓ_min, bulge scale | — | report: conditioning vs precision, proposer convergence, tolerance satisfiability (feeds Q3) |
| sk-01 | Spec numbers (binary N, `Int`), reflective normalizer | sk-00 | soundness law closed; (a+b)² identity in one rewrite |
| sk-02 | Limb bigints refining spec `Int` | sk-01 | refinement laws closed; 256-bit mul benchmark |
| sk-03 | Typed IR, `Sat` per kind, meaning-lemma statements, rounding-lemma statements; LAWS review | sk-01, sk-P1 | LAWS reviewed by Danielle |
| sk-04 | `check_is_sat` + meaning lemmas + rounding lemmas for §5.1–5.2 | sk-02, sk-03 | laws closed |
| sk-05 | Bulge arcs, tangency, joins, trim/split points (§5.3–5.4) | sk-04 | laws closed |
| sk-06 | `accept_sound`: partition, untouched, flips, diagnostics | sk-04 | law closed |
| sk-07 | Proposer v1: KKT + active set + LM, F32 with exact refinement, components | sk-P1, sk-04 | fixture sketches accepted; check < X ms for N constraints (set after sk-P1) |
| sk-08 | Proposer v2: drag, projected continuation, flip handling | sk-07 | interactive drag at target frame time with provisional display; accept on release |
| sk-09 | Splines, NURBS, conic arcs, offsets, G2 (Q6) | sk-04 | laws closed for the curve vocabulary |
| sk-10 | Profiles: loops, arrangements (exact ℚ(√D) comparisons), inside tests, fill rule | sk-05, sk-09 | inside-test law closed |
| sk-11 | Rational + matrix library (for tier E) | sk-02 | laws closed |
| sk-12 | SDF bridge and renderer (Lipschitz pruning); optional SDF laws | sk-10 | render demo |
| sk-13 | Tier E: quadratization, §8.3–8.7, redundancy certificates | sk-11, sk-06 | laws closed |
| sk-14 | Certified continuation (Duff–Lee 2024, Lee 2025) and certified local manifold structure (Burr–Hauenstein–Lee 2026) | sk-13 | design + prototype |
| sk-15 | Arc length and other transcendental dimensions | sk-13 | design + law |
| sk-16 | Integration: UI, typed-IR persistence, host (JS lane or binary; see #813) | sk-08, sk-12 | end-to-end sketch → solid demo |

sk-02 and sk-03 can run in parallel after sk-01.

---

## 13. Open questions (for Danielle)

- **Q1.** Tier S (positional tolerance) as the core guarantee, tier E opt-in?
  (Recommended.)
- **Q2.** Nearest-solution metric: per-entity weights, rigid-motion term?
- **Q3.** Grid (nm vs pm), default ε and ℓ_min, parameter scales. sk-P1 informs
  this.
- **Q4.** *Resolved by D7:* the proposer may live anywhere. Preference?
- **Q5.** Fill rule: nonzero or even-odd.
- **Q6.** G2 formulation (positional form of curvature continuity).
- **Q7.** Default anchor-triple policy for flip reporting.
- **Q8.** Spec numbers in binary (recommended) vs opaque-constant Peano.
- **Q9.** Bulge arcs (recommended) vs rational-quadratic-Bézier arcs.
- **Q10.** Accept "no external references" for v1?

---

## 14. Risks

- **R1** Bend is young: checker/emitter bugs; checker speed on reflection.
- **R2** Proposer convergence on ill-conditioned clusters (F32 refinement stalls
  around κ ≈ 10^5–10^7).
- **R3** Tier S accepts near-inconsistent sketches (mitigation: tier E).
- **R4** Strict checks may reject solutions the user considers fine
  (mitigation: proposer targets exact equalities; rounding lemma).
- **R5** Bigint sizes for spline/NURBS checks and bulge parameters.
- **R6** Arc length needs real analysis in the spec.
- **R7** Spline inside tests and intersections need verified real-root
  isolation.
- **R8** No native library target (#813) constrains host integration.
- **R9** No external references is a visible parity gap.

---

## 15. References

- Barbier et al., *Lipschitz Pruning*, CGF 44(2), Eurographics 2025.
  https://diglib.eg.org/handle/10.1111/cgf70057
- Keeter, *Gradients are the new intervals*, 2025.
  https://www.mattkeeter.com/blog/2025-05-14-gradients/
- Hubert-Brierre et al., *Accelerating Signed Distance Functions*, CGF 44(7),
  2025. https://diglib.eg.org/items/1a39a460-61c5-4b38-8486-d86353d2d6a4/full
- Duff, Lee, *Certified homotopy tracking using the Krawczyk method*, ISSAC 2024.
- Lee, *A priori bounds for certified Krawczyk homotopy tracking*, arXiv
  2512.01355. https://arxiv.org/abs/2512.01355
- Burr, Hauenstein, Lee, *Certified surface approximations using the interval
  Krawczyk test*, arXiv 2602.07718 (local manifold structure, assuming dimension
  and full rank). https://arxiv.org/abs/2602.07718
- Krawczyk, 1969; Rump, *Verification methods*, Acta Numerica 2010.
- Hauenstein, Sottile, *alphaCertified*, ACM TOMS 38(4), 2012.
- Burnikel, Funke, Mehlhorn, Schirra, Schmitt, *A separation bound for real
  algebraic expressions*, ESA 2001 / Algorithmica 2009.
- Carson, Higham, mixed-precision iterative refinement, SISC 2017, 2018.
- Wan, exact integer linear solving with numeric methods, 2006;
  Saunders, Wood, Youse, *Numeric-symbolic exact rational linear system
  solver*, ISSAC 2011.
- Peyrl, Parrilo, rational SOS decompositions, TCS 2008.
- Draisma et al., *The Euclidean distance degree of an algebraic variety*,
  FoCM 2016.
- Guibas, Salesin, Stolfi, *Epsilon geometry*, SoCG 1989.
- Fornjot (fj-core docs), "robustness through explicitness" (noted there as
  not fully implemented). https://docs.rs/fj-core/0.49.0/fj_core/
- Zou et al., *A review on geometric constraint solving*, 2022.
  https://arxiv.org/abs/2202.13795
- neoscad/sketch-solver (reference architecture only).
  https://github.com/neoscad/sketch-solver

---

## 16. Changelog: v0.1 audit → v0.2

| Finding | Resolution |
|---|---|
| B1 N2 does not scale | N2 moved to tier E in Finsler/Debreu form (§8.7); core no longer certifies optimality |
| M1 arcs break closure | D4 + bulge arcs (§5.3); clamped splines and conic arcs through end control points |
| M2 symmetric wrong | exact positional reflection check (§5.1) |
| M3 σ direction | angular σ removed; all direction checks positional (§5) |
| M4 angular tolerance vs grid | positional tolerances + rounding lemma (§5.6); sk-P1 informs Q3 |
| M5 depth-independence overstated | §2 now says checking only; proposer limits stated (§6); N1/N2 out of core |
| M6 KKT nonsingularity | "generically"; tiny positive weights; LM; active set (§6) |
| M7 tier E scope | §8.6 scope + optional redundancy certificates |
| M8 meaning gap | typed IR as spec and persisted truth; mandatory meaning lemmas (D6, §4) |
| M9 trusted base | §11 expanded; JS boundary validation; differential testing |
| M10 acceptance theorem | `accept_sound` (§7); proposer leaves the trust story |
| M11 unary checker Nat | binary spec numbers recommended; `ofNat | negSucc` Int (§3) |
| M12 parity gaps | vocabulary extended (§0, §5); arrangements (§9); external references declared out of scope |
| M13 milestones | risk-first with sk-P1; rational/matrix and integration milestones; gate rules (§10, §12) |
| M14 L1 underspecified | partition supplied and checked; Sat on whole result; persistent IDs; anchors within one part (§7) |
| Minor 1 | exact equal-length equivalence (§5.1) |
| Minor 2 | ℓ_min > ε; vacuous lower bounds stated |
| Minor 3 | point on segment without a parameter (§5.1) |
| Minor 4 | NURBS knot range added (§5.5) |
| Minor 5 | tangency meaning lemma constant to derive in sk-03 (§5.4) |
| Minor 6 | offset: local meaning and C′(t) ≠ 0 stated (§5.5) |
| Minor 7 | moot (N2 in tier E only) |
| Minor 8 | "imply", lifted box (§8.4) |
| Minor 9 | integer-form identity (§8.2) |
| Minor 10 | straight-line programs over an environment (§4) |
| Minor 11 | runtime limits (§10, R8) |
| Minor 12 | F32 conversion details (§6) |
| Minor 13 | D2 reworded |
| Minor 14 | merge conflicts, construction flag, diagnostics, drag option, imperial grid, circular patterns (§3, §4, §5.2, §6, §7) |
| Nits | flips "reported"; q, q′ computed by checker; fail-stop wording; normalizer usage wording |
| Literature | corrections and missing references (§15) |
