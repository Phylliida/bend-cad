# bend-cad — Design v0.1 (draft, pending audit)

A formally verified 2D sketch constraint solver in Bend 2, aiming at Onshape /
FreeCAD sketcher parity, feeding an implicit-function (SDF) modeling pipeline.

This document is self-contained. It does not build on any existing project in
the workspace; external solvers and papers are cited as references only.

---

## 0. Goal and scope

**Entities:** points, lines/segments, circles, arcs, ellipses and conics,
B-splines and NURBS (control-point and fit splines), offsets.

**Constraints:** coincident, concentric, horizontal, vertical, fix, parallel,
perpendicular, tangent (incl. curve–curve and at joins), G1/G2 continuity,
equal, midpoint, symmetric, distance, radius/diameter, angle, point-on-curve,
offset, drag.

**Downstream:** implicit / SDF modeling (extrude, revolve, CSG, sphere tracing).
No B-rep.

**Motivating stress case:** chains of 20–30 dependent circle∩circle
constructions (each point at given distances from two earlier points).

**Not in v1:** 3D constraints, B-rep topology, certified global optimality of
the nearest solution. Arc-length dimensions are designed for but built last.

---

## 1. Decisions

| # | Decision |
|---|---|
| D1 | The core guarantee is **tolerance satisfaction on exact geometry**: every merge-based constraint holds exactly; every other constraint holds within its tolerance band; this is decided exactly. |
| D2 | Geometry is **exact integers** at fixed per-kind scales. One number type. |
| D3 | Coincident, concentric, equal-radius, horizontal, vertical, and fix are **variable merging / constants**: exact by construction. |
| D4 | Every check is a **low-degree polynomial (in)equality over Int**. No square roots, no trigonometry, no real numbers anywhere in the core spec. |
| D5 | Contact points and curve parameters are **explicit variables**. |
| D6 | The proposer (solver) is **untrusted**; the checker is a **decision procedure** for the spec. |
| D7 | Solving means finding the **nearest solution** to the current sketch (weighted projection). First- and second-order optimality are certified; "untouched stays untouched" and "no flips" are laws. |
| D8 | **Exact existence/uniqueness** of a real solution is an **opt-in tier**, still stated and proven over ℚ only (quadratization + contraction with a constant Hessian). |
| D9 | **Lipschitz bounds replace interval arithmetic** everywhere (side conditions over balls, SDF rendering). |

Naming: **tier S** = the core guarantee (D1–D7). **Tier E** = the opt-in exact
existence layer (D8).

---

## 2. Why this shape

**Exact algebraic numbers are infeasible at depth.** Each circle∩circle adjoins
a square root; a chain of k steps puts coordinates in a quadratic tower of degree
up to 2^k. At k = 30 that is ~10^9 rational coefficients per coordinate, and
exact zero tests via separation bounds (BFMSS-style) need on the order of 2^k
times the input bit-size. Fine for k ≲ 5, impossible at k = 30.

**Exact-real semantics with interval arithmetic** (an earlier iteration of this
design: abstract complete ordered field, interval enclosures, Krawczyk existence
certificates, slope transformers, adaptive precision, ideal-membership
certificates for redundancy) is sound but heavy, and its precision cost grows
with chain depth (≈ log₂ of the conditioning, additive per step).

**Tolerance satisfaction (D1) removes most of that machinery:**

- Each constraint is checked against the *actual rounded geometry*, so the
  precision needed depends only on local conditioning, not on chain depth.
- Redundant-but-consistent constraints need no certificates; they are checked
  like any other.
- The spec lives in ℤ; the checker is exact integer evaluation.

**This is not epsilon geometry.** Epsilon geometry (Guibas–Salesin–Stolfi) makes
predicates three-valued with ad-hoc handling of the uncertain branch. Here all
predicates are exact and two-valued on exact geometry; only *dimension targets*
carry tolerance bands. Topology (loop closure, inside/outside) stays exact.
Fornjot's "robustness through explicitness" (relationships stated, never
inferred within tolerance) is the same principle from the B-rep side.

**What tier S does not give** (and tier E does): it accepts a sketch whose
constraints are inconsistent but consistent within ε, and it does not prove a
sketch is fully constrained or that its solution is locally unique.

---

## 3. Numbers

**Spec level.** `Int` = sign + Peano `Nat` (unbounded in Bend's theory). All
laws are stated over spec `Int`.

**Runtime level.** Limb bigints refining spec `Int`:
- Limbs are `Nat` values < 2^16. In the C runtime `Nat` is native but capped at
  2^48 − 1 (it saturates and posts `ERR_NATS`), so 16-bit limbs keep schoolbook
  column sums under the cap; limb-bound laws make the cap unreachable.
- Not `U32` limbs: `U32` is modeled as a 32-bit `Word` (bit list) in the theory,
  which makes proofs bit-level, and there is no `U64` for carries.

**Scales.** Every variable has a kind with a fixed scale; values are integers at
that scale; scale factors enter checks as integer constants.
- Coordinates and lengths: 1 unit = 1 nm (open question Q3: nm vs pm). User
  dimensions in decimal mm are exact integers.
- Curve parameters t: dyadic, 1 unit = 2^−s.
- Angle dimensions: a rational rotation stored as an integer pair (a, b) (§5.3).

**Magnitudes.** ±1 km at 1 nm ≈ 2^40. Quadratic checks ≈ 2^80–2^160; cubic
spline checks with parameter scaling ≈ a few hundred bits. Small bigints.

---

## 4. Sketch IR

- **Variables** with kinds: `coord`, `length`, `param`, `aux`.
- **Entities:** `Point(x, y)`, `Segment(P, Q)`, `Circle(C, r)`,
  `Arc(C, r, S, E, dir)` with endpoints S, E checked on the circle,
  `Ellipse(...)`, `BSpline(degree, knots, control points, weights)`.
- **Merging (D3).** The UI's coincident/concentric/equal-radius/horizontal/
  vertical constraints compile to shared variables; fix compiles to constants.
  Point-on-curve is *not* merging; it is a check with a parameter (D5).
- **Constraints** compile to a list of polynomial checks (§5) plus
  nondegeneracy side conditions (segment length ≥ ℓ_min, radius > 0, NURBS
  weights > 0).
- **Representation:** flat sparse polynomials (list of coefficient + monomial)
  rather than nested expression trees (Bend forbids mutual recursion; flat
  lists keep every function structurally recursive on one list).

---

## 5. Tier S: constraint vocabulary and checks

Notation: u = Q − P, v = D − C, cross/dot are the 2D products. ε is a length
tolerance (in nm units). σ is a rational upper bound on sin²(α) for an angular
tolerance α. ℓ_min is a nondegeneracy length.

**Principle:** each check *implies* its stated geometric meaning (soundness).
Where an exact equivalence is cheap it is used; otherwise the check may be
slightly stricter than the meaning, which only costs the proposer slack.

### 5.1 Core

| Constraint | Encoding | Exact Int check | Meaning implied |
|---|---|---|---|
| coincident, concentric, equal radius, horizontal, vertical | merge | — | exact |
| fix | constant | — | exact |
| distance(P, Q) = d | — | (d−ε)² ≤ \|u\|² ≤ (d+ε)² (lower bound vacuous if d ≤ ε) | \|\|u\| − d\| ≤ ε |
| radius r = d | — | \|r − d\| ≤ ε | same |
| equal length | — | (\|u\|² − \|v\|²)² ≤ ε²·(\|u\|² + \|v\|²) | \|\|u\| − \|v\|\| ≤ ε (and implied by it at ε/√2) |
| perpendicular | — | dot(u,v)² ≤ σ·\|u\|²\|v\|² | angle within α of 90° |
| parallel | — | cross(u,v)² ≤ σ·\|u\|²\|v\|² (optionally dot > 0) | angle within α of 0°/180° |
| point on line AB | — | cross(P−A, B−A)² ≤ ε²·\|B−A\|² | dist(P, line) ≤ ε |
| point on segment | param s | \|P − A − s(B−A)\|² ≤ ε², 0 ≤ s ≤ 1 | dist(P, segment) ≤ ε |
| point on circle | — | (r−ε)² ≤ \|P−C\|² ≤ (r+ε)² | radial error ≤ ε |
| point on arc | — | on circle, plus orientation-sign tests against S, E | on the arc's angular range |
| midpoint M of PQ | — | \|2M − P − Q\|² ≤ 4ε² | \|M − (P+Q)/2\| ≤ ε |
| symmetric P, Q about AB | — | midpoint on line (as above, doubled), dot(Q−P, B−A)² ≤ σ·\|Q−P\|²\|B−A\|² | mirror within ε, α |

Every check involving a direction also carries the nondegeneracy side condition
on that direction's length.

### 5.2 Tangency (contact points, D5)

| Constraint | Variables | Check |
|---|---|---|
| line–circle tangent | contact T, param s | T on line/segment (§5.1); T on circle band; dot(T−C, B−A)² ≤ σ·\|T−C\|²\|B−A\|² |
| circle–circle tangent | contact T | T in both radius bands; cross(T−C₁, T−C₂)² ≤ σ·\|T−C₁\|²\|T−C₂\|²; sign of dot(T−C₁, T−C₂) selects external (< 0) or internal (> 0) |
| G1 join of two curves | merged endpoint | end tangent directions parallel within σ, dot > 0 |

The contact point is exact geometry, so later stages (trimming, profiles) get
the touching point directly.

### 5.3 Angles as rational rotations

A dimension "angle θ" is stored as an integer pair (a, b) with t = a/b ≈ tan(θ/2).
The rotation is R̂ = [[b²−a², −2ab], [2ab, b²−a²]] = (a²+b²)·R(θ'), where
θ' = 2·atan(a/b). Check: cross(R̂u, v)² ≤ σ·\|R̂u\|²\|v\|² and dot(R̂u, v) > 0.

The spec is about θ' exactly; degrees are display. The UI picks (a, b) so that
\|θ' − θ\| is far below α.

### 5.4 Curves

| Constraint | Variables | Check |
|---|---|---|
| point on B-spline span j | param t | \|P − C_j(t)\|² ≤ ε², knot_j ≤ t ≤ knot_{j+1} |
| point on NURBS span j | param t | \|w(t)·P − N(t)\|² ≤ ε²·w(t)², w(t) > 0 |
| curve–spline tangent | contact params | contact check plus tangent directions parallel within σ |
| offset point at distance d | param t | (P − C(t)) ⊥ C′(t) within σ; distance band on \|P − C(t)\| |
| G2 join | — | **open (Q6):** relative band on squared curvature plus sign agreement |
| ellipse / conic | — | implicit conic or rational parametrization; designed in sk-10 |
| arc length | — | **exception:** needs rational enclosures of atan / integrals; built last (sk-15) |

C_j(t) is evaluated exactly in Bernstein form per span (t is rational,
control points are integers).

### 5.5 The tier S theorem

LAWS.bend defines `Sat(sketch, geometry)` as the conjunction of the checks above,
over spec `Int`. The implementation `check` runs on limb bigints.

```
law check_is_sat:
  for +s: Sketch
  for +g: Geometry
  {Sketch.check(s, g) == Sketch.Sat(s, g) : Bool}
```

So `check` is a decision procedure for the spec. Optional per-constraint
meaning lemmas (e.g. the distance band ⇔ \|\|u\| − d\| ≤ ε, stated without √
via squared quantities) document that each check means what the table says.

---

## 6. Proposer: nearest-solution solving

**Objective.** Minimize Σ wᵢ(xᵢ − x₀ᵢ)² subject to F(x) = 0, where x₀ is the
current sketch. The optimizer treats dimension targets as **exact equalities**;
tolerance bands are only for acceptance (otherwise solutions snap to band edges).

**KKT system.** W(x − x₀) + J(x)ᵀλ = 0 and F(x) = 0. This is square in (x, λ)
for under-constrained, well-constrained, and consistently redundant sketches
(after dropping dependent rows), so **no DOF pinning planner is needed**.

**Weights.** Only user geometry carries weight. Contact points, curve
parameters and aux variables get weight 0; otherwise the solver would prefer
moving the user's geometry over moving a contact point. Dragging: the dragged
point's target is the cursor, with a large weight. Default per-entity weights
are a UX decision (Q2).

**Algorithm (untrusted).**
- Gauss–Newton / Levenberg–Marquardt on the KKT system, minimal-norm steps.
- Bend has only F32 (no f64): linear solves in F32, **residuals computed exactly
  in Int**, mixed-precision iterative refinement (Carson–Higham line of work).
  Each step gains roughly F32's precision when well conditioned; ill-conditioned
  clusters fall back to exact/dyadic elimination.
- Connected components of the constraint graph are solved independently
  (fork-join parallel in Bend).
- **Projected continuation** for large edits: move a dimension in small steps,
  projecting each from the previous, so the solution stays on its branch.
- Redundancy: rank-revealing QR (untrusted) drops dependent rows for the
  optimization; the tier S check still checks every constraint. Conflicts:
  constraints whose bands cannot be met are reported.
- DOF reporting in v1 is untrusted (QR); certified DOF is later (sk-14).
- Termination: fuel. Completeness is not proven in v1.

**Reference (not a dependency):** neoscad/sketch-solver uses a similar
architecture (deterministic LM, continuation from drawn to target dimensions,
QR diagnostics, flip detection). It is very new; use it for ideas only.

**Where it runs:** in Bend by default (one toolchain). Bend files are importable
from JS, so an external proposer is possible but not planned.

---

## 7. Nearest-solution certification (tier S, core)

**N1 — first-order (stationarity).** The proposer returns λ (rational, fixed
scale). Check exactly: ‖W(x − x₀) + J(x)ᵀλ‖∞ ≤ τ.

**N2 — second-order (not a saddle).** Let H_L = W + Σ λᵢ·∇²Fᵢ(x), evaluated
exactly at the computed point. Check H_L is positive definite on the tangent
space null(J(x)):

1. The proposer names basic columns B and supplies M with
   **M·J_B = I and J_B·M = I**, both checked exactly. (Checking both sides
   avoids any rank–nullity argument.)
2. Null-space basis Z = [−M·J_N ; I] (after the column permutation). JZ = 0
   follows from J_B·M = I; every v with Jv = 0 equals Z·v_N follows from
   M·J_B = I.
3. The proposer supplies L (unit lower triangular) and D (diagonal) with
   Zᵀ H_L Z = L D Lᵀ checked exactly and every Dᵢᵢ > 0. Then
   vᵀ(ZᵀH_LZ)v = Σ Dᵢᵢ (Lᵀv)ᵢ² > 0 for v ≠ 0.

N1 + N2 are certified facts about the computed point: approximately stationary,
with positive curvature on the tangent space. The exact strict-local-minimum
claim needs tier E (§8.6).

**L1 — untouched stays untouched.** Components of the constraint graph that
contain no edit come back bit-identical. Enforced by construction: the final
step copies original values for untouched components (their constraints only
involve their own variables, so they stay satisfied). Proven as a law about
`solve`.

**L2 — no flips.** For designated anchor triples, orient(P, Q, R) has the same
sign before and after. Exact determinant sign check; a violation is reported as
a flip rather than silently accepted. The default anchor policy is open (Q7).

---

## 8. Tier E (opt-in): exact existence and uniqueness over ℚ

### 8.1 Quadratization

Introduce aux variables so every equation is quadratic:
- √a → s with s² = a, s ≥ 0.
- a/b → q with q·b = a, b ≠ 0.
- degree > 2 products → y = x·z, repeatedly.

Then the second-derivative tensor T (T_ijk = ∂²f_i/∂x_j∂x_k) is **constant**.

### 8.2 Midpoint identity

For quadratic f: **f(x) − f(y) = J((x+y)/2)·(x − y)** exactly. Proven once
(ring normalizer).

### 8.3 Certificate

Rational data (x̃, Y, r, q, q′) from the proposer; ∞-norms throughout (no √).
Let κ = maxᵢ Σⱼ Σₖ \|T_ijk\|, so ‖J(x) − J(x̃)‖∞ ≤ κ·‖x − x̃‖∞.

Exact checks:
1. q₀ = ‖I − Y·J(x̃)‖∞ and q = q₀ + ‖Y‖∞·κ·r < 1.
2. ‖Y·f(x̃)‖∞ ≤ (1 − q)·r.
3. q′ = ‖I − J(x̃)·Y‖∞ < 1.

With g(x) = x − Y·f(x) and m = (x+y)/2 in the ball B = B∞(x̃, r):
g(x) − g(y) = (I − Y·J(m))(x − y), and ‖I − Y·J(m)‖∞ ≤ q, so g contracts by q
and maps B into B.

### 8.4 Theorems (ℚ only)

- **Approximate solvability:** ∀k. ∃x ∈ ℚⁿ ∩ B with ‖f(x)‖∞ ≤ 2^−k.
  Witness: simplified-Newton iterates xₙ₊₁ = g(xₙ) from x̃, with
  ‖f(xₙ)‖ ≤ ‖J(x̃)‖·qⁿ·‖Y·f(x̃)‖ / (1 − q′)
  (from f = J(x̃)·Y·f + (I − J(x̃)·Y)·f).
- **Approximate uniqueness:** ∀x, y ∈ B:
  ‖x − y‖ ≤ (‖Y·f(x)‖ + ‖Y·f(y)‖) / (1 − q).

Meta-level (documented, not formalized): since B is compact and f is
continuous, these two statements together say exactly that f has one real root
in B. The formal statements never mention ℝ.

### 8.5 Side conditions over the ball

For quadratic g: g(x) ≥ g(x̃) − ‖∇g(x̃)‖₁·r − ½·Σⱼₖ \|∂²g/∂x_j∂x_k\|·r²
on B. Checking that this lower bound is > 0 proves the condition over all of B.
Exact constants, no intervals; the same idea as Lipschitz pruning for SDFs.

### 8.6 Applications

- Whole-sketch consistency and local uniqueness.
- The KKT system from §6 (also quadratic after quadratization): an exact KKT
  point exists and is unique in the ball; with a margin on N2's pivots it is a
  strict local minimum (margin argument designed in sk-13).
- x̃ may be a refinement of the displayed integer geometry; the result reports
  ‖x̃ − displayed‖.

### 8.7 Cost

Precision ≈ log₂(conditioning) bits, additive in chain depth. Tier S never pays
this; tier E pays it only when asked.

---

## 9. Profiles and the SDF bridge

- **Profiles** are closed loops of segments with merged endpoints, so they are
  exactly closed. The winding number is well defined everywhere off the curves;
  no near-closed-polygon leaks.
- **Exact inside tests at rational points:** lines by orientation signs; arcs by
  \|p − c\|² vs r² plus angular-range signs; splines by counting real roots of
  the span polynomial along a ray (Sturm, or Descartes/Bernstein on [0, 1]),
  later. Fill rule open (Q5).
- **SDF generation** from exact parameters, converted to F32 for shaders. Bend's
  F32 is axiomatic, so shader numerics are not verified.
- **Optional spec-level laws** over an abstract Euclidean field record (ordered
  field with √ of nonnegatives), one per operator:
  - sign agreement with the exact inside test;
  - 1-Lipschitz (|f(p) − f(q)| ≤ |p − q|), so sphere tracing never steps
    through a surface;
  - min, max, polynomial smooth-min, extrude, revolve preserve 1-Lipschitz.
- **Rendering acceleration:** Lipschitz pruning (Barbier et al. 2025) and
  Keeter's point-sample pseudo-intervals (one sample plus the Lipschitz radius
  bounds a region), instead of interval arithmetic.
- With tier E, if the SDF is L-Lipschitz in its parameters, the displayed SDF is
  within L·r of the exact one everywhere.

---

## 10. Bend engineering notes

- **No common-subexpression elimination** (WONTFIX) and affine values: always
  evaluate forward over an environment; never recurse over a DAG (a depth-30
  fan-in-2 DAG unfolds to ~2^30 calls).
- Geometry values are `Data` (`+`, refcounted); closures and arrays are affine
  `Type`.
- **Termination:** iterative loops take a fuel `Nat` as their first argument
  (the checker reads arguments left to right).
- **No tactics:** a reflective ring normalizer over spec `Int` (AST, eval,
  normalize to sorted monomials, soundness law) proves polynomial identities in
  one `{==}` step: bigint refinement, §8.2, LDLᵀ identities, check/meaning
  lemmas.
- **No mutual recursion:** flat polynomial IR (§4).
- No `if`; matches only on parameters / pattern variables: helper-heavy style.
- **F32 only:** proposer uses F32 plus exact-residual refinement (§6).
- **Nat runtime cap 2^48 − 1:** limb bounds proven (§3).
- **Parallelism:** fork-join over independent components and over the
  constraint list (balanced split).
- **Laws workflow:** LAWS.bend is human-owned; open laws are the roadmap;
  `bend PROOF.bend` is the gate.
- The README notes the Lean formalization lags bend.ts; optionally mirror the
  top-level statements in Lean.

---

## 11. Trusted base

**Trusted:** the Bend kernel/checker; LAWS.bend (spec `Int`, sketch IR, `Sat`
definitions, top theorems); optionally the Euclidean-field axioms for SDF laws.

**Not trusted:** the proposer; F32 rendering; the UI → IR compiler (it decides
which entities a user constraint refers to; a later milestone may verify it).

---

## 12. Milestones

| ID | Milestone | Depends on | Exit criterion |
|---|---|---|---|
| sk-00 | Scaffold: LAWS/PROOF/main layout, gate script | — | `bend PROOF.bend` green on an empty law set |
| sk-01 | Spec `Int` + reflective ring normalizer | sk-00 | normalizer soundness law closed; (a+b)² identity is one line |
| sk-02 | Limb bigint refining spec `Int` (add, sub, mul, cmp, limb bounds) | sk-01 | refinement laws closed; 256-bit mul benchmark |
| sk-03 | Sketch IR, kinds/scales, merging, `Sat` for the core vocabulary in LAWS | sk-02 | LAWS reviewed by Danielle |
| sk-04 | `check_is_sat` for §5.1 + §5.3 + nondegeneracy | sk-03 | law closed |
| sk-05 | Tangency via contact points (§5.2) | sk-04 | law closed, examples |
| sk-06 | Proposer v0: KKT / min-norm GN, F32 + exact refinement, components, drag, projected continuation, flip detection | sk-04 | fixture sketches solve and pass `check` |
| sk-07 | N1, N2, L1, L2 | sk-06 | laws closed |
| sk-08 | Depth-30 circle-chain benchmark (well- and ill-conditioned) | sk-06, sk-07 | timing + precision report |
| sk-09 | Splines: Bernstein spans, B-spline/NURBS, point-on, tangency, G1, offsets, fit splines; decide G2 (Q6) | sk-04 | law closed for spline vocabulary |
| sk-10 | Ellipses / conics | sk-04 | law closed |
| sk-11 | Profiles: loops, exact inside tests (lines/arcs), fill rule; spline inside via root counting | sk-05, sk-09 | inside-test law closed |
| sk-12 | SDF bridge: export, renderer with Lipschitz pruning; optional SDF laws | sk-11 | render demo; optional laws |
| sk-13 | Tier E: quadratization, certificate, §8.4 laws, §8.5, KKT certification | sk-04, sk-07 | laws closed |
| sk-14 | Certified continuation (Lee 2025) and certified DOF (Burr–Hauenstein–Lee 2026) | sk-13 | design + prototype |
| sk-15 | Arc length and other transcendental dimensions | sk-13 | design + law |

---

## 13. Open questions (for Danielle)

- **Q1.** Tier S as the core guarantee, tier E opt-in per sketch or cluster?
  (Recommended.)
- **Q2.** Nearest-solution metric: per-entity weights, rigid-motion term?
- **Q3.** Grid scales (nm vs pm) and default ε, σ, ℓ_min.
- **Q4.** Proposer location: Bend only, or allow an external JS proposer?
- **Q5.** Fill rule: nonzero or even-odd.
- **Q6.** G2 tolerance formulation.
- **Q7.** Anchor-triple policy for the no-flip law.

---

## 14. Risks

- **R1** Bend is young: kernel bugs, checker speed on reflection-heavy proofs.
- **R2** F32-based proposer convergence on ill-conditioned clusters.
- **R3** Tier S accepts near-inconsistent sketches (mitigation: tier E).
- **R4** Checks stricter than meanings may reject solutions the user considers
  fine (mitigation: proposer targets the exact equalities, leaving slack).
- **R5** Bigint sizes for spline and NURBS checks (degree × scale): bound and
  benchmark.
- **R6** Arc length needs real analysis in the spec.
- **R7** Spline inside tests need verified real-root counting.

---

## 15. References

- Barbier et al., *Lipschitz Pruning: Hierarchical Simplification of
  Primitive-Based SDFs*, Eurographics 2025. https://diglib.eg.org/handle/10.1111/cgf70057
- Keeter, *Gradients are the new intervals*, 2025.
  https://www.mattkeeter.com/blog/2025-05-14-gradients/
- Hubert-Brierre et al., *Accelerating Signed Distance Functions*, CGF 2025.
  https://diglib.eg.org/items/1a39a460-61c5-4b38-8486-d86353d2d6a4/full
- Lee, *A priori bounds for certified Krawczyk homotopy tracking*, arXiv
  2512.01355. https://arxiv.org/abs/2512.01355
- Burr, Hauenstein, Lee, *Certified surface approximations using the interval
  Krawczyk test*, arXiv 2602.07718. https://arxiv.org/abs/2602.07718
- Hauenstein, Sottile, *alphaCertified: certifying solutions to polynomial
  systems*, ACM TOMS 2012.
- Carson, Higham, mixed-precision iterative refinement (2017–2018).
- Peyrl, Parrilo, *Computing sum of squares decompositions with rational
  coefficients*, TCS 2008 (only for the skipped global-nearest certificate).
- Draisma et al., *The Euclidean distance degree of an algebraic variety*,
  FoCM 2016 (background on nearest-point critical points).
- Guibas, Salesin, Stolfi, *Epsilon geometry*, 1989.
- Fornjot (fj-core docs), "robustness through explicitness".
  https://docs.rs/fj-core/0.49.0/fj_core/
- Zou et al., *A review on geometric constraint solving*, 2022.
  https://arxiv.org/abs/2202.13795
- neoscad/sketch-solver (reference architecture only).
  https://github.com/neoscad/sketch-solver
