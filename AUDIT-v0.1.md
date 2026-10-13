# Audit of DESIGN.md v0.1

Independent audit by a separate Claude Opus 5.5 agent, 2026-10-13. Kept as the
record behind DESIGN.md v0.2. Finding IDs (B1, M1–M14, Minor 1–14) are
referenced in the v0.2 changelog. One closing paragraph about an operational
incident during the audit was removed; it is unrelated to the design.

The audit's verification basis: the math was derived by hand (not
machine-checked); Bend claims were checked against the repo source, plus the
in-repo checker run in memory to time Nat arithmetic; citations were checked by
fetching arXiv pages, Crossref metadata, READMEs and full texts; the N2 cost was
estimated from determinant and minor size bounds, not benchmarked.

## Verdict (summary)

The core idea holds up: exact integer geometry, tolerance bands decided
exactly, and an untrusted solver. Most §5 checks and all of §8.2–8.5 survive.
Not ready to build as written:

- **Before sk-03, fix:** B1 (Finsler-based N2, or move N2 to tier E), the arc
  representation (M1), the wrong meanings (M2, M3), and the tolerance-vs-grid
  policy (M4).
- **Restructure:** typed IR with mandatory meaning lemmas, one acceptance
  theorem over arbitrary proposals, and an honest trusted base (M8–M10).
- **Reword:** the overstated claims (M5–M7).
- **Plan for M11:** unary checker arithmetic and from-scratch Int, bigint,
  rational and matrix libraries make sk-01/02 much heavier than they look.
- **Reorder risk-first:** prototype the proposer and the depth-30 chain with an
  untrusted solver before the proof work.

## Blocker

**B1. §7 N2 does not scale.** M = J_B⁻¹ has denominators det(J_B), and LDLᵀ
entries of ZᵀH_LZ are ratios of minors. For a component with 120 constraints
and 30 DOF, Jacobian entries ~2^41: M entries ~5,300 bits, ZᵀH_LZ ~11k bits,
LDLᵀ ~300k bits; verifying ZᵀH_LZ = LDLᵀ is ~10⁴ products of 300k-bit numbers,
~10¹²–10¹³ 16-bit-limb operations. Hours or worse per solve. Small components
(~20 constraints) are fine. **Fix:** Finsler/Debreu form. Proposer supplies
ρ ≥ 0 and a dyadic unit-triangular T; checker verifies Tᵀ(H_L + ρJᵀJ)T is
strictly diagonally dominant with positive diagonal (entries ~100–150 bits).
Soundness: Jv = 0 ⇒ vᵀ(H_L + ρJᵀJ)v = vᵀH_Lv, plus a Gershgorin lemma. Drops
basic columns, M, the two-sided inverse and the full-row-rank requirement.
Alternatively move N2 to tier E.

## Major

**M1. §4/§9 arcs break exact closure.** `Arc(C, r, S, E)` only bands S and E to
within ε of the circle; trim and contact points likewise. Gaps up to ε at every
arc join; "exactly closed" and "no leaks" are false with arcs. **Fix:** in
sk-03 choose a representation where curves pass through merged endpoints by
construction (arcs as rational quadratic Béziers through S, E with circularity
as a band, or arc plus radial connectors; clamped B-splines merge endpoints
with end control points).

**M2. §5.1 symmetric is wrong.** |Q − mirror(P)|² = 4h_m² + |d∥|², so the
check bounds the error by √(4ε² + σ|PQ|²): a factor 2 on ε plus an angular
term growing with |PQ| (100 mm apart, α = 10⁻⁶ → ~100 nm). **Fix:** exact
positional check with w = B − A,
R̂ = [[wx²−wy², 2wxwy], [2wxwy, wy²−wx²]]:
‖|w|²(Q−A) − R̂(P−A)‖² ≤ ε²|w|⁴ (degree 6, means exactly |Q − mirror(P)| ≤ ε).

**M3. §5 σ bounded in the wrong direction.** "σ is a rational upper bound on
sin²α" accepts deviations slightly beyond α; soundness needs σ ≤ sin²α.
**Fix:** specify the tolerance as a rational half-angle tangent p/q, so
sin²α = (2pq)²/(p²+q²)² exactly.

**M4. §3/§5 fixed angular tolerances can be unsatisfiable on the grid.** A grid
direction on a segment of length L has resolution ~0.7 nm / L; guaranteed
satisfiable only when α ≳ 0.71 nm/ℓ_min. Counterexample: CD ⊥ AB, |CD| = 10 µm,
α = 10⁻⁶: admissible region ~2 nm × 0.02 nm, usually no lattice point.
Conversely α is loose on long entities. **Fix:** positional, length-scaled
tolerances for direction checks (or tie α to grid/ℓ_min), plus a rounding
lemma: every exact solution rounds to a grid point satisfying `Sat` under
stated conditions.

**M5. §2 "precision independent of chain depth" holds only for `Sat`.** N1's
residual at a rounded point has a floor ~‖H_L‖·δ and ‖λ‖ grows like
‖x−x₀‖/σ_min(J), exponential in depth for ill-conditioned chains, so a fixed τ
fails spuriously or certifies nothing. N2's certificate grows with component
size. F32-factorization iterative refinement stops converging around κ ≈ 10⁷
(practically 10⁵–10⁶; Carson–Higham 2018, Table 7.1). **Fix:** state precisely;
make τ relative, or move N1/N2 out of the core.

**M6. §6 KKT square but not reliably nonsingular.** Needs J full row rank and
ZᵀH_LZ nonsingular. Counterexamples: drag target at a circle's center (focal
point; every circle point stationary); zero-weight variables free in null(J);
rank lost only at the solution (near-tangent circle∩circle). Inequalities
(0 ≤ s ≤ 1, dot > 0, arc ranges, tangency side) need active-set logic.
**Fix:** tiny positive weights instead of 0, "generically nonsingular", LM
damping, an active set.

**M7. §8.6 tier E "whole-sketch consistency" unsupported for redundant
sketches.** The certificate needs a square nonsingular system. Under-constrained
sketches work through the KKT system (a KKT root implies F = 0); say so. Rows
dropped for redundancy are not certified. **Fix:** scope the claim; optional
redundancy certificates (F_k = Σ cᵢFᵢ checked by the normalizer).

**M8. §4/§5.5/§11 gap between user meaning and IR.** Unclear whether the IR
holds typed constraints or raw polynomials; if the untrusted UI→IR compiler
emits polynomials, `Sat` says nothing about "distance". Meaning lemmas are
optional yet are the only machine-checked link to meaning (would have caught
M2, M3). The compiler decides references, merges, σ, (a, b), branches, spans,
x₀ and W. **Fix:** typed IR with `Sat` per constraint kind in LAWS.bend;
compile to polynomials inside `check`; mandatory meaning lemmas; typed IR as
the persisted source of truth, re-checked on load and save.

**M9. §11 trusted base incomplete.** Missing: comp.ts emitters/runtimes
including the native mapping of Base's Nat ops ("99% AI-written and has not
been fully audited"); clang; base.bend; the logic (Type : Type with a live/dead
wall; bend.lean mismatches bend.ts). The JS boundary passes values unchecked
(negative BigInt as Nat, malformed constructors). **Fix:** list them, test
lanes against each other on random sketches, validate inputs inside Bend.

**M10. No single top-level acceptance theorem.** Laws are scattered; L1 is "a
law about `solve`", which would rely on foreign code if the proposer is
external. **Fix:** one law over an arbitrary proposal p:
`accept(sketch, edit, p) = Ok(g)` ⇒ `Sat`, untouched, no flips, (N1/N2). The
proposer leaves the trust story, which also settles Q4.

**M11. The checker evaluates Nat in unary.** Measured: `{==}` on
Nat.is_lt(10⁶, 10⁶+1) took 1.3 s; Nat.mul(1000, 1000) < 10⁶+1 took 2.9 s.
Closed facts about 2^16, 2^32, 2^48, the nm/mm factor, 2^S scales or large σ
numerators can never be decided by computation. Keep radix and scales symbolic;
normalizer coefficients atoms or binary; sign-magnitude Int needs a canonical
zero. **Fix (decide in sk-01):** Int as `ofNat n | negSucc n`; binary or atomic
coefficients; scale constants as erased parameters with defining equations.

**M12. Parity gaps.** External references (projecting model edges) impossible
with SDF and no B-rep; acknowledge. Crossing curves need an arrangement
(feasible exactly; one square root per intersection). Missing dimension kinds:
horizontal/vertical distance, point–line, line–line, point–circle,
circle–circle, arc sweep, driven/reference. Missing workflow: expressions and
variables; construction geometry; trim/extend/split/fillet (fit D5 as new
points with point-on constraints); offset-curve entity; Normal, Block, Snell.

**M13. Milestones not risk-first.** sk-08 benchmark and proposer feasibility
come after all proofs; Q3 is unscheduled; sk-03 doesn't need sk-02; missing a
rational/matrix library milestone and integration (UI, persistence, host);
sk-06 overloaded; no performance criteria. `bend` exits 0 with "relies on
unsafe or foreign code", so the gate must fail on that line; open laws make the
gate red, so keep roadmap laws in a file PROOF.bend does not import.

**M14. §7 L1 underspecified.** "Untouched" must be defined in LAWS (otherwise a
partitioner marking everything touched satisfies L1 vacuously): proposer
supplies a partition; checker verifies closure and that edits lie in touched
parts. "Stays satisfied" assumes it was satisfied before (fails for loaded or
failed sketches, global tolerance changes). Merges/unmerges change variables:
define a correspondence. Anchor triples spanning two components can report
false flips.

## Minor

1. Equal length: valid but strict; exact degree-4 equivalent exists, e.g.
   A − B − ε² ≤ 0 or (A − B − ε²)² ≤ 4ε²B, both directions (A = |u|², B = |v|²).
2. Point on circle: lower bound vacuous when r < ε; require ℓ_min > ε.
3. Point on segment: dyadic s at scale 2^−S quantizes the foot by |B−A|·2^−S
   (needs S ≥ 41); or drop s and use the line check plus
   0 ≤ dot(P−A, B−A) ≤ |B−A|².
4. NURBS row missing knot_j ≤ t ≤ knot_{j+1}; w(t) > 0 follows from positive
   weights.
5. Tangency meaning unstated; derived |dist(C, line) − r| ≤ 2ε + r(1 − cos α).
6. Offset check is local (foot point), not a global distance; needs C′(t) ≠ 0.
7. N2 at an approximate point shows PD for the proposer's λ at a point neither
   feasible nor stationary; "certified optimality" overstated.
8. §8.4: the two statements imply exactly one real root in B (not
   equivalent); uniqueness after quadratization holds in the lifted box.
9. §8.2 needs induction over terms; integer form
   2(f(x) − f(y)) = (2b + T(x+y))(x − y) avoids the ½.
10. §4 rationale: binary-tree ASTs need no mutual recursion, and datatypes may
    be mutually recursive. The real issue is DAG sharing with no CSE; a
    straight-line program over an environment beats expanded sparse
    polynomials, which blow up for spline checks.
11. Bend limits: Nat literals cap at 4294967295n; JS lane single-core and deep
    non-tail recursion overflows (#798); no native library target (#813), so
    no embedding in a C/C++ host today.
12. F32 proposer: scale residuals above ~2^128 before conversion; F32 → Int
    needs F32.bits decoding (F32.to_u32 returns 0 for negatives and ≥ 2^32).
13. D2 "one number type": λ, M, LDLᵀ, tier E and NURBS need rationals.
14. Unspecified: merge-conflict errors; construction flag; per-constraint
    check results; drag as hard equality; imperial fractions below 1/64" not
    exact at 1 nm; circular patterns accumulate n·|θ′ − θ|.

## Nits

- Objective vs KKT factor of 2 (absorbed into λ; consistent with H_L).
- "No flips" is really "flips are reported".
- Two-sided inverse check redundant for square matrices (moot under B1's fix).
- §8.3: q, q′ are computed by the checker; check 3 is a formal convenience.
- "Saturates and posts ERR_NATS" is GPU behavior; CPU prints and exits, JS
  throws. All lanes fail-stop.
- "One `{==}` step" is a rewrite with the soundness lemma, then `{==}`.

## Claims that check out

Distance band (exact, incl. vacuous lower bound); radius; equal length (both
directions); perpendicular/parallel (apart from M3); point on line (exact, B ≠ A);
point on segment (implies); midpoint (exact); circle–circle tangency sign
selection; rational rotation R̂ = (a²+b²)R(θ′) and the angle check; NURBS
equivalence when w ≠ 0; §8.2 identity; κ bound; §8.3 contraction and
maps-into-B; §8.4 residual bound and uniqueness inequality (together imply one
real root); §8.5 lower bound; N2 algebra. All Bend claims checked against the
repo: Peano Nat in theory, native with 2^48 − 1 cap; U32 = Word(32), no
U64/I64/F64; F32 axiomatic; affinity, Data vs Type; no CSE (#812); termination
left to right; no mutual recursion of defs; erased args, laws, open laws, the
gate; JS imports non-IO defs with Nat as BigInt; no `if`; Lean model lags.

## Literature

All 13 citations exist. Corrections: Burr–Hauenstein–Lee certifies local
manifold structure assuming dimension and full rank, not DOF or redundancy.
"Ad-hoc" is unfair to epsilon geometry (GSS 1989 has a calculus of
ε-predicates with warranties close to tier S's semantics). Carson–Higham gains
~24 − log₂(c·n·κ) bits per step, not "F32's precision"; exact-residual solving
matches Wan 2006 and Saunders–Wood–Youse 2011 better. Keeter needs a true
Lipschitz constant ≤ 1 and reported mixed performance. Fornjot says the
principle is not fully implemented and still validates with an epsilon.
neoscad: all claims check out (created 2026-10-07, 2 commits). Missing: BFMSS
(Burnikel, Funke, Mehlhorn, Schirra, Schmitt 2001/2009), Krawczyk / Rump for
§8.3, Duff & Lee (ISSAC 2024) as the base of Lee 2025.
