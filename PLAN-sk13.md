# Plan: sk-13, generic dependencies (written 2026-10-18 for a fresh session)

**The design** is DESIGN.md §8.11, with Danielle's decisions Q20–Q27 in
§16 (Q24–Q27 after the second review of the sk-09 laws,
AUDIT-sk09-laws.md). This file is the order of work, the references, and what to check
before each step. Read §8.11 first.

**In one paragraph.** v1 finds red constraints by counting. When
constraints depend on each other through geometry (a repeat, a chain of
parallels, a fourth right angle), counting cannot see it. The kept block
is singular, and the solver refuses with nothing red, after retrying
every precision. sk-13 makes every refusal a theorem:
- an **implied** equation is dropped from the system solved, with a
  certificate; its constraint still holds (shown amber when all its
  equations were dropped);
- a red constraint is **conflicting** or **over-determined** (today's
  `Why`), dropped whole;
- a **singular configuration** is reported as such.

Dependencies are found by layers, cheapest first: linear, directions,
lengths, then the witness method. Each candidate the witness proposes is
decided exactly by a Gröbner basis (modular F5 with an exact check), run
side by side with a ball-arithmetic nonzero test.

## Ground rules (Danielle's, standing)

- **Verified and complete (D7).** Every answer is a law, and every stage
  is proven to succeed where it should. A checked search is fine only
  when its termination is proven too.
- **Prove the solver as it runs.** No check-and-fallback paths added just
  to ease a proof. F5's own termination gets proven; there is no
  Buchberger fallback.
- **Exact, comprehensive, fastest.** No degree bound: each decision is
  exact. Use the fastest algorithm even at a higher proof cost.
- **Workflow.**
  - Drafts in `tools/drafts/*.draft` are expanded by `tools/expand.py`;
    edit the draft, never the generated lib file.
  - The gate is `./check.sh`: about 50 s, with tests checked in parallel,
    each its own root.
  - The native regression is `tools/regress.sh` (about 2 min, set by the
    slowest GUI sketch).
  - Commit freely in bend-cad. Implement code yourself, not with agents.
- **Bend idioms** are in memory (`reference_bend2_idioms`):
  - rewrite orientation;
  - callees before callers;
  - `+` for reused parameters, `1n++j` for a reused predecessor;
  - a check fully checks all imports, but the unsafe report covers the
    root's own defs only.
- **Before sk-13a (done):** Danielle read the six sk-09 law drafts in
  ROADMAP.bend and thinks they look good (2026-10-18). The independent
  review the same day (AUDIT-sk09-laws.md) found the soundness laws
  stated for level 0 only; they now hold at every level (Q25). Its other
  findings are folded into Phase 1 and the pins milestone.

## Phase 0: evidence and the regression set (done 2026-10-18)

Done: `proto/sketches/` (README there), in `tools/regress.sh`; the raw
inputs are made with `tools/diag/replay.mjs --repeats`. What follows is
the plan as written.


- Copy the GUI sketches into the repo, as `proto/sketches/` or similar:
  `/home/bepis/prog/verus-cad/slowsketches/` holds `sketch.json` and
  `sketch(1).json` through `sketch(4).json`.
- Add them to `tools/regress.sh` with expected answers and a time limit.
- Run the solver on the raw requests too, including the repeats the page
  now drops, so later phases show the change from "refused" to "amber".
- What they are:
  - `sketch.json`: certified in 0.6 s since the `dsig` fix; it never
    finished before.
  - `sketch(1)`: certifies.
  - `sketch(2)`: `onCircle` three times.
  - `sketch(3)`: two `onCircle` pairs repeated.
  - `sketch(4)`: (3) plus a direction dependency, worked out in
    tools/diag/README.md §4.
- The diagnosis tools are in tools/diag/ and proto/probe_*.bend.

## Phase 1, sk-13a: dropped equations, conflicts, and the linear layer

Revised 2026-10-18 for Q24 (DESIGN §8.11, §16): implied equations are
dropped inside the solve, never whole constraints; amber constraints stay
in the meaning; side conditions are never dropped. Red is Conflict or
Over, dropped whole. **Superseded in detail by SK13A-REVIEW.md v2** (after
AUDIT-sk13a-drafts.md, on Q28's principle: judgments as (in)feasibility
with certificates): the laws are solve_amber, a box-free solve_drop,
solve_conflict with a support, and solve_deg0; the first layer eliminates
over all equations (degree 0) and decides side conditions by
Fourier–Motzkin. Where the bullets below differ, the review document
wins. **Now superseded by PLAN-sk13a.md** (the order of work for v3:
derivations, completeness laws, semantic corollaries; exact simplex for
side conditions).

- **The answer** gains one field, `drop`: the dropped equations (in the
  sketch's numbering, `SK.Sketch.eqs(sk)`) with their certificates
  h·g_j ≡ Σ qᵢ·gᵢ. In this phase h = 1 and the qᵢ are constants; the type
  takes expressions so Phases 2–4 reuse it. Amber, for the page, is a
  constraint all of whose equations are dropped.
- **`Why`** becomes a sum type: `Over` (today's) and `Conflict` (the
  certificate h·g_j ≡ Σ qᵢ·gᵢ + k, k a nonzero constant, over kept
  equations and the constraint's own). `explained₂` checks both, with
  `clean` (no spare flag) kept for both, and `distinct(red)`.
- **The spec** (spec/solve.bend): the solved system is
  eqs(mark(red, sk)) less the dropped equations; `cert_ok` checks one
  certificate with the ring normalizer, over equations that are solved
  (not dropped, not red), so no two certificates lean on each other.
- **The verdict** (`final`): the plan checks the solved system; each
  certificate is checked; h ≠ 0 over the box (trivial for h = 1); the
  side conditions are those of mark(red, sk), amber constraints' included.
- **Proof of soundness**: Zeros(solved) and the certificates give
  Zeros(eqs(mark(red, sk))), so `solve_exists`, `solve_unique` and
  `solve_pins` keep their statements. New: `solve_drop` (every x in the
  box satisfying the solved equations satisfies each dropped one) and
  `solve_conflict` (no x satisfies a Conflict's equations with the kept
  ones).
- **The linear layer**: equations that are linear (Fix, HDistance,
  VDistance, Midpoint, Radius, Diameter, merges included), processed in
  constraint order, eliminated exactly over the dyadic constants against
  the solved ones so far. A residual with a variable: solved. Residual 0:
  dropped (implied). A nonzero constant: the constraint is red, Conflict.
  This gives Q21 (the last in order). Constant side conditions that fail
  (d = −5 ≥ 0) make the constraint red, Conflict, too.
- **Then today's structural stage** runs on the solved system.
- **The review's items folded in** (AUDIT-sk09-laws.md):
  - `solve_total` v2: with `drop_of(sk)`, and a matching of the solved
    equations into the free variables in place of the count (lib/maxpf
    has the facts);
  - `solve_complete` v2: Regular for the solved system;
  - the drawing has one value per variable (in `final`);
  - `dyadic(mark(red_of(sk), sk))` in place of `dyadic(sk)`;
  - the plan's pins are the reported pins (in `final`).
- **Laws**: drafts in ROADMAP.bend, restated in tests/ so lawsync covers
  them; staged with Danielle before they are called done.
- **Exit**: the gate passes; the new laws proven; the regression set
  unchanged except where a linear dependency now drops (e.g. a repeated
  Fix: amber where it was Over). New test sketches: hdistance a–b, b–c,
  a–c consistent (amber) and not (Conflict); the partly implied midpoint
  pair (certifies, nothing flagged); Distance 5 and −5 (Conflict).

## After Phase 1: pins from the drawing (Q26)

Structural pins make exactly drawn axis-aligned sketches singular
(AUDIT-sk09-laws.md 3: a horizontal segment with only a length is
refused). Choose the pins from the drawing's Jacobian (rank-revealing
pivoting). This changes `solve_total` ("pins from the sketch alone") and
reopens part of `solve_complete`'s proof: a choice made at a drawing near
x must stay regular at x. Design it before Phase 2.

## Phase 2, sk-13b: directions

- Labels are Gaussian dyadics (c + is, as dyadic pairs). Parallel is
  label 1, Perpendicular is i, an Angle is c + is. A frame node joins the
  segments that are horizontal or vertical by a merge, with label 1 or i.
- A union–find with labels, written functionally in Bend. A cycle whose
  label product is real makes its closing edge implied. Otherwise the
  cycle is a conflict.
- The path lemma, by induction on the path:
  |b|²·cross(g₁g₂·a, c) = dot(g₁·a, b)·cross(g₂·b, c) + cross(g₁·a, b)·dot(g₂·b, c).
  - It was checked exactly on random Gaussian rationals (2026-10-18).
  - Perpendicular is cross(i·a, b) = −dot(a, b).
- Q15 allows zero-length segments. So |b|² > 0 for the interior segments
  is proven over the certified box with ball arithmetic, as side
  conditions are (§8.6).
- Exit: sketch(4) certifies, with #38 amber (or whichever constraint is
  last in its cycle); a conflicting angle cycle comes back red; the gate
  and the regression pass.

## Phase 3, sk-13c: lengths

- Squared-length nodes (point pairs, squared radii) with constant anchors
  d². EqualLength is an edge; Distance, Radius and Diameter are anchors;
  OnCircle ties a pair to a radius.
- A class anchored twice is implied if the anchors agree, a conflict
  otherwise. Signs come from side conditions (r > 0, d ≥ 0).
- Exit: test sketches (equal-length triangles, a distance repeated through
  an equal length) behave; the gate passes.

## Checkpoint with Danielle (before Phase 4)

Measure how often anything still reaches the witness layer on the
regression set and on new GUI sketches. Then review the scope of Phase 4
together: it is the large one. Settle there (DESIGN §8.11's correction):
the exact decision per candidate is implied / not this one, and conflict
is its own exact test (1 ∈ I + (g_c), degenerate solutions removed).

## Phase 4, sk-13d: the witness layer and the exact decision (large)

Order inside the phase:

1. **Polynomials and Gröbner theory in Bend.**
   - Sparse polynomials over a field, the degree-reverse-lexicographic
     order, reduction, S-polynomials.
   - Buchberger's criterion (all S-pairs reduce to 0 ⇒ Gröbner basis) and
     membership by reduction.
   - Port from AFP `Groebner_Bases` (General, Reduction, Groebner_Bases,
     Macaulay_Matrix).
2. **The checker** for a claimed basis: each element built from the inputs,
   each input reducing to 0, each S-pair reducing to 0. Proven sound.
3. **F5 over 𝔽_p, signature-based, with rewrite bases.**
   - Port from AFP `Signature_Groebner`. Its `rb_termination` (around line
     3843 of Signature_Groebner.thy) and the algorithm's termination
     (around line 7287) are what we need. It also proves there are no
     zero reductions.
   - Primes below 2²⁴, in `Nat`: Bend packs a Nat below 2⁴⁸ into a machine
     word, so products stay native.
4. **Modular lifting.**
   - Chinese remaindering and rational reconstruction.
   - Unlucky primes are finitely many: Arnold 2003 characterizes them by
     leading monomials. So adding primes until the check passes ends.
     Prove that.
5. **The decision per candidate c.**
   - Certify the block without c at x*.
   - Compute the colon ideal (I : g_c) with the degenerate solutions
     removed: a variable t with t·h₀ = 1.
   - Find a generator h with h(x*) ≠ 0 over the box. The cofactors come
     from one exact linear solve.
   - Run that side by side with the nonzero test on g_c(x*).
6. **The witness.** The relaxed drawing, with a rank tolerance, proposes
   candidates and their order. If it finds none, every constraint of the
   failing block is a candidate.

Open design items, to settle before coding them:
- **Corank above 1** (several dependencies at once): which sets to remove
  together, and in what order.
- **The exact statement of `solve_complete` v2**: Regular after removing
  the implied constraints.
- **Whether sk-13e's symbolic step reuses F5**, with the dimensions as
  extra variables. Likely yes.

## Phase 5, sk-13e: generic theorems first, and the page

- Before the exact decision, try each candidate as a generic theorem, with
  the dimensions as symbols: low degree and fast. Wu's method has proved
  hundreds of classical theorems this way (Chou, 1988).
- The page:
  - implied constraints in amber ("redundant, holds anyway");
  - conflicts in red;
  - a singular configuration as a status message naming the block (Q20).
- The "Why" detail in the list shows the certificate's constraints.

## References

Downloaded to `bend-cad/refs/`, which git ignores; re-download with the
URLs below.

| What | For | Local | URL |
|---|---|---|---|
| Maletzky, signature-based GB in Isabelle (AFP), ~10.5k lines incl. termination | Phase 4.3 port | refs/afp-Signature_Groebner | https://isa-afp.org/entries/Signature_Groebner.html |
| Immler & Maletzky, Gröbner bases theory in Isabelle (AFP), ~19k lines incl. F4, Macaulay matrices | Phase 4.1–4.2 port | refs/afp-Groebner_Bases | https://isa-afp.org/entries/Groebner_Bases.html |
| Maletzky, the signature formalization's paper (JSC 2021) | guide to the AFP entry | refs/arxiv-2012.02239 | https://arxiv.org/abs/2012.02239 |
| Maletzky & Immler, GB of modules and F4 in Isabelle | F4 alternative | refs/arxiv-1805.00304 | https://arxiv.org/abs/1805.00304 |
| Eder & Faugère, survey of signature-based algorithms (JSC 2017) | choosing the variant, notation | refs/arxiv-1404.1774 | https://arxiv.org/abs/1404.1774 |
| Pan, Hu & Wang, termination of F5-type algorithms | a second termination proof | refs/arxiv-1202.3524 | https://arxiv.org/abs/1202.3524 |
| Berthomieu, Eder & Safey El Din, msolve (ISSAC 2021) | practical modular pipeline | refs/arxiv-2104.03572 | https://arxiv.org/abs/2104.03572 |
| A probabilistic and deterministic modular algorithm for GB over ℚ | modular lifting, lucky primes | refs/arxiv-1309.4044 | https://arxiv.org/abs/1309.4044 |
| Arnold, Modular algorithms for computing Gröbner bases, JSC 35 (2003) 403–419 | unlucky primes characterized | not on arXiv | (journal) |
| Michelucci & Foufou, the witness configuration method, CAD 38(4) 2006 | Phase 4.6 | not downloaded | (journal) |
| Zou & Feng, limitations of the witness configuration method | read before Phase 4.6 | refs/arxiv-1904.00526 (PDF) | https://arxiv.org/abs/1904.00526 |

Zou & Feng criticize the witness method. In our design the witness only
proposes candidates, with every constraint of the block as the fallback,
so its limits cost speed, not correctness or completeness. Check that
reading against their examples.

## Risks

- **Scale.** About 30k lines of Isabelle to port into Bend's proof style
  is months of work, and Phase 4 dominates. That is why the checkpoint
  comes first: Phases 1–3 should cover the sketches people actually draw.
- **Check times grow.** Keep new files' import closures small. The gate
  checks each test's closure.
- **F5's native speed in Bend is unmeasured.** Prototype the 𝔽_p
  arithmetic and one reduction early in Phase 4.
