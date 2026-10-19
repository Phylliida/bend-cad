# Plan: sk-13a, the degree-0 layer (2026-10-18)

The statements are in SK13A-REVIEW.md (v3): the answer, the spec
(`spec/_draft13a.bend`), and laws 1–18. This file is the order of work,
what each step proves, and the risks. It replaces PLAN-sk13.md's Phase 1
bullets; the rest of PLAN-sk13.md stands.

## What sk-13a delivers

**The solver** finds, in one pass over the constraints in order:
- every equation that is a constant combination of earlier solved ones
  (dropped);
- every constraint with a degree-0 refutation against what was kept before
  it (red, Conflict, with an irreducible support);
- every redundant constraint (amber).

Only then does it use structure (red, Over). All of it is proven:
- derivation laws for each judgment;
- completeness laws for the layer;
- the semantic meaning as corollaries;
- the existing laws restated over the solved system.

**For your sketches:**
- Repeats, including repeated OnCircles, become amber and certify at the
  first precision. Today oncircle-pairs with its repeats is refused after
  88 s.
- Conflicting dimensions, Radius −1, a distance of −5, and an angle
  against its opposite become red with their supports.
- vertical-twice stays refused until sk-13b (directions): its dependency
  needs multipliers of degree above 0.

## Ground rules (standing)

- Prove the solver as it runs: no check-and-fallback added to ease a
  proof.
- Verified and complete (D7).
- Drafts in `tools/drafts/*.draft`, expanded by `tools/expand.py`.
- The gate is `./check.sh`; the native regression is `tools/regress.sh`.
- Commit freely. Implement code myself, not with agents. Agents audit.
- No exact counts in docs.

## Steps

### S0. Statements settled and wired
- Danielle reviews SK13A-REVIEW.md v3, then a third independent audit runs
  on it.
- `spec/_draft13a.bend` replaces `spec/solve.bend`.
- Laws 1–18 go into ROADMAP.bend, written out in full.
- `tools/stmtcheck.py` type-checks the open ones.
- The `Why`, `Out` and `explained` call sites are updated
  (`lib/redpf.bend`, `lib/solve.bend`, `proto/*.bend`, `gui/solve_cli.bend`).
  Until the new stage lands, the existing proofs keep the gate green with
  amber = drop = [].
- Exit: the gate passes, with the new laws open.

### S1. Polynomials as vectors, and the bridge between the two notions
- **Rows.** Integer polynomials in normal form (`lib/zring.bend`'s ZTerm
  lists) with a combination: a list of (equation, integer coefficient).
- **Invariant.** In every ordered field, a row's value is Σ c · den · g,
  reusing `lib/fring.bend`'s padd/pscale/pneg lemmas and
  `lib/qnorm.bend`'s clr_ok.
- **The non-root lemma.** A nonzero integer polynomial has an integer
  point where it is nonzero: by induction on the variables, since a
  univariate polynomial of degree d has at most d roots.
- **What follows from it:**
  - `Ident(e1, e2)` holds iff the normal forms are equal;
  - then the two agree in every ordered field;
  - a polynomial identity can be read coefficient by coefficient, which is
    what lets a linearized point refute a refutation.
- Proves the tools for laws 5–15.

### S2. Degree-0 elimination over all equations
- **What it does.** Fraction-free Gaussian elimination over monomial
  vectors, constraint by constraint, against the solved rows kept so far
  *and c's own earlier equations* (audit 2.8).
- **Outcomes:**
  - residual 0: dropped, with its combination;
  - nonzero constant: refutation (equation part);
  - otherwise: tentatively solved.
- **Pivots** are leading monomials other than 1, kept distinct
  (echelon form).
- **Proves:** 5 (`solve_drop0`) from the invariant; the equation part of
  7; 9 (`solve_deg0`) from the echelon form and S1.

### S3. Exact simplex with Bland's rule, for side conditions
- **The system.** Monomials are the unknowns. Equalities come from the
  solved rows plus c's tentative ones; inequalities from kept sides,
  entity sides and c's sides. Strictness uses the standard extra variable
  (maximise t with sₖ ≥ t on strict sides).
- **Output:** a linearized feasible point, or a Motzkin certificate.
- **Proves:**
  - termination (Bland: no basis repeats);
  - certificate soundness, giving the side part of 7, and 6 (amber sides:
    the premises plus the side's negation);
  - "a feasible linearized point means no refutation exists" (from S1),
    giving 10 (`solve_mz0`), 11(b), and 8 (`solve_conflict_min`: one
    simplex per support member, each giving a feasible point once that
    member is removed).
- Fastest at our sizes, as Danielle prefers. Fourier–Motzkin was the
  simpler alternative but can blow up.

### S4. The single pass
- `kuhnc` extended: each constraint is normalized, then S2, then S3, then
  the structural matching of its tentatively solved equations as a unit
  (the matching step `grp` takes a list of equations, not a contiguous
  run). Conflict comes before Over.
- On success, c's rows, sides and drops are committed. Amber is c with an
  equation, all equations dropped, and all sides implied.
- `Out` gains amber and drop; `red_of`, `why_of`, `drop_of` and
  `amber_of` come from the sketch alone.
- **Proves:** 16 (`solve_total` v2, with `perfect` from lib/maxpf's
  matching facts), 11(a) (an Over equation had a residual with a
  variable), 12 (`solve_amber_complete`).

### S5. The verdict and soundness
- **`final` gains:**
  - the drop certificates (`qzero`; h = 1; rows are earlier solved
    equations);
  - the plan checked over the solved system;
  - side conditions of mark(red, sk), amber constraints' included.
- **Proves:**
  - 1 (`solve_exists`: Zeros of the solved system, plus the certificates,
    gives Zeros of every kept equation);
  - `solve_unique`, `solve_pins`, 2 (`solve_red` v2);
  - 3 (`solve_regular`, from the plan check's Jacobian bound, reusing
    sk-06 and C-series lemmas);
  - 4 (`solve_blame`, from `solve_exists`: the support is kept).

### S6. Semantic corollaries
- 13 (`solve_drop`) from 5;
- 14 (`solve_amber`) from 5 and 6, by induction along the constraint
  order;
- 15 (`solve_conflict`) from 7, via Refutes0's soundness in every ordered
  field;
- 18 (`solve_refused`) from 17.

### S7. `solve_complete` v2
- The C1–C6 proof (`lib/completepf.bend`) with the kept system replaced
  by the solved one.
- The drop certificates pass, because S2 proves them right for every
  sketch.
- `Strict` is refined: a ≥ 0 side with only pinned variables is checked
  at its exact value.
- `dy` only for kept constraints.
- **Proves:** 17.

### S8. The page and the CLI
- **The CLI** prints amber, drops, conflicts with supports, and Over.
- **The page:**
  - amber "redundant", plus "holds anyway" when ok;
  - red Conflict "conflicts with #a, #b" when ok, "cannot all hold with
    #a, #b" on a refusal;
  - red Over "over-determined".
- **The regression:** proto/sketches/expected updated, and new test
  sketches:
  - an HDistance chain, consistent and not;
  - the partly implied midpoint pair;
  - Distance 5 and −5;
  - Radius −1;
  - an angle against its opposite;
  - EqualLength(a, a).

### S9. Audit and sign-off
- An independent audit of the proofs' statements against the review
  document.
- Gate and regression green.
- Danielle signs off on the laws.

**Exit for sk-13a:**
- laws 1–18 proven;
- the regression shows the expected changes (repeats amber and fast;
  vertical-twice still refused);
- the new test sketches behave.

## Risks

- **The non-root lemma** (S1): classical, but a real proof (polynomial
  degree and root counting in Bend). It is the bridge every later phase
  uses too.
- **Bland's rule termination** (S3): a classical combinatorial argument,
  moderately hard to formalize. If it turns out far harder than expected,
  I'll stop and ask before considering alternatives.
- **Re-proving `solve_complete`** (S7): C1–C6 took a long time. The
  change should be a substitution (solved for kept), but the proof is
  large.
- **Check times:** new files with small import closures; the gate checks
  each test's closure.
- **Scope:** sk-13a is now a large milestone (S1–S7). Commit at each step
  with the gate green, and check in with Danielle after S0 and after S3.
