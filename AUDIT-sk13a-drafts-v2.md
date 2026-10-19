# Audit of the sk-13a drafts, v2 (SK13A-REVIEW.md v2, spec/_draft13a.bend)

Second independent audit by a separate Claude Opus 5.5 agent, 2026-10-18,
of the drafts rebuilt on Q28's principle after the first audit
(AUDIT-sk13a-drafts.md). Read-only; Bool definitions checked on concrete
sketches in a scratch copy.

No blocker in the definitions; four should-fix gaps in the laws.

## Findings, most serious first

**1. Should-fix (near-blocker): the semantic laws are vacuous when the
kept system is infeasible beyond degree 0, which reopens lazy solver B.**
If the solved equations have no zero, `solve_drop` holds for any drop list;
if `mark(red ++ amber)` has no solution, `solve_amber` holds for any amber
list. Checked: S = (x0, x5), A = (x1, x2), B = (x3, x4); c0 Fix x0 = 1, c1
Fix x0 = 2, c2 HDistance(A, B, 1), c3 Distance(A, B, ½). Dishonest answer
red = [], drop = [1], amber = [1], pins [1, 2, 5]: `explained`, `amber_ok`
and `perfect` hold; the solved system [x0 − 1, x3 − x1 − 1, Dist] forces
(y_B − y_A)² = −¾, impossible in every ordered field, so `solve_drop` and
`solve_amber` hold vacuously; `solve_deg0` holds (independent modulo
constants); ok is always False. The page shows Fix x0 = 2 "redundant";
the honest answer is Conflict{[0]}. The same vacuity lets anything be
dropped and shown amber, and lets blame land on an innocent constraint.
Fix: state the degree-0 certificate in the law, like `solve_deg0`:
`solve_drop0` (each dropped g_j equals `lin(ls, solved)` as an identity),
`solve_conflict0` (a constant combination of c's equations and its
support's is a nonzero constant, or c has a failing variable-free side),
`amber_ok` requiring every equation of an amber constraint dropped and its
sides variable-free and true. The semantic laws become lemmas that hold on
refusals too; with `solve_deg0` the conflict certificate forces c's
coefficient nonzero, closing the triangle-inequality blame attack for
equation conflicts without a feasibility witness. Question for Danielle:
this changes the letter of the principle, not its intent.

**2. Should-fix: Over can pre-empt the linear layer.** Today's `red_of`
gives [1] for Fix x0 = 1 twice, and [2] for Fix x0 = 1, Fix x1 = 2,
HDistance(p, q, 1): both truly redundant, yet with amber = drop = [] today's
solver satisfies every v2 law there. The review's "today's solver fails
solve_deg0 on any repeat" is false: only where structure can't see the
repeat (Distance(p, q, 5) twice, free endpoints). Fix: for a red constraint
with Over{j}, equation j is not a constant combination plus a constant of
the solved equations of constraints *before* c (order-relative: against
the whole solved set the intended algorithm violates it: Fix x0..x3, then
Distance(p, q, 5) Over, later EqualLength(pq, rs) and Distance(r, s, 5)
give e5 + e6 ≡ the Over equation).

**3. Should-fix: no amber completeness.** A solver dropping honestly but
never reporting amber passes; Q24 says redundancy is reported. Law: a kept
constraint that drives an equation, has all its equations dropped, and
whose sides are variable-free and hold (or has none) is amber.

**4. Should-fix: side conditions: nothing requires step 3; the review
overstates `solve_deg0`.** Radius(c, −1) and Fix r = 0 are c's equations
against the circle's r > 0, so the Motzkin system must include c's
tentative equations and the entity sides. "Support free of constant
contradictions, by solve_deg0" holds for equations only: Fix x7 = −5 and
HDistance(p, q, d = x7) both kept, innocent Fix x9 = 3 blamed with
Conflict{[those two]} passes all laws. Under the two-step plan, (a) leaves
the first audit's finding 5 open, with its regression against v1. Fix: in
(a), a law that every variable-free side of a kept constraint holds;
Fourier–Motzkin completeness with (b). Note: Fourier–Motzkin can blow up;
exact simplex yields the same certificates.

**5. Minor: supports may contain junk and are not ordered.** `why_ok`
accepts Conflict{[driven, merge]}, unrelated kept constraints, positions
after c; Q21 not enforced. Fix: `below(s, c)`; with (1)'s certificate,
the support is exactly the owners of the nonzero rows.

**6. Minor: `Cert` and `solve_drop` disagree about h.** For sk-13a the
verdict must require h = 1, constant multipliers, and rows that are solved
equations; from sk-13b `solve_drop` needs the nondegeneracy hypothesis too.

**7. Minor: `perfect`'s comment still overclaims.** `uses` is syntactic:
OnCircle(p, c) with p merged into the centre gives −r², which can be
matched to p.x.

**8. Minor (algorithm): step 2 must also reduce against c's own earlier
equations**, else a constraint with two dependent equations (a degenerate
Symmetric) violates `solve_deg0`.

**9. Question for Danielle: four laws have no `ok`, so they cannot follow
from `seal`.** `solve_amber`, `solve_drop`, `solve_conflict`, `solve_deg0`
must be proven about the elimination itself, as `solve_total` is; ROADMAP's
"the proofs use nothing about how the answer was found" no longer holds for
them. `solve_deg0` also needs: a nonzero polynomial has a rational
non-root.

## Verdicts

- `solve_amber`: the right notion; deleting all at once is the strongest
  form (implies every subset; rules out mutual justification). Content
  whenever `mark(red ++ amber)` is feasible (always when ok); else (1).
- `solve_drop`: closes lazy A and C; vacuous on infeasible solved systems.
- `solve_conflict`: true for the intended algorithm; blame gaps in 1, 4.
- `solve_deg0`: correct as written (ℚ infinite, so constant on ℚⁿ is a
  constant polynomial; `Q.eq`/`Q.num` robust to unreduced rationals; `hl`
  fixes lengths); not vacuous (Distance(p, q, 5) twice, ls = [1, −1]);
  achievable given (8); needs no `cov`; doesn't stop Over pre-emption (2).
- `solve_red` v2: fine. `solve_total` v2: holds; implies v1's count.
- `solve_complete` v2: holds for the intended algorithm; covers what v1
  covered except where v1 discarded a partly implied constraint v2 keeps
  (by design) and the regression in (4) while only step (a) is in.
- Definitions: `picked`, `solved`, `only`, `drops`, `clean`,
  `dropped_ok`, `ceqs`, `conflicts`, `support`, `lin`/`AllZero` correct;
  `amber_ok` rejects merges, driven and red, but accepts amber whose
  equations are still solved (1); Conflict's `why_ok` fine except (5).
- Single pass: sound; a rejected c discards only its own tentative data,
  and every certificate points backwards.

## First-audit findings

1 closed for the box hole, B reopened by vacuity (1). 2 partly (equation
supports covered, side and nonlinear supports not). 3 partly (constrains
what is solved, not what is red). 4 closed. 5 not closed under (a). 6
mostly (comment remains). 7 closed. 8 closed (supports not minimal). 9
closed as a deferral (`solve_drop` needs nondegeneracy too).
