# Audit of the sk-13a drafts, v4 (SK13A-REVIEW.md v4, PLAN-sk13a.md v4, spec/_draft13a.bend, spec/_draft_sketch13a.bend)

Fourth independent audit by a separate Claude Opus 5.5 agent, 2026-10-19,
asked above all to break `honest_unique`. Checked against the files with
Bend on scratch copies outside the repo; no repository file changed.

**Verdict: `honest_unique` is true as the definitions read; `Honest` is
satisfiable by the intended algorithm with one plan correction (1). No
blocker; two should-fix, one question for Danielle, the rest minor.**

## Findings, most serious first

**1. Should-fix: PLAN S3's deletion filter must test each member's full
equations, or `ConflictMin` fails for the plan.** `Conflict0` and
`ConflictMin` use `eqs_of(c :: S)`, which includes members' dropped
equations; S3 took "equalities from the solved rows". Counterexample
(checked): c0 Vertical(A, B); c1 Coincident(A, B), x equation dropped
(equals c0's), y solved; c2 HDistance(A, B, d), d = (y_B − y_A) + 1. S2
reduces c2 to −1 with c0's row and c1's y row (support {c0, c1}); with
solved rows only, removing c0 leaves {y_A − y_B, c2} + d ≥ 0, feasible, so
c0 stays; removing c1 is feasible too: `Conflict{[0, 1]}`. But c2 with all
of c1's equations is refuted (ls = [1, −1, 1], k = −1), so `ConflictMin`
fails; the honest irreducible support is {c1}, and the plan would blame
Vertical. Fix: test each candidate support with all equations of its
members (dropped ones included), their sides, c, and the entity sides.

**2. Should-fix: S0a misses the well-formedness check.** `seal` calls
`WF.wf_dec` (`lib/solve.bend:240`), whose `cmerge` (`lib/wfdec.bend:155`)
still requires shared variables: once the page stops merging, every sketch
with a merge fails the verdict, law 10 (incl. `wf_dec(mark(red_of(sk),
sk))`) becomes false, and `wfcpf.cmerge_dec` cannot be proven from
`Constraint.wf` = Unit. Add to S0a: drop `cmerge`; update
`lib/wfdec.bend`, `lib/wfcpf.bend`, `lib/covpf.bend` (its Coincident case
now has equations), `tests/sketch_demo.bend` (`merge_ok`). Sketches still
sharing variables get identically-0 merge equations that today's solver
matches syntactically and then fails on (singular Jacobian), so "stays
green" holds only after regenerating the `.in` files unshared; after sk-13a
those merges are amber (honest). Saved IR should be unshared on load.

**3. Question for Danielle: structure is syntactic, and `honest_unique`
now locks that in.** `uses`/`inside` read the expression tree; an equation
in which a variable cancels can be matched to it (a zero Jacobian column).
Example: earlier y² − 1 solved and matched to y; c with x_m − x_m + y: not
degree-0 derivable, no degree-0 refutation, syntactically matches x_m;
Honest forces c kept, and the solve refuses on a singular block (from
normal forms, c would be Over). Before `honest_unique` a solver could do
better; now it may not. Rare once merges are unshared. Options: structure
from normal forms (the normalizer into the trusted spec), or accept and
write the limit down.

**4. Minor: stale text in trusted files and DESIGN.**
`_draft_sketch13a.bend:76` ("merges (D3): realized by shared variables, no
equations"), `:619` ("every merge is realized"); `LAWS.bend:720–721`
("Merge kinds need their variable sharing (wf)"); `_draft13a.bend:322`
("its own and solved equations" → earlier solved), `:327` (cites
"solve_conflict0"); DESIGN §4 as-built bullets (merges share variables,
`wf` requires it; "merge conflicts are errors" no longer holds:
Horizontal + Vertical is a degenerate segment); DESIGN §8.11 still says
Over is "infeasible for generic values" and points to "SK13A-REVIEW.md
(v2)" / "Laws (drafts, v2)".

**5. Minor: `honest_unique` as written in the review doesn't parse.** The
binders lack types and the equalities `: Bool`; with them it type-checks
(scratch `tests/t2.bend`). Put it in that form, since it is signed off.

**6. Minor: the proof sketch is incomplete.** "Its absence forbids [Over]
(clean)" also needs `Over0`(a) (else a derivable equation pads the set:
audit 3.1b). "A refutation forces Conflict (Mz0)" needs `Drop0` to rewrite
dropped premises as solved, and a lemma re-indexing side multipliers
(`pre_sides ++ csides(c)` vs `Mz0`'s list place entity sides differently).
No decision procedure is needed (each mismatched case is a direct
contradiction), so S6's "derivability decided by the echelon basis" lemma
can go.

**7. Minor: amber sides could be certified by their own certificates.** S5
re-checks amber sides with balls, but the degree-0 certificate that makes
a side amber proves e ≥ 0 wherever the premises hold. With `final` checking
amber sides that way, law 11 could exempt them from `Strict` now, and the
open law "amber sides at equality, nonlinear" shrinks to nothing for
sk-13a. Separately, a non-amber ≥ 0 side at equality on free, unpinned
variables is excluded by `Strict` with no open law.

**8. Minor, forward-looking: leftovers of merges having no equations.**
`ceqs > 0` in Conflict's `why_ok`, `has_eqs` for supports and amber,
`lt(0, ceqs)` in `AmberComplete`: harmless now (every kind has an
equation), but a future kind with sides and no equations whose side
conflicted could be neither kept (`Mz0`) nor red: `Honest` unsatisfiable.
Use "driving".

**9. Minor: the open-laws list misses three limits.** Q26 (pins from the
drawing: law 11's "regular in the solver's free variables"); sk-19 (a red
constraint's deviation); the general ≥ 0-at-equality case from 7.

## Verdict on `honest_unique`: true

Induction over constraints, hypothesis: both agree on red for every
constraint before c and on drops for every equation position before c's
first; then `below_solved`, `kept_before`, `pre_eqs`, `pre_sides` are equal
lists. For c: drops (both kept): equation by equation, `Drop0` in one gives
a combination of the (equal) earlier solved, which `Deg0` of the other
forbids solving. Kept vs Conflict: `Conflict0`'s refutation extends to the
premises (support ⊆ kept before c), and `Drop0` turns it into a refutation
of the solved system, which `Mz0` forbids. Over vs Conflict: the same
extension contradicts `Over0`(b). Kept vs Over: by `clean` the earlier
members of s are solved in the other too; by `Over0`(a) c's members of s
are not derivable even with a constant, so `Drop0` cannot have dropped
them; s (over-determined) lies inside the other's solved system, and
pigeonhole contradicts `Matchable`. Amber: given red and drops at c,
`Amber0`/`AmberComplete` force it either way. Later constraints cannot
unforce an earlier decision. Tried: ties within one constraint, an
identically-0 equation (Coincident(A, A), shared merges), a derivable
equation next to an over-determined one, red constraints whose equations
would have been dropped, sides implied only by later or red constraints,
driven constraints, merges in supports: each forced. The delicate steps
are list bookkeeping (rewriting dropped premises via `Drop0` inside
`Ident`; embedding side lists into `Mz0`'s order and `eqs_of(c :: S)`
into `pre_eqs ++ eqs_of([c])`; pigeonhole through filtered `solved`; the
lemma that `owners` is nondecreasing).

## Satisfiability: yes, with (1)

`Deg0` (each committed equation not derivable even with a constant), `Mz0`
(the last kept constraint's simplex includes every kept and entity side;
with nothing kept, entity sides v > 0 hold at all ones), `Over0`(a) (the
Kuhn witness uses only earlier solved and c's tentatively solved; a
constant-shifted derivation would have been a refutation), `AmberComplete`
(the simplex is complete for the linearized system), `Matchable` (by
induction on accepted units; pins play no part), `ConflictMin` (once the
filter tests full equations).

## Laws

1, 2, 4, 7, 8, 9, 12 fine. 3 fine (the explicit inverse is real work). 5
provable given (1). 6 true; statement needs (5). 10 true once `wfdec` is
updated (2). 11 fine; (7) would strengthen it. No loopholes: with 5 and 6
the only freedom left is in Over witnesses, which irreducible support is
shown, the pins (Q26) and the box.

## Definitions

All the new ones say what their comments and the review say; edge cases
(past the end, driven, empty lists, `lin` truncation under ∀/∃, `side_at`
past the end) fine. The IR change is semantically clean: `means`
unchanged; `means_sound`/`means_complete` stay true with a weaker
hypothesis; `sketch_*` unaffected; sketches still sharing variables mean
the same, their merges come out amber.

## Third-audit findings

1 closed. 2 closed in the spec, the plan needs (1). 3 closed. 4 closed. 5
closed (stale comments in 4). 6 mostly (DESIGN §8.11 and
`_draft13a.bend:327` remain). 7 partly (7, 9). 8 closed.
