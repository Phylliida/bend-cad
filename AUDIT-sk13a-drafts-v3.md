# Audit of the sk-13a drafts, v3 (SK13A-REVIEW.md v3, PLAN-sk13a.md, spec/_draft13a.bend)

Third independent audit by a separate Claude Opus 5.5 agent, 2026-10-18,
after Danielle read v3 ("looks good"). Read-only; every loophole and
counterexample below was checked with `bin/bend --check-only` against a
scratch copy of the spec (a planted false fact was rejected).

One blocker, two should-fix, the rest minor.

## Findings, most serious first

**1. Blocker: Over can still pre-empt the degree-0 layer, two ways; a
lying solver passes all 18 laws.**
- (a) Order: `clean` lets the over-determined set use *later* kept
  constraints. Fix x0 = 1 twice answered red = [0] `Over{0, [0, 1], [x0]}`,
  amber = drop = []: `explained`, `amber_ok`, `perfect` True; 11(a) holds
  (`below_solved(.., 0)` empty); 11(b) holds; 12 has no obligation (#1's
  equation is solved). The page shows #0 red, #1 plain; honest: #1 amber.
  Same with Fix x0 = 1, Fix x0 = 2 (#0 "over-determined" instead of "#1
  conflicts with #0"), breaking Q21 and the "innocent constraint cannot be
  blamed" claim.
- (b) Padding: the set may count c's own degree-0-implied equations, so
  the order fix alone is not enough. The partly implied midpoint with A's
  and B's x fixes before it (c0–c2 the y fixes, c3 x0 = 0, c4 x2 = −1, c5
  Midpoint, c6 x4 = 1), answered red = [5] `Over{5, [0..6], [six vars]}`,
  every other equation earlier and solved: all checks True; 11(a) holds
  (j, the x equation, has x4); 11(b) holds (feasible). Honest: keep the
  midpoint (y equation dropped), c6 amber.
- Fix: in `why_ok` Over, every equation of s that c does not own belongs
  to a constraint before c (provable: `lib/struct.bend` says witnesses use
  only earlier accepted constraints); extend 11(a) from j to every
  equation of c in s: none is a constant combination plus a constant of
  `below_solved(i)` with c's own earlier equations (true for the plan: the
  matching only sees tentatively solved equations). With both, the laws
  determine red (and each reason's kind), drop and amber uniquely, by
  induction along the order; only Over witnesses and conflict supports stay
  free. Worth saying in the review.

**2. Should-fix: law 8 is false for the plan as written.** S2 takes a
conflict's support from the elimination; S3's "one simplex per member"
assumes it is already irreducible. Radius(C, 3) then Radius(C, −5): S2's
residual is 8, `Conflict{[0]}`, but #1 alone with the circle's r > 0 is
refuted (ls = [−1], ms = [1], k = −5; `refok` True). HDistance(A, C, −3)
after an HDistance chain likewise (in the plan's own test class). Simplex
certificates can also name unneeded members when sides repeat (a
LineDistance's l > 0 shared with another; Distance(P, Q, r) next to the
circle's r > 0). Fix: Chinneck's deletion filter (a simplex per member,
sides and entity sides included) for every conflict, S2-found ones too;
law 7's support and refutation from the filtered set. Irreducibility
follows since feasibility only grows as rows are removed. The page then
says "Radius −5 cannot hold", not "conflicts with Radius 3".

**3. Should-fix: law 18 says much less than its prose.** `solve_complete`'s
contrapositive at g = g0 gives, for each x meeting its hypotheses, some
d > 0 with ¬Near(g0, x, d): in an ordered field, only that g0 differs from
x at some free variable (the drawing is not itself a regular solution); a
regular solution at distance ε is consistent with it. Its hypothesis ("no
level certifies") ranges over all levels; the page tries finitely many.
Fix: restate honestly; add open laws for what "refused" should mean: a
quantitative refusal (a Kantorovich-type radius and conditioning bound)
and/or sk-13e's three-way refusal ("every refusal is explained", §8.11).
Neither is in the open-laws list.

**4. Minor / should-fix: law 3 needs verdict checks S5 doesn't list.**
`final` never compares the plan's pins with `Out.pins`, and
`lib/plan.bend` says vp and ep "need not be permutations"; regularity in
`free(nvars, 0, Out.pins)` needs both. Add to `final`: `Out.pins` = the
first np entries of vp (as sets), vp covers exactly 0..nvars − 1, ep
covers exactly the solved equations. From the contraction bound to an
explicit two-sided inverse (diagonal dominance, then a block-triangular
inverse) is new proof work: put it in PLAN's Risks.

**5. Question for Danielle: merges are invisible in supports and in
"cannot hold at all".** Horizontal(A, B) then VDistance(A, B, 3): equation
x1 − x1 − 3 ≡ −3, `Conflict{[]}`, shown "cannot hold at all", yet removing
the merge fixes it. Law 15 is true only because `only` keeps the shared
variables. If the merge is last, Q21 would flag it, but merges cannot be
red. Should supports name the merges whose shared variables a refutation
uses?

**6. Minor: comments and claims.**
- `perfect`'s comment still says "not singular for want of structure"
  (`_draft13a.bend:770`); the review says corrected; it wasn't (`uses` is
  syntactic).
- The file header (lines 1–25) still describes only v1's Over.
- The Judgments comment says amber means "the other constraints imply
  it"; should be the *earlier* ones.
- "Over: infeasible for generic values" is false for incidence theorems
  with no values (Pappus); flag as Phase 4.
- Law 7's "by 9 and 10" should be "by 5 and 10" (5 moves the support's
  dropped equations into solved ones; 9 isn't needed).
- "Names exactly the constraints needed": irreducible, not unique
  (c1 = HDistance(A, B, 1), c2 = HDistance(B, C, 1), c3 = HDistance(A, C, 2)
  dropped/amber, c4 = HDistance(A, C, 3) supported by {c1, c2} or {c3}).

**7. Minor: limits not covered by any law or open law.**
- An equation implied only through sides (x7 ≥ 0 and −x7 ≥ 0 make Fix
  x7 = 0 redundant) is never amber.
- Amber sides are re-checked with balls; a ≥ 0 amber side at equality
  certifies only when its variables come out at radius 0 (pins, or exact
  linear blocks: today's solver gave radius 0 everywhere on a Fix/HDistance
  sketch). The nonlinear case is excluded by `Strict` with no open law.

**8. Minor (S1 risk).** "Ident iff the normal forms are equal" needs normal
forms proven *reduced* (distinct monomials, no zero coefficients); today
only soundness is proven. With it, non-root suffices everywhere: the
conclusions of 5–7 need only the normalizer's soundness over ℚ; the
hypotheses of 8–12 need non-root plus coefficientwise reading; the
corollaries 13–15 need non-root plus the normalizer in F.

## Verdicts per law

1 fine (`final` must check the drop certificates and amber sides). 2
fine. 3 true, needs (4). 4 fine. 5 fine; with 9 it forces the drop set
uniquely (the greedy basis in order). 6 fine; Motzkin form and `negate`
right, incl. k = 0 with a strict side. 7 fine (wording, 6). 8 right
statement, false for the plan as written (2). 9 fine, via the echelon
form. 10 fine and provable (each S3 run contains everything committed; a
feasible point of a larger system serves a smaller one; implied amber
sides hold at every feasible point). 11 (b) true; (a) true but too weak
(1). 12 fine and provable. 13–15 fine; 14's backward induction works. 16
fine. 17 true; `Strict` refinement sound (`bmul` checked). 18 overclaims
(3).

## Definitions

Derivations (`Ident`, `lin`, `slin`, `AllZero`, `negate`, `nonneg`,
`strict_pos`, `refok`, `Refutes0`): correct, robust to unreduced rationals;
sound, and complete for the linearized system (Motzkin; strict sides by
homogenization). Pieces (`eqs_of`, `csides`, `esides`, `below_solved`,
`kept_before`, `side_at`, `alldrop`, `amber_ok`, `over_at`, `support`,
`unmark`, `only`): correct incl. driven constraints, merges, empty lists,
positions past the end. Over's `why_ok`: where the holes are (1).

## Earlier findings

First audit: 1–4 closed; 5 mostly (residual case is 7); 6 closed in the
laws, comment remains (6); 7 closed; 8 closed once the plan has the
deletion filter (2); 9 deferred to sk-13b, `Strict` bullet closed.
Second audit: 1 closed for drop, amber, conflict; red partly (1); 2 partly
(1); 3, 4 closed; 5 closed given (2); 6 closed for sk-13a; 7 not closed
(comment unchanged); 8, 9 closed.
