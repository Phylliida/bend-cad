# Review of the six sk-09 law drafts (ROADMAP.bend)

Independent review by a separate Claude Opus 5.5 agent, 2026-10-18, after
Danielle read the drafts and judged them good. It was asked for gaps
between each statement and its comment, vacuous hypotheses, loopholes (a
useless solver that satisfies all six), weak trusted definitions, and what
sk-13 should keep. Read-only: no repository file was changed. Findings 1
and 3 were re-checked by hand the same day (noted below). Decisions on
them are recorded in DESIGN §16 and HANDOFF, not here.

Every law is true as stated. Together they leave gaps.

## Findings, most serious first

**1. Blocker: the soundness laws cover level 0 only.**
- `solve_exists`, `solve_unique`, `solve_red`, `solve_pins` are stated for
  `SO.solve` = `solve_l(sk, g0, 0n)`. `solve_complete` promises
  certification by `solve_l(sk, g, l)` for an existential l, which its
  proof picks through `CR.arch`, so in general l > 0.
- No law constrains an answer at l > 0, so the comment's "(so, by
  solve_unique, x is the geometry it certifies)" does not follow.
- Loophole: honest at level 0, and at every l ≥ 1 ok = True with
  centers g, radius 0 at the pins and 1 elsewhere. All six laws hold
  (red/why/pins kept equal to red_of/why_of/pins_of).
- Conversely the GUI calls only `SO.solve`, and no completeness law applies
  to level 0.
- Fix: state the four soundness laws for every l over `solve_l`. The
  existing `exists_of`/`unique_of`/`red_of`/`pins_of` (lib/solvepf.bend)
  take any answer with `final == True`, which `seal` gives at every level.
- Re-checked by hand: true (ROADMAP.bend; lib/solvepf.bend:77–101).

**2. Should-fix: `solve_total` states squareness by count only.**
- Its last conjunct is `neqs(kept) + len(pins) = nvars`. Nothing says the
  kept equations can be matched to the free variables.
- A lazy structure stage passes: Fix x0 = 1 twice and Fix x1 = 2, with
  red = [] and pins = [2]. The kept Jacobian has two equal rows, so
  `solve_complete`'s `hr` cannot hold and it says nothing. (The real
  solver answers red 1, pins 2 3, ok True.)
- So no law makes red flag enough. Fix: add an injective matching of the
  kept equations into `free(nvars, 0n, pins_of)` (each equation to a
  variable it mentions); lib/maxpf.bend proves the facts already. sk-13's
  `solve_red_complete` needs this base.

**3. Question for Danielle: `Regular` in the structurally chosen free
variables fails on basic sketches.**
- A segment with a Distance and no other constraint: pins p1.x, p1.y,
  p2.x, free p2.y, and ∂/∂p2.y = 2(p2.y − p1.y) = 0 when it is horizontal.
- Native runs: (0,0)–(100,0) with Distance 100, drawn exactly: ok False.
  A 3-4-5 triangle with a horizontal base: ok False; tilted: ok True.
- Any free variable axis-aligned with its pinned partner does this, which
  grid snapping makes common. HANDOFF records it; the GUI's untrusted
  variable order avoids most cases; the law's comment gives only the
  rarer vertical-line example.
- Re-checked by hand: (0,0)–(100,0), Distance 100: ok False, pins 0 1 2;
  (0,0)–(6,8), Distance 10: ok True.
- Decide whether pins are chosen numerically (from the drawing). That
  changes `solve_total`'s "pins depend on the sketch alone".

**4. Should-fix, for sk-13: implied must be judged on meanings, side
conditions included.**
- `Distance(p, q, 5)` and `Distance(p, q, −5)` have the same equation; the
  second's side −5 ≥ 0 fails, so it is a conflict, not amber.
- `Angle` (c, s) against (−c, −s): equations agree up to sign, the dot > 0
  sides need opposite directions.
- `solve_implied` should conclude `Constraint.means`; the decision must
  check sides too.
- Keep in `explained`/`Why`: the owner check, `clean` (no spare flag) for
  every kind, naming by position.
- Add `distinct(red)`: a repeated position is harmless now, ambiguous once
  each position carries a status.
- Over says nothing about whether the constraint holds: Fix x = 1 twice is
  Over today where users expect amber. Either decide Over flags exactly
  too (Q22) or state that Over makes no claim.
- Deciding at a solution x* makes red depend on the drawing:
  `solve_total`'s sketch-only equalities and `solve_complete`'s `red_of`
  hypotheses must then be restated, and red must stay constant on the
  Near neighbourhood.
- Conflict "with interior lengths nonzero" means no nondegenerate
  solution; under Q15 a collapsed segment satisfies the cycle. Law and UI
  should say so.

**5. Question for Danielle: no law bounds the box's radius.**
- A box of radius 2¹⁰⁰ around the unique solution of an all-linear sketch
  passes every law; `solve_unique` only rules out boxes holding a second
  solution. §9's guaranteed digits need small radii.
- Option: `solve_complete` for every ε > 0, some level gives radius ≤ ε at
  the free variables.
- Related: a try-harder loop stopping at the first certifying level may
  get a neighbouring root; `solve_complete` does not exclude a lower
  level certifying something else.

**6. Minor: radius-0 coordinates that are not reported pins.** `final`
never ties the plan's pinned variables to `Out.pins`, so `solve_unique`'s
"given the radius-0 coordinates" also covers holds that are not reported.
Today both come from the same structure (lib/numer.bend, `skel.pins`).
A sketch certified with every radius 0 makes `solve_unique` say only that
the box is a point. Fix: a `solve_regular` law (the converse of
`solve_complete`), or check in `final` that the plan's pins equal
`Out.pins`.

**7. Minor.**
- `held` and `PinnedAt` read a missing drawing entry as 0: require
  `len(g0) = nvars` in the verdict.
- `dyadic(sk)` checks red constraints' constants too, which the solver
  never uses: `dyadic(mark(red_of(sk), sk))`.
- `Strict` requires > 0 for a ≥ 0 side whose variables are all pins,
  though a radius-0 ball certifies equality there.

## Verdict per law

- solve_exists: matches its comment and §10.2; level 0 only (1).
- solve_unique: matches; uniqueness relative to all radius-0 coordinates,
  as admitted; level 0 only.
- solve_red: sound; no-spare holds in the strong sense given ok. Keep the
  structure for v2.
- solve_pins: matches; minor short-drawing issue.
- solve_total: true but too weak, counts only (2).
- solve_complete: true as stated, but its coverage depends on untrusted
  structural choices (2, 3) and on levels no soundness law constrains (1).

The trusted definitions match their names (`inbox`, `means`, `Near`,
`Regular`, `free`, and `explained`, sound because syntactic occurrence is
conservative).
