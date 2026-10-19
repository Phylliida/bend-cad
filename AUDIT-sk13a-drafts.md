# Audit of the sk-13a drafts (SK13A-REVIEW.md, spec/_draft13a.bend)

Independent audit by a separate Claude Opus 5.5 agent, 2026-10-18, after
Danielle read the drafts ("seems good") and asked for one. Read-only; it
checked definitions with `bin/bend --check-only` on `{==}` facts in a
scratch copy (a planted false fact was rejected). Before it reported, the
same day, Danielle and Claude had found that the box-relative
`solve_drop` says nothing beyond `solve_exists` (the box holds exactly one
solution of the solved system), and had framed the fix in real algebraic
geometry: redundancy is a property of the whole real solution set
(conversation of 2026-10-18; DESIGN §8.11 records the outcome). Finding 1
below is the same hole, found independently, with sharper lazy solvers.

## Findings, most serious first

**1. Blocker: `solve_drop` is checked only with `ok` and only inside the
box, so nothing constrains what is dropped.** With pins at radius 0 and
the box isolating one solution of `solved`, "implied in the box" means
"holds at that point". `drop_of` is otherwise free.
- Lazy solver A ("check the drawing"): red = [], drop = every position,
  pins = every variable, box = g0 at radius 0, ok only when g0 satisfies
  the sketch exactly. Every law holds: `explained(sk, [], all, [])` and
  `perfect([], free(n, 0, all), [])` are True (checked), `Regular` of the
  empty system is trivial, and `Near` with every variable pinned forces
  g = g0 = x. The old count ruled this out; `perfect` with free drops does
  not, so review item 2's fix is undone.
- Lazy solver B (a conflict reported amber): Fix x0 = 1, Fix x0 = 2, Fix
  x1 = 5 with drop_of = [1], red = []: `perfect` holds, ok is always
  False, so no law applies; the page shows "Fix x0 = 2: redundant, holds
  anyway" and refuses.
- Lazy solver C: a segment with Fix p, Fix q.y, HDistance 100, the
  HDistance dropped and q.x pinned: certifies only an exact drawing and
  shows the HDistance amber.
- Fix: a drop law independent of the answer and of the box: for every wf
  sketch, every ordered field and every x, Zeros(x, solved(sk, red_of,
  drops(drop_of))) implies Zeros(x, picked(eqs, drops(drop_of))). For
  directions add eval(h, x) ≠ 0 and state separately that h ≠ 0 over the
  box; never use the box as the hypothesis.

**2. Should-fix (near-blocker): `solve_conflict` is vacuous when the rest
is unsatisfiable.** HDistance(p, q, 1), HDistance(p, q, 2), Fix x7 = 5:
the solver keeps both HDistances (`perfect` matches them to x_q, x_p) and
flags Fix x7 = 5 as Conflict; `why_ok` checks only the owner, so
`explained` accepts (checked), and `solve_conflict` holds because the
restored sketch is unsatisfiable anyway. A fine constraint shows red on a
refused sketch. Fix: a self-contained claim: the Conflict names its
support S (solved, checked in `explained`), S has a common zero, and S
with c's equations has none; or rely on finding 3 for the linear family.
On the question asked: restoring one constraint with every other red one
still removed is the right notion; the problem is only the vacuity.

**3. Should-fix: no law requires the linear layer to do anything.**
Today's solver with drop_of = [] and reasons tagged Over satisfies every
draft. Suggested: no nontrivial rational combination of the solved linear
equations is constant (DESIGN's `solve_red_complete`, linear family). It
also makes `solve_conflict` meaningful for linear conflicts.

**4. Should-fix: the algorithm, read literally, breaks `solve_total` v2.**
If equations step 2 marks solved skip step 3's matching, `perfect` fails
(A: Fix x0 = 1; N nonlinear in x1 only; L: x0 + x1 − 3 → residual x1 − 2,
solved: three equations over two variables). Every equation not dropped
must go through the matching, and step 2's basis additions and drops are
kept only if the constraint survives step 3. With both, certificates stay
valid at the end; no other breaking interaction found.

**5. Should-fix: side conditions fixed by linear equations are never
decided.** Radius(c, −1) or Fix r = 0 (the circle's r > 0 fails, no
constraint side does); HDistance with d = x7 and Fix x7 = −5. Refused with
nothing red; if the equation was dropped, the culprit shows amber. Also a
coverage regression from v1 (a constraint v1 flagged Over becomes amber,
and if its side with variables fails at x, v1 certified x and v2 cannot).
Fix: evaluate side conditions (entity sides included) exactly when the
linear layer fixes all their variables (the side half of the substitution
extension, in sk-13a); show amber only when ok.

**6. Minor / should-fix: equations identically constant but not linear.**
OnLine(p, a) with p an endpoint of a, Parallel(a, a), EqualLength(a, a),
Distance(p, p', d) with p, p' merged. `uses` is syntactic, so `perfect`
still matches them (checked for EqualLength(a, a)); the Jacobian row is
identically 0 and the solver refuses with nothing red; `perfect`'s
comment ("not singular for want of structure") overclaims. Fix: normalize
every equation first: normal form 0 → dropped, nonzero constant →
Conflict, each with qs = []; or soften the comment.

**7. Minor: dropped positions unchecked; amber undefined in the spec.**
`explained` accepts repeated drops, drops past the end, and drops of a red
constraint's equations (checked); `picked` reads past the end as 0 = 0.
"All equations dropped" is vacuous for merge constraints (no equations).
Fix: `dropped_ok` in `explained` (distinct, in range, owner not red), and
a spec `amber(sk, red, ds)` requiring at least one equation.

**8. Minor: `Conflict{j}` is checked only for its owner.** Either equation
of a Midpoint is accepted (checked), so the page can name the wrong one.
The Why comment ("with the solved equations") is narrower than what the
certificate may use (c's own other equations too).

**9. Minor, later: `solve_conflict` lacks the nondegeneracy carve-out.**
Under Q15 a collapsed segment satisfies any direction cycle, so as drafted
it will be false for sk-13b/c conflicts. Separately, the third bullet of
AUDIT-sk09-laws.md item 7 (`Strict` for ≥ 0 sides with only pinned
variables) is missing from the "left as they are" list.

## Verdicts

- Definitions: `solved`, `picked`, `drops` correct (with nothing dropped,
  `solved` = `Sketch.eqs(mark(red, sk))`, checked with a driven constraint
  and red positions). `Cert`, `Drop` fine as data. `clean` v2 correct.
  `Why`/`why_ok`: Over fine; Side fine (`fails` right on −5, 0 > 0 and
  expressions with variables); Conflict owner-only (8). `explained`:
  `distinct(red)` good, lacks drop checks (7). `conflicts`, `unmark`
  correct. `perfect` correct as a matching and rules out the previous
  review's lazy stage, but syntactic, and not enough with free drops (1, 6).
- Laws: `solve_red` v2 fine. `solve_drop` true for the intended solver but
  far too weak (1). `solve_conflict` the right notion, dropping `ok` right,
  but vacuous when the rest is unsatisfiable (2). `solve_total` v2 sound,
  needs (1)'s law to mean anything. `solve_complete` v2 stays true for the
  intended algorithm given (4); on sketches v1 covered no drop or conflict
  fires except (5); the weaker `dy` is safe; without (1)'s fix lazy solver
  A satisfies it.
