# sk-13a: the trusted part, for review (2026-10-18)

What "correct" means once the solver drops implied equations and reports
conflicts (DESIGN §8.11, Q24). Nothing here is wired in yet: the new spec
is `spec/_draft13a.bend` (a copy of `spec/solve.bend` with one section
replaced; it type-checks), and the laws below are drafts for
ROADMAP.bend. Once you are happy with them, the spec replaces
`spec/solve.bend` and the solver and proofs get built on it.

## The answer

`Out` gains one field, `drop`: the dropped equations, each with its
position in `Sketch.eqs` and a certificate. Everything else stays.

- **red** (dropped whole, made driven): the constraints that do not hold,
  each with a `Why`.
- **drop**: equations left out of the system solved because the solved
  ones imply them. Their constraints are not made driven, so they still
  hold at the certified geometry.
- **amber**, for the page only: a constraint all of whose equations are
  dropped.

## The spec (`spec/_draft13a.bend`, the section "Dropped equations")

- **`solved(sk, red, ds)`**: the system the solver solves. These are the
  sketch's equations whose constraint is not red and that are not dropped,
  in order. With nothing dropped it is the system of `mark(red, sk)`.
- **`picked(es, js)`**: the equations at the positions `js`, for example
  the dropped ones.
- **`Cert{h, qs, k}`**: a certificate h·g = Σ qᵢ·g_{iᵢ} + k, an identity of
  polynomials over the sketch's equations.
  - It is data only. The verdict checks the certificate of each dropped
    equation (k = 0, and h nonzero over the box). The laws say what
    passing buys.
  - In sk-13a, h = 1 and the qᵢ are constants. Later phases reuse the
    type: h = |b|² for directions, Gröbner cofactors in Phase 4.
- **`Drop{j, c}`**: dropped equation j and its certificate. `drops(ds)`
  gives their positions.
- **`Why`**: now three reasons.
  - `Over{j, s, w}`, today's: equation j lies in an over-determined set s.
  - `Conflict{j, c}`: equation j cannot hold together with the solved
    equations; c is a certificate with k ≠ 0.
  - `Side{i}`: its i-th side condition has no variables and is false, for
    example a distance of −5. It is checked exactly, over ℚ.
- **`clean`** (no red flag is spare) now requires the other equations of
  an Over set to be *solved*, not just owned by a kept constraint. Without
  that, a repeated Fix whose copy was dropped would still count as two
  equations.
- **`explained(sk, red, ds, why)`**: `distinct(red)` (a review item), and
  each red constraint's reason holds.
  - `Over`: as today, with the new `clean`.
  - `Conflict`: j is that constraint's equation. What a conflict means is
    the law `solve_conflict`, not a Bool check, so no normalizer is
    trusted.
  - `Side`: the failing side is checked here.
- **`conflicts(red, why)`**: the red constraints whose reason is
  `Conflict` or `Side`. `unmark(c, red)` is red without c.
- **`perfect(es, vs, m)`**: m matches the equations es one to one with the
  variables vs, each equation with a variable it mentions, and every
  variable of vs is used exactly once. This replaces `solve_total`'s count
  (review item 2).

Ran on small examples (all as expected):
- `fails`: −5 ≥ 0 fails, 5 ≥ 0 and 0 ≥ 0 hold, 0 > 0 fails, and x > 0 is
  never "failing" because it has a variable.
- `solved`: it counts right with red and dropped equations.
- `explained`: Side explains the −5 distance and not a Fix. A constraint
  listed red twice is rejected. An Over set using a dropped equation is
  rejected.
- `perfect`: true for the right matching; false for a swapped one, a
  repeated variable, or a variable left over.

## The laws (drafts for ROADMAP.bend)

**Unchanged in statement:** `solve_exists`, `solve_unique`, `solve_pins`.
Amber constraints are never marked, so "holds anyway" is `solve_exists`.

**`solve_red` v2**: the same, with the dropped equations passed to
`explained`.

```
law solve_red:
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  {SV.explained(sk, SO.Out.red(SO.solve_l(sk, g0, l)), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l))), SO.Out.why(SO.solve_l(sk, g0, l))) == True{} : Bool}
```

**`solve_drop`** (new): every dropped equation is redundant. In the box,
the equations solved imply it. This is what makes amber's "redundant"
true; that it *holds* is `solve_exists`.

```
law solve_drop:
  for ~F: O.OField
  for ~H: N.Emb<KI.dnum(), F>
  for +sk: SK.Sketch
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}
  for +x: M.Vec(~F)
  for  hb: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x)
  for  hz: SK.Zeros(~F, x, SV.solved(sk, SO.Out.red(SO.solve_l(sk, g0, l)), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l)))))
  SK.Zeros(~F, x, SV.picked(SK.Sketch.eqs(sk), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l)))))
```

In sk-13a the certificates hold everywhere (h = 1), but the box is in the
statement so the law keeps its shape when directions bring h = |b|².

**`solve_conflict`** (new): a conflicting constraint cannot be restored.
Bring it back, with every other red constraint still dropped, and no
geometry in any ordered field means the sketch. There is no `ok`
hypothesis: it holds whenever the solver answers, so a refused sketch's
conflicts are proven too.

```
law solve_conflict:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +g0: List<&2, S.D>
  for +l: Nat
  for +c: Nat
  for  hc: {SV.mem(c, SV.conflicts(SO.Out.red(SO.solve_l(sk, g0, l)), SO.Out.why(SO.solve_l(sk, g0, l)))) == True{} : Bool}
  for +x: M.Vec(~F)
  for  m: SK.Sketch.means(~F, x, SV.mark(SV.unmark(c, SO.Out.red(SO.solve_l(sk, g0, l))), sk))
  Empty
```

**`solve_total` v2**: as today, plus `drop` = `drop_of(sk)`. The count is
replaced by a one-to-one matching of the solved system with the free
variables:

```
  ... M.Both({SO.Out.drop(SO.solve_l(sk, g0, l)) == SO.drop_of(sk) : List<&2, SV.Drop>}, ...
  ... M.Both({SV.explained(sk, SO.red_of(sk), SV.drops(SO.drop_of(sk)), SO.why_of(sk)) == True{} : Bool}, ...
  ... (&m: List<&2, Nat> -> {SV.perfect(SV.solved(sk, SO.red_of(sk), SV.drops(SO.drop_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m) == True{} : Bool})
```

**`solve_complete` v2**: two hypotheses change.
- `hr`: Regular for the *solved* system, `SV.solved(sk, SO.red_of(sk),
  SV.drops(SO.drop_of(sk)))`. The full kept system has implied rows, so it
  is never regular.
- `dy`: the constants of the kept constraints only,
  `SV.dyadic(SV.mark(SO.red_of(sk), sk))` (review item 7). This is a
  weaker hypothesis, so the law is stronger.

`hz` still asks x to satisfy every kept equation, dropped ones included.
Since they are implied, that's no extra condition.

## How the solver finds them (not trusted; for orientation)

One pass over the constraints, in order, extending today's red stage
(`kuhnc`). For each constraint:
1. If a side condition with no variables fails, it is red with `Side`.
2. Its linear equations are reduced exactly, over ℚ, against the solved
   linear equations kept so far.
   - A residual with a variable: the equation is solved.
   - Residual 0: it is dropped, with the certificate (the multipliers of
     the reduction).
   - A nonzero constant: the constraint is red with `Conflict`.
3. Its remaining equations are matched as a unit, as today. If that fails,
   it is red with `Over`.

Each constraint is judged against what was kept *before* it, and nothing
kept is revisited. So a certificate never leans on a constraint that is
flagged later. That was a real hazard: with a linear stage followed by a
separate structural stage, a conflict could be proven against a Fix the
structural stage then flagged. Processing in order also gives Q21: the
last constraint of a dependency is the one dropped or flagged.

The certificates are checked with a new normalizer for polynomials with
rational coefficients, proven in every ordered field (the existing ones
are ℤ in every field, `fring_eq`, and ℚ over ℚ, `qring_eq`). Every later
phase needs it too.

## Review items left as they are, with reasons

- **A drawing shorter than nvars** (review 7) reads missing entries as 0,
  the same in `held`, `PinnedAt` and `Near`. That's a consistent
  convention (the drawing padded with zeros), not a gap, and checking the
  length would add a hypothesis on every nearby drawing in
  `solve_complete`. I'd leave it.
- **The plan's pins against the reported pins** (review 6) is checked by
  no law either way. It's worth a `solve_regular` law later: the box's
  solution is regular, the converse of `solve_complete`. Not in sk-13a.

## An extension I'd suggest, not yet in the plan

A constraint whose variables are all fixed by linear equations (two fixed
points and a Distance between them, which is common in a GUI) can be
decided by substituting: its equation becomes a constant, which is 0
(dropped) or not (`Conflict`). The certificate has polynomial
multipliers, which the same `Cert` and normalizer cover. It's cheap, and
it turns today's Over for that case into amber or conflict, as Q22 asks.
It could go in sk-13a or wait.

## Questions

1. The spec and laws above: changes?
2. `solve_conflict` without `ok`, so conflicts are proven even on a
   refused sketch: right?
3. The substitution extension: in sk-13a, or later?
