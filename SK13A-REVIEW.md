# sk-13a: the trusted part, for review (v2, 2026-10-18)

What "correct" means once the solver reports redundant and conflicting
constraints (DESIGN §8.11, Q24). v1 of this document was audited
(AUDIT-sk13a-drafts.md); v2 rebuilds it on one principle, chosen with
Danielle the same day. Nothing is wired in yet: the spec is
`spec/_draft13a.bend` (`spec/solve.bend` with one section replaced; it
type-checks and its definitions were run on examples), and the laws below
are drafts for ROADMAP.bend.

## The principle: every judgment is an (in)feasibility, with a certificate

What the solver says about a constraint is a statement about **solution
sets**, never about its box. The box is how a solution is certified; v1's
`solve_drop` was stated inside the box, where the solved system has exactly
one solution, so it said nothing beyond "holds at that point". That was
the hole.

- The laws say "in every ordered field". For statements of the form "for
  all x, these imply that", this is the same as over the reals (every
  ordered field sits inside a real closed field, and Tarski showed those
  all agree), so the laws speak about real geometry.
- Each judgment is an infeasibility question:
  - **Redundant (amber)**: "the others, with c failing" has no solution.
  - **Conflict (red)**: "c with its support" has no solution.
- The classical *theorems of the alternative* say such a question is
  decided by a certificate, and they are complete (a certificate exists
  exactly when the system is infeasible):
  - for linear equations and inequalities, **Farkas** (1902) and
    **Motzkin** (1936): a nonnegative combination of the rows is a
    contradiction;
  - for polynomials, the **Positivstellensatz** (Krivine 1964, Stengle
    1974), the same with sums of squares.
- One certificate format, one checker (`lib/qnorm.bend`), every phase. The
  layers are truncations of this hierarchy: sk-13a uses constant
  multipliers ("degree 0"), directions and lengths use lemma-shaped
  multipliers, Phase 4 raises the degree (Gröbner bases).
- **Over** stays as the structural reason: the over-determined part of
  the Dulmage–Mendelsohn decomposition, infeasible for *generic* values.
  It claims exactly that until Phase 4 decides those exactly.
- **Nondegeneracy** (from sk-13b, where a chain of parallels says nothing
  about a segment of length 0): as in geometric theorem proving (Wu,
  Chou), explicit conditions in geometric form, from a fixed vocabulary in
  the spec, never a polynomial chosen by the solver (one could vanish on
  the other solutions and empty the law again).

## The answer

`Out` gains two fields:
- **amber**: constraint positions, the redundant ones (the user-facing
  claim; `solve_amber`).
- **drop**: equations the solver leaves out of the system it solves, each
  with a certificate (the solver's own reduction; `solve_drop`). An
  equation can be dropped without its constraint being amber: a midpoint
  whose x equation follows from others, or an angle whose equation follows
  but whose side condition still picks the orientation.

**red** keeps its meaning (dropped whole, made driven), with a `Why`.

## The spec (`spec/_draft13a.bend`, "Judgments as (in)feasibility")

- `solved(sk, red, ds)`: the sketch's equations whose constraint is not
  red and that are not dropped, in order. With nothing dropped it is the
  system of `mark(red, sk)`.
- `picked(es, js)`: the equations at the positions js.
- `only(cs, sk)`: the sketch with only the constraints at positions cs
  driving.
- `Cert{h, qs}`, `Drop{j, c}`, `drops`: a dropped equation's certificate,
  h·g_j = Σ qᵢ·g_{iᵢ}. Data only: the verdict checks it with `qzero` and
  that h ≠ 0 over the box (h = 1 in sk-13a), and `solve_drop` says what
  dropping means.
- `Why`: `Over{j, s, w}` (as today) or `Conflict{s}`: it cannot hold with
  the constraints at positions s, all kept; s is empty when it cannot hold
  at all (a distance of −5).
- `explained(sk, red, ds, why)`: red has no repeats; the dropped equations
  are distinct equations of kept constraints (`dropped_ok`); each red
  constraint's reason is well formed.
  - `Over`: as today, with `clean` now excluding dropped equations.
  - `Conflict{s}`: the constraint drives an equation, and s is distinct,
    in range, without it, and without red constraints.
- `amber_ok(sk, red, amber)`: no repeats, none red, each drives an
  equation. That excludes merges, which are shared variables with no
  equations, and driven constraints.
- `conflicts(red, why)` and `support(c, red, why)`: which red constraints
  conflict, and with what.
- `perfect(es, vs, m)`: a one-to-one matching of equations with
  variables, each equation with one it mentions.
- `lin(ls, es)`, `AllZero(ls)`: a combination with constant coefficients,
  and "all coefficients 0".

Examples run (all as expected):
- `only` keeps the named constraints and keeps driven ones driven.
- A Conflict naming itself, a red constraint, or a position past the end
  is rejected.
- A dropped equation of a red constraint, a drop listed twice, and a drop
  past the end are rejected.
- A merge or a driven constraint can't be amber.
- `support` returns the right set.

## The laws (drafts for ROADMAP.bend)

Unchanged: `solve_exists`, `solve_unique`, `solve_pins` (amber
constraints are never marked, so the certified geometry satisfies them).

**`solve_amber`**: deleting every amber constraint changes no solution.

```
law solve_amber:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +g0: List<&2, S.D>
  for +l: Nat
  for +x: M.Vec(~F)
  for  m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SO.Out.red(SO.solve_l(sk, g0, l)), SO.Out.amber(SO.solve_l(sk, g0, l))), sk))
  SK.Sketch.means(~F, x, SV.mark(SO.Out.red(SO.solve_l(sk, g0, l)), sk))
```

**`solve_drop`**: every dropped equation is implied, everywhere, by the
equations solved.

```
law solve_drop:
  for ~F: O.OField
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +g0: List<&2, S.D>
  for +l: Nat
  for +x: M.Vec(~F)
  for  hz: SK.Zeros(~F, x, SV.solved(sk, SO.Out.red(SO.solve_l(sk, g0, l)), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l)))))
  SK.Zeros(~F, x, SV.picked(SK.Sketch.eqs(sk), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l)))))
```

**`solve_conflict`**: a conflicting constraint cannot hold together with
its support. It follows that it cannot be restored into the kept sketch
either, since more constraints mean fewer solutions.

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
  for  m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(c, SO.Out.red(SO.solve_l(sk, g0, l)), SO.Out.why(SO.solve_l(sk, g0, l)))}, sk))
  Empty
```

**`solve_deg0`** (the first layer is complete): no combination of the
solved equations with constant coefficients, not all 0, is constant.
Repeats, chains of dimensions, and constraints that are identically 0 or
constant are all such combinations, so none of them survives into the
system solved.

```
law solve_deg0:
  for +sk: SK.Sketch
  for  w: SK.Sketch.wf(sk)
  for +g0: List<&2, S.D>
  for +l: Nat
  for +ls: List<&2, S.Q>
  for  hl: {SV.qlen(ls) == SV.neqs(SV.solved(sk, SO.Out.red(SO.solve_l(sk, g0, l)), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l))))) : Nat}
  for +k: S.Q
  for  hk: @x: List<&2, S.Q> -> S.Q.eq(E.qeval(x, SV.lin(ls, SV.solved(sk, SO.Out.red(SO.solve_l(sk, g0, l)), SV.drops(SO.Out.drop(SO.solve_l(sk, g0, l)))))), k)
  SV.AllZero(ls)
```

**`solve_red` v2**: when ok, `explained(sk, red, drops(drop), why)` and
`amber_ok(sk, red, amber)`.

**`solve_total` v2**:
- as today, plus amber = `amber_of(sk)` and drop = `drop_of(sk)`;
- `explained` and `amber_ok` for them;
- in place of the count, a one-to-one matching of the solved system with
  the free variables:
  `&m -> SV.perfect(SV.solved(sk, red_of, drops(drop_of)), SV.free(nvars, 0n, pins_of), m)`.

**`solve_complete` v2**:
- `hr`: Regular for the solved system.
- `dy`: only the kept constraints' constants need be dyadic.

**How they close the audit's lazy solvers:**
- Dropping everything and pinning everything fails `solve_drop`: the
  empty system implies nothing.
- A conflict shown amber fails `solve_amber`: deleting it changes the
  solutions.
- An innocent constraint blamed for someone else's conflict (HDistance 1
  and 2 kept, Fix x7 = 5 blamed) fails `solve_deg0`: the two HDistances
  combine to a constant, so they cannot both be solved.
- Today's solver with nothing dropped fails `solve_deg0` on any repeat.

**What `solve_conflict` does not claim:** that the support is itself
consistent in general. That would need a feasibility certificate for a
nonlinear set, which has no rational point in general. What holds:
- the support is free of constant-multiplier contradictions, by
  `solve_deg0`;
- when the answer is ok, the kept sketch is certified consistent, so c
  conflicts with a consistent sketch.

## How the solver finds them (not trusted; for orientation)

One pass over the constraints, in order, extending today's red stage
(`kuhnc`). Each constraint is judged against what was kept before it, and
nothing kept is revisited, so every certificate stays valid at the end.
For each constraint c:
1. Its equations and side conditions are written as integer coefficient
   vectors over their monomials (clear denominators and normalize, as in
   `lib/qnorm.bend`).
2. **Equations, degree 0.** Each equation is reduced against the solved
   equations kept so far, by exact fraction-free elimination that tracks
   each row's combination.
   - Residual 0: dropped, with that combination as its certificate (h = 1).
   - Residual a nonzero constant: c is red, `Conflict`, with the
     combination's owners as its support.
   - Otherwise: tentatively solved.
   This is the first step of F4 (the Macaulay matrix with constant
   multipliers). It catches every repeat, including nonlinear ones (a
   repeated OnCircle), at the cost of one Gaussian elimination.
3. **Side conditions, degree 0** (Fourier–Motzkin over the same vectors,
   with the solved equations).
   - If c's sides make the kept sides and equations infeasible, c is red,
     `Conflict`, with the Motzkin certificate's owners as its support.
     This covers Radius −1 against the circle's r > 0, an angle against
     its opposite, and a distance of −5.
   - Each side of c that the kept ones imply is recorded.
4. **Structure.** Every tentatively solved equation of c goes through the
   matching as a unit (the matching step takes a list of equations now,
   not a contiguous run). On failure c is red, `Over`. Only when c
   survives are its basis additions and drops kept.
5. **Amber.** c is amber when it drives an equation, all its equations
   were dropped, and all its side conditions are implied.

The page shows amber as "redundant". It adds "holds anyway" only when the
answer is ok, since only then is there a solution for "holds" to refer to.

## The audit's findings, and where each went

1. `solve_drop` empty: restated box-free (`solve_drop`). Amber is now its
   own law (`solve_amber`).
2. `solve_conflict` vacuous: the support is named, and `solve_deg0` stops
   blame landing on an innocent constraint. The claim's limits are stated
   above.
3. No law for the linear layer: `solve_deg0`, which also covers nonlinear
   repeats.
4. The algorithm must match every equation it does not drop: step 4.
5. Side conditions fixed by linear equations: step 3, as Fourier–Motzkin
   (the principled general case, not evaluation of fixed variables).
6. Identically constant equations: the degree-0 elimination drops them
   (residual 0) or flags them (`Conflict{[]}`); `solve_deg0` requires it.
7. Unchecked drops: `dropped_ok`. Amber is defined by `amber_ok`
   (it drives an equation).
8. Conflict naming the wrong equation: Conflict now names its constraint
   and support, not an equation. The page can show "conflicts with #3,
   #7".
9. Nondegeneracy for later conflicts: the principle above (a fixed
   geometric vocabulary, from sk-13b).

## Left as they are, or for later, with reasons

- A drawing shorter than nvars reads as zeros consistently. It's a
  convention, not a gap.
- The plan's pins against the reported pins: for a later `solve_regular`
  law.
- `Strict` asking > 0 for a ≥ 0 side whose variables are all pins: a
  `solve_complete` refinement, harmless (it only narrows what that law
  covers). Later.
- A completeness law for side conditions (no Motzkin certificate left
  among the kept sides): comes with Fourier–Motzkin.
- Blame on a refused sketch: `solve_conflict` says c and its support
  cannot all hold, but a dishonest solver could name a support that is
  infeasible beyond degree 0 (three distances breaking the triangle
  inequality) and blame an innocent c. When the answer is ok the
  certified geometry shows the support consistent, so this is only about
  refusals. The principled fix is a feasibility witness for the support
  (a certified box for it alone, from the existing block machinery).
  Later, with the nonlinear layers.
- Branch-selecting constraints (hold here, pick this solution among
  several) and real-only implications (sums of squares, for example
  Distance 0 forcing coincidence): Phase 4, where the real solutions can
  be computed exactly.

## Questions

1. The spec and laws above: changes?
2. sk-13a in two steps: (a) equations at degree 0, with only variable-free
   sides; (b) Fourier–Motzkin for the rest of the sides. Or both at once?
3. Should branch-selecting constraints (later) look different from amber
   in the page?
