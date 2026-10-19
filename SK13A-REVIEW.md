# sk-13a: the trusted part (v3, 2026-10-18)

What "correct" means once the solver reports redundant and conflicting
constraints (DESIGN §8.11, Q24, Q28). History:
- v1 was audited in AUDIT-sk13a-drafts.md: the box-relative law said
  nothing.
- v2 rebuilt everything on Q28's principle and was audited in
  AUDIT-sk13a-drafts-v2.md: its semantic laws were vacuous when the rest
  of the sketch is infeasible.
- v3 states derivations, with completeness laws, and turns the semantic
  claims into proven corollaries. Every limit is a law: proven, or open in
  ROADMAP with its proof planned (Danielle, 2026-10-18: "all limits are
  proved, not just stated").

The spec is `spec/_draft13a.bend`: `spec/solve.bend` with its red-constraint
section replaced, and `Strict` refined. It type-checks, and its Bool
definitions were run on examples. The order of work is PLAN-sk13a.md.

## The principle, both halves

Every judgment about a constraint is an (in)feasibility question about
solution sets, decided by a theorem of the alternative:
- Farkas (1902) and Motzkin (1936) for the linear fragment;
- the Positivstellensatz (Krivine 1964, Stengle 1974) for polynomials.

Each theorem has two halves that match exactly:
- **Semantics:** "no point satisfies these". In every ordered field;
  for these statements that is the same as over the reals (Tarski).
- **Derivations:** "this combination of them is a contradiction". This is
  a *proof system*. Nullstellensatz and Positivstellensatz proof systems
  of bounded degree are standard objects of proof complexity (Beame et
  al. 1994, Grigoriev and Vorobjov 2001).

The semantic half alone fails when premises are inconsistent: from a
contradiction everything follows, so an implication claim says nothing.
A bounded-degree derivation does not fail that way: "this equation is 1
times that one" stays true however broken the rest is. So the laws come
in three kinds:
1. **Derivation laws:** each judgment comes with its derivation in the
   layer's proof system. In sk-13a that is constant multipliers, "degree
   0".
2. **Completeness laws:** every derivation of that degree that exists was
   found. This is the layer's boundary, proven.
3. **Semantic corollaries:** what the derivations mean for solution sets.
   They are proven from 1 and the spec, and have content whenever the rest
   is consistent, in particular whenever the answer is ok.

Over stays as the structural reason: the over-determined part of the
Dulmage–Mendelsohn decomposition, infeasible for *generic* values. A
completeness law makes sure it is used only when degree 0 finds nothing.

From sk-13b, nondegeneracy conditions appear as explicit hypotheses in
geometric form ("b is not a point"), from a fixed vocabulary in the spec,
as in geometric theorem proving (Wu, Chou).

## The answer

`Out{ok, red, why, amber, drop, pins, gc, gr, plan}`: two new fields.
- **red**, with **why**: constraints made driven. `Over{j, s, w}` (as
  today), or `Conflict{s}`: c cannot hold with its *support* s, kept
  constraints before it.
- **amber**: the redundant constraints, the user-facing claim.
- **drop**: equations of kept constraints left out of the system solved,
  each with a certificate, the solver's own reduction. A constraint can
  have dropped equations without being amber. Two examples: a midpoint
  whose x equation follows from others, and an angle whose equation
  follows but whose side condition still picks the orientation.

## The spec (`spec/_draft13a.bend`)

Systems:
- `solved(sk, red, ds)`: equations of kept constraints that are not
  dropped, in order.
- `below_solved(sk, red, ds, j)`: those at positions before j.
- `eqs_of(sk, cs)`: the equations owned by the constraints at positions
  cs.
- `csides(sk, cs)`: the side conditions of the driving constraints among
  cs.
- `esides(sk)`: the entities' side conditions (r > 0, bulge > 0).
- `kept_before(sk, red, c)`: kept, driving constraints before position c.
- `only(cs, sk)`: the sketch with only cs driving.
- `picked`, `side_at`, `negate` (the side condition that holds exactly
  where s fails).

Derivations:
- `Ident(e1, e2)`: the same polynomial (equal at every rational point; ℚ
  is infinite).
- `lin(ls, es)`: the combination l₁e₁ + … + lₙeₙ.
- `slin(ms, ss)`: the same over side conditions' expressions.
- `AllZero(ls)`: every coefficient is 0.
- `Refutes0(es, ss, ls, ms, k)`, Motzkin's form: the lengths match, every
  mᵢ ≥ 0, and Σ lᵢeᵢ + Σ mₖsₖ = k identically, with k < 0, or k = 0 and
  some strict side having mₖ > 0. No point in any ordered field satisfies
  es and ss.

Bookkeeping:
- `Cert{h, qs}`, `Drop{j, c}`, `drops`: a dropped equation's certificate,
  checked by the verdict.
- `explained(sk, red, ds, why)`: red has no repeats; drops are distinct
  equations of kept constraints (`dropped_ok`); each reason is well
  formed.
  - Over: as today, with `clean` excluding dropped equations.
  - Conflict{s}: c drives an equation; s is distinct, *before* c (Q21),
    kept, and each member drives an equation.
- `amber_ok(sk, red, ds, amber)`: no repeats, none red, each drives an
  equation (no merges, no driven), and all its equations are dropped.
- `conflicts`, `support`, `over_at`, `unmark`, `perfect` (as before).
- `Strict(F, x, ss, pins)`, refined: a ≥ 0 side whose variables are all
  pins may hold with equality. Its ball has radius 0, and ball products
  are exact on exact inputs (radius |c₁|r₂ + |c₂|r₁ + r₁r₂), so the box
  check sees its exact value.

Examples run (all as expected):
- `eqs_of` on a driven constraint is empty.
- `kept_before` skips red and driven constraints.
- `below_solved` counts drops correctly.
- `refok` accepts the two Fixes x0 = 1 and x0 = 2 refuted with (−1, 1)
  and k = −1, and Radius −1 against r > 0 with (−1; 1) and k = −1.
- `refok` rejects k = +1, a length mismatch, a negative side multiplier,
  and k = 0 without a strict side.
- Conflict rejects a support after c and a driven support.
- `amber_ok` requires the equation dropped.

## The laws

Abbreviations, expanded in ROADMAP:
- A = `SO.solve_l(sk, g0, l)`;
- red, why, amber = `SO.Out.red(A)`, `SO.Out.why(A)`, `SO.Out.amber(A)`;
- ds = `SV.drops(SO.Out.drop(A))`;
- solved = `SV.solved(sk, red, ds)`;
- eqs = `SK.Sketch.eqs(sk)`;
- s(c) = `SV.support(c, red, why)`;
- P(c) = the premises before c: equations `eqs_of(sk, kept_before(sk,
  red, c))` and sides `csides(sk, kept_before(sk, red, c)) ++ esides(sk)`.

### From the verdict (when ok; independent of how the answer was found)

1. `solve_exists`, `solve_unique`, `solve_pins`: unchanged. Amber
   constraints are never marked, so the certified geometry satisfies them.
2. `solve_red` v2: `explained(sk, red, ds, why)` and `amber_ok(sk, red,
   ds, amber)`.
3. **`solve_regular`** (new): the certified geometry is a regular point
   of the solved system in the free variables. It is the converse of
   `solve_complete`, and gives `solve_unique` its full meaning when the
   box is a point:
   ```
   (&x: M.Vec(~F) -> (BX.inbox(..., gc, gr, x) & SK.Sketch.means(~F, x, SV.mark(red, sk)) & DV.Regular(~F, x, solved, SV.free(SO.nvars(sk), 0n, SO.Out.pins(A)))))
   ```
4. **`solve_blame`** (new): every conflict's support is consistent; some
   geometry means `only(s(c), sk)`. With 7 below, c is the culprit with
   respect to a consistent support. It follows from `solve_exists`: the
   support is kept, so the certified geometry satisfies it.

### Derivations (about the search, for every wf sketch, ok or not)

5. **`solve_drop0`**: each dropped equation is a constant combination of
   solved equations before it:
   ```
   for +j, hj: {SV.mem(j, ds) == True{}}
   (&ls: List<&2, S.Q> -> SV.Ident(SV.eqat(eqs, j), SV.lin(ls, SV.below_solved(sk, red, ds, j))))
   ```
6. **`solve_amber0`**: each side condition of an amber constraint c is
   implied by the premises before it. The premises plus its negation
   have a degree-0 refutation:
   ```
   for +c, hc: {SV.mem(c, amber) == True{}}
   for +i, hi: {SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{}}
   (&ls -> &ms -> &k -> SV.Refutes0(eqs_of(sk, kept_before(sk, red, c)), csides(sk, kept_before(sk, red, c)) ++ esides(sk) ++ [SV.negate(SV.side_at(SV.csides(sk, [c]), i))], ls, ms, k))
   ```
   Its equations are all dropped (`amber_ok`), so 5 covers them.
7. **`solve_conflict0`**: c and its support have a degree-0 refutation:
   ```
   for +c, hc: {SV.mem(c, SV.conflicts(red, why)) == True{}}
   (&ls -> &ms -> &k -> SV.Refutes0(SV.eqs_of(sk, Con{c, s(c)}), SV.csides(sk, Con{c, s(c)}) ++ SV.esides(sk), ls, ms, k))
   ```
   By 9 and 10, the support alone has none, so every refutation uses c,
   and an innocent constraint cannot be blamed.
8. **`solve_conflict_min`**: the support is irreducible at degree 0.
   Remove any one member and no degree-0 refutation is left:
   ```
   for +c, hc: (as in 7); for +m, hm: {SV.mem(m, s(c)) == True{}}
   for +ls, +ms, +k, h: SV.Refutes0(SV.eqs_of(sk, Con{c, SV.unmark(m, s(c))}), SV.csides(sk, Con{c, SV.unmark(m, s(c))}) ++ SV.esides(sk), ls, ms, k)
   Empty
   ```
   This is an irreducible infeasible subsystem (Chinneck's IIS) with
   respect to degree 0. The page's "conflicts with #3, #7" names exactly
   the constraints needed.

### Completeness of the layer (for every wf sketch)

9. **`solve_deg0`**: no constant combination of the solved equations,
   other than all zeros, is constant:
   ```
   for +ls, hl: {SV.qlen(ls) == SV.neqs(solved)}; for +k: S.Q; for hk: SV.Ident(SV.lin(ls, solved), E.QCst{k})
   SV.AllZero(ls)
   ```
10. **`solve_mz0`**: the kept system has no degree-0 refutation. That
    covers the solved equations together with every kept side condition
    and the entities':
    ```
    for +ls, +ms, +k, h: SV.Refutes0(solved, SV.csides(sk, SV.kept_before(sk, red, SO.ncons(sk))) ++ SV.esides(sk), ls, ms, k)
    Empty
    ```
    Together, 9 and 10 are what makes 7 assign blame: using only kept
    constraints, no refutation exists.
11. **`solve_over0`**: Over is used only when degree 0 finds nothing. For
    c red with Over and equation j:
    - (a) equation j is not a constant combination of earlier solved
      equations plus a constant: `Ident(eqat(eqs, j), lin(ls,
      below_solved(sk, red, ds, j)) + k)` → Empty;
    - (b) c with the premises before it has no degree-0 refutation:
      `Refutes0(P(c) equations ++ eqs_of(sk, [c]), P(c) sides ++
      csides(sk, [c]), …)` → Empty.
12. **`solve_amber_complete`**: redundancy is reported. A kept constraint
    c that drives an equation, has all its equations dropped, and whose
    every side condition is implied by P(c) (a refutation as in 6, given
    for each i) is amber:
    ```
    for +c, hk: {SV.mem(c, red) == False{}}, he: {SV.lt(0n, SV.ceqs(sk, c)) == True{}}, hd: {SV.alldrop(sk, ds, [c]) == True{}}
    for hs: @i: Nat -> {SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{}} -> (&ls -> &ms -> &k -> SV.Refutes0(... as in 6 ...))
    {SV.mem(c, amber) == True{}}
    ```

### Semantic corollaries (proven from 5–12 and the spec)

13. **`solve_drop`**: in every ordered field, wherever the solved
    equations hold, every dropped equation holds.
14. **`solve_amber`**: in every ordered field, deleting every amber
    constraint changes no solution: `means(mark(red ++ amber, sk))` →
    `means(mark(red, sk))`. It follows from 5 and 6 by induction along
    the constraint order. Each justification looks only backwards, so two
    amber constraints cannot justify each other.
15. **`solve_conflict`**: in every ordered field, c and its support
    cannot all hold. Hence c cannot be restored into the kept sketch.

### Search facts (as today, extended)

16. `solve_total` v2:
    - as today, plus amber = `amber_of(sk)` and drop = `drop_of(sk)`;
    - `explained` and `amber_ok` for them;
    - in place of the count, a one-to-one matching
      `perfect(solved, free(nvars, 0n, pins_of), m)`.
17. `solve_complete` v2:
    - `hr`: Regular for the solved system;
    - `dy`: only the kept constraints' constants need be dyadic;
    - `hs`: `Strict(F, x, sides(mark(red_of, sk)), pins_of(sk))`, the
      refinement.

### What a refusal means (already proven, stated as a corollary)

18. **`solve_refused`**: if no level certifies, there is no regular
    solution near the drawing. This is `solve_complete`'s
    contrapositive, stated so the page's "refused" has a law behind it.

## Where the audits' findings went

**First audit:**
1. `solve_drop` empty: closed by 5 and 13.
2. `solve_conflict` vacuous: closed by 7 with 9 and 10.
3. No law for the linear layer: closed by 9 and 10.
4. The algorithm must match every equation it doesn't drop:
   PLAN-sk13a.md step 4.
5. Side conditions fixed by linear equations: closed by 10, with the
   simplex in sk-13a.
6. Identically constant equations: closed by 9 (a 0 or constant equation
   is a combination).
7. Unchecked drops: closed by `dropped_ok`, and `amber_ok` now requires
   the equations dropped.
8. Conflict naming the wrong equation: supports name constraints, and 8
   makes them minimal.
9. Nondegeneracy: from sk-13b, as hypotheses in the laws.

**Second audit:**
1. Vacuity: closed by 5–8. The semantic laws are corollaries.
2. Over pre-empting: closed by 11.
3. Amber completeness: closed by 12.
4. Side conditions in step (a): closed. There is no separate step; the
   simplex is in sk-13a, and its system includes c's own equations and
   the entities' sides.
5. Junk and order in supports: closed by `below(s, c)`, `has_eqs` and 8.
6. Cert vs h: in sk-13a the verdict requires h = 1, constant multipliers,
   and rows that are earlier solved equations; nondegeneracy enters 5 and
   13 from sk-13b.
7. `perfect` overclaims: comment corrected (the matching is syntactic;
   regularity is `solve_complete`'s and `solve_regular`'s).
8. Reduce against c's own earlier equations: PLAN-sk13a.md step 2.
9. Laws without `ok`: intended. Laws 1–4 come from the verdict, 5–18 from
   the search proofs, as `solve_total` does. ROADMAP's sentence is
   rewritten to say which is which. `Ident` → equality in every field
   needs "a nonzero polynomial has a rational non-root": in the plan.

## Open laws for later phases (in ROADMAP when their phase starts)

- Directions and lengths (sk-13b/c): derivation and completeness laws for
  their certificate shapes, with nondegeneracy hypotheses from a fixed
  spec vocabulary.
- Phase 4: higher-degree derivations (Gröbner) and their completeness;
  real-only implications (sums of squares, e.g. Distance 0 forcing
  coincidence); branch-selecting constraints decided exactly from the
  real solutions; the exact decision of Over flags (Q22).
- §10.3: the solution nearest the layout (Q27).
- The plan's pins against the reported pins: covered by 3.

## Questions

1. Any changes to the spec or laws?
2. Should branch-selecting constraints (Phase 4) look different from amber
   in the page?
