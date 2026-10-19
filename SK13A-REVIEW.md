# sk-13a: the trusted part (v4, 2026-10-19)

What "correct" means once the solver reports redundant and conflicting
constraints (DESIGN §8.11, Q24, Q28, Q29).

History, each version audited:
- v1: AUDIT-sk13a-drafts.md. The box-relative law said nothing.
- v2: AUDIT-sk13a-drafts-v2.md. The semantic laws were vacuous on
  inconsistent premises.
- v3: AUDIT-sk13a-drafts-v3.md. Over could pre-empt amber, supports were
  not irreducible, and the refusal law overclaimed.
- v4 makes four changes:
  - merges become equations (Q29);
  - Over sets look only backwards;
  - the conditions on a classification become one predicate, `Honest`,
    with a law that **the sketch determines the classification**;
  - the refusal law is restated honestly, and the stronger forms become
    open laws.

Danielle's standing rules: verified and complete; the principled way;
"all limits are proved, not just stated".

Where things are:
- The spec is in two draft files:
  - `spec/_draft13a.bend`: `spec/solve.bend` with its red-constraint
    section replaced, `Strict` refined, and `Honest` added;
  - `spec/_draft_sketch13a.bend`: `spec/sketch.bend` with merges as
    equations.
- Both type-check. Planted errors are rejected, and the Bool definitions
  were run on examples.
- The order of work is in PLAN-sk13a.md.

## The principle, both halves

Every judgment about a constraint is an (in)feasibility question about
solution sets, decided by a theorem of the alternative:
- Farkas (1902) and Motzkin (1936) for the linear fragment;
- the Positivstellensatz (Krivine 1964, Stengle 1974) for polynomials.

Each has two matching halves:
- **semantics:** "no point satisfies these", in every ordered field, which
  for these statements is the same as over the reals;
- **derivations:** "this combination is a contradiction". This is a proof
  system; bounded-degree Nullstellensatz and Positivstellensatz proof
  systems are standard in proof complexity.

The semantic half alone says nothing when premises are inconsistent,
while a bounded-degree derivation stays meaningful. So:
1. each judgment comes with its derivation in the layer's proof system
   (sk-13a: constant multipliers, "degree 0");
2. completeness conditions say every derivation of that degree was found;
3. the semantic claims are proven corollaries.

`Honest` collects 1 and 2 as a predicate of any classification.
`honest_unique` proves that two honest classifications of a sketch agree.
Every lazy solver the audits found was a case of the laws not pinning the
answer down. This law proves they now do.

**Over** claims only a count, a structurally over-determined set (a Hall
violator, the over-determined part of the Dulmage–Mendelsohn
decomposition). It doesn't claim infeasibility: incidence theorems such
as Pappus give over-determined sets that are consistent for every value.
Phase 4 decides Over flags exactly.

From sk-13b, nondegeneracy enters as explicit hypotheses in geometric
form, from a fixed vocabulary in the spec (as in Wu and Chou).

## The answer

`Out{ok, red, why, amber, drop, pins, gc, gr, plan}`.
- **red** with **why**: constraints made driven.
  - `Over{j, s, w}`: equation j lies in s, a set of more equations than
    variables (all in w), made of c's own equations and *earlier* solved
    ones.
  - `Conflict{s}`: c cannot hold with its support s, kept constraints
    before it, irreducible.
- **amber:** the redundant constraints.
- **drop:** equations left out of the system solved, each with a
  certificate. This is the solver's own reduction: a constraint may have
  dropped equations without being amber.

## The spec

`spec/_draft_sketch13a.bend` (Q29: merges as equations, D3 revised).
- Coincident(a, b) is x_a − x_b, y_a − y_b; Horizontal is y_a − y_b;
  Vertical is x_a − x_b; Concentric is the centres' x and y differences;
  EqualRadius is r_a − r_b.
- `Constraint.wf` asks nothing beyond the references.
- `Constraint.means` is unchanged: it already stated these equalities.
- This is how Fix was already handled (§4: "Fix{v, k} is an equation
  v − k = 0 in the spec; treating v as a constant is the certificate
  layer's optimization").

`spec/_draft13a.bend`: systems and pieces.
- `solved`: equations of kept constraints that are not dropped.
- `below_solved(.., j)`: those at positions before j.
- `own_below(sk, c, i)`: c's own equations before position i.
- `eqs_of(sk, cs)` and `csides(sk, cs)`: the equations and side
  conditions of a set of constraints.
- `esides`: the entities' side conditions.
- `kept_before`: the kept constraints before a position.
- `pre_eqs`, `pre_sides`: the premises before c (the equations and sides
  of the kept constraints before it, plus the entities' sides).
- `neg_pre`: those premises plus the negation of one of c's sides.
- `only`, `picked`, `side_at`, `negate`.

`spec/_draft13a.bend`: derivations.
- `Ident`: the same polynomial (equal at every rational point).
- `lin`, `slin`, `AllZero`.
- `Refutes0`, Motzkin's form: Σ lᵢeᵢ + Σ mₖsₖ = k identically, every
  mₖ ≥ 0, and k < 0, or k = 0 with a strict side mₖ > 0. No point in any
  ordered field satisfies the system.

`spec/_draft13a.bend`: bookkeeping.
- `explained`:
  - red has no repeats, and drops are distinct equations of kept
    constraints;
  - **Over:** `clean` now requires every equation of s that c doesn't
    own to belong to a constraint *before* c, not red, and not dropped
    (audit 3.1a);
  - **Conflict:** c drives an equation; s is distinct, before c, kept,
    and drives equations.
- `amber_ok`: distinct, kept, drives an equation, all its equations
  dropped.
- `conflicts`, `support`, `over_at`, `over_s`, `unmark`, `perfect`.
- `Strict` (refined): a ≥ 0 side whose variables are all pins may hold
  with equality. Ball products are exact on radius 0.

**`Honest(sk, red, why, ds, amber)`** is the conjunction of:
- `explained` and `amber_ok`;
- `Drop0`: each dropped equation is `lin(ls, below_solved(j))`;
- `Amber0`: each side of an amber c is implied, i.e. `Refutes0` of the
  premises before c plus the side's negation;
- `Conflict0`: each conflict has a `Refutes0` with its support;
- `ConflictMin`: removing any member of the support leaves no refutation;
- `Deg0`: no constant combination of solved equations, other than all
  zeros, is constant;
- `Mz0`: the kept system (solved equations, kept and entity sides) has no
  refutation;
- `Over0`:
  - none of an Over constraint's equations in its set is a constant
    combination, plus a constant, of earlier solved equations and its own
    earlier ones (audit 3.1b);
  - it has no refutation with its premises;
- `AmberComplete`: a kept constraint with an equation, all its equations
  dropped, and every side implied, is amber;
- `Matchable(solved)`: a one-to-one matching of solved equations with
  variables they mention.

Checked on examples:
- The audit's lying Over (Fix x0 = 1 twice, the first flagged) is now
  rejected; the honest form is accepted.
- Merges have equations (Horizontal 1, Coincident 2).
- A Coincident is amber only with both equations dropped.
- A Conflict can name a merge in its support.
- Earlier examples still hold.

## The laws

Abbreviations: A = `SO.solve_l(sk, g0, l)`; red, why, amber, ds =
`drops(drop)` of A; solved = `SV.solved(sk, red, ds)`.

**From the verdict** (when ok; independent of how the answer was found)
1. `solve_exists`, `solve_unique`, `solve_pins`: unchanged.
2. `solve_red` v2: `explained` and `amber_ok`.
3. `solve_regular`: the certified geometry is a regular point of the
   solved system in the free variables. The verdict gains three checks
   (audit 3.4): the plan's pins are the reported pins, the plan's variable
   order covers exactly 0..nvars − 1, and its equation order covers exactly
   the solved equations.
4. `solve_blame`: every conflict's support is consistent, because the
   certified geometry satisfies it.

**Honesty** (about the search, for every wf sketch, ok or not)
5. **`solve_honest`**: `Honest(sk, red, why, ds, amber)` at every level.

**The spec pins the answer down** (about the spec alone; no solver)
6. **`honest_unique`**: two honest classifications of a wf sketch agree
   on every constraint (red or not, conflict or not, amber or not) and on
   every equation (dropped or not):
   ```
   law honest_unique:
     for +sk: SK.Sketch
     for  w: SK.Sketch.wf(sk)
     for +r1, +y1, +d1, +a1; h1: SV.Honest(sk, r1, y1, d1, a1)
     for +r2, +y2, +d2, +a2; h2: SV.Honest(sk, r2, y2, d2, a2)
     for +c: Nat
     M.Both({SV.mem(c, r1) == SV.mem(c, r2)}, M.Both({SV.mem(c, SV.conflicts(r1, y1)) == SV.mem(c, SV.conflicts(r2, y2))}, M.Both({SV.mem(c, a1) == SV.mem(c, a2)}, {SV.mem(c, d1) == SV.mem(c, d2)})))
   ```
   The proof is by induction along the constraint order. Given the same
   earlier decisions, a constraint's fate is forced:
   - its derivable equations must be dropped (`Deg0`), and only those
     (`Drop0`);
   - a degree-0 refutation with the premises forces Conflict (`Mz0`,
     `Over0`(b)), and its absence forbids it (`Conflict0`, since a
     refutation with a support extends to the premises);
   - a Hall violator among the earlier solved equations and its own
     forces Over (`Matchable`), and its absence forbids it (`clean`);
   - amber is forced both ways (`Amber0`, `AmberComplete`).

   Only the shown witnesses and supports may differ: supports are
   irreducible but not unique (audit 3.6).

**Semantic corollaries** (proven from 5 and the spec)
7. `solve_drop`: wherever the solved equations hold, every dropped
   equation holds.
8. `solve_amber`: deleting every amber constraint changes no solution.
   This goes by induction along the order; justifications look only
   backwards.
9. `solve_conflict`: c and its support cannot all hold (by `Conflict0`),
   so c cannot be restored. Blame is earned: the support alone has no
   refutation, by `Drop0` and `Mz0` (audit 3.6's correction of "by 9 and
   10").

**Search facts**
10. `solve_total` v2:
    - as today, plus amber and drop from the sketch;
    - `explained` and `amber_ok`;
    - `perfect(solved, free(nvars, 0n, pins_of), m)` in place of the
      count.
11. `solve_complete` v2: Regular for the solved system; `dy` for kept
    constraints only; the refined `Strict`.

**What a refusal means today**
12. `solve_refused`, restated honestly (audit 3.3): if no level certifies,
    the drawing itself is not a regular solution of the solved system, in
    the free variables the solver chose. That is all `solve_complete`'s
    contrapositive gives. It says nothing about a regular solution near
    the drawing, and the page tries finitely many levels. The stronger
    forms are open laws below.

## Open laws (in ROADMAP when their phase starts; none is prose only)

- **`solve_refusal_explained`** (sk-13e): every refusal is explained, as
  one of three outcomes: a red constraint, a singular configuration naming
  the block, or a quantitative bound (no regular solution within a stated
  radius of the drawing, with a conditioning bound, Kantorovich-style).
  Audit 3.3.
- **Implicit equalities** (with the simplex, as soon as dimensions can be
  variables): an equation forced by side conditions alone (x ≥ 0 and
  −x ≥ 0 make Fix x = 0 redundant) is dropped and can be amber. These are
  the LP's implicit equalities, decided by the same simplex. Audit 3.7.
- **Amber sides at equality, nonlinear** (Phase 4): a ≥ 0 amber side that
  holds with equality at a nonlinear solution is certified exactly.
  Audit 3.7.
- Directions and lengths (sk-13b/c): derivation and completeness laws for
  their certificate shapes, with nondegeneracy hypotheses.
- Phase 4: higher-degree derivations; real-only implications (sums of
  squares); branch-selecting constraints; the exact decision of Over
  flags (Q22).
- §10.3: the solution nearest the layout (Q27).
- **The exact linear presolve** (the step after sk-13a): substituting the
  solved linear equations' pivots before Newton. This is faster, and it
  makes merged points display identical again. Its law: certifying the
  reduced system and substituting certifies the full one.

## Where the third audit's findings went

1. Over pre-empting: (a) `clean` looks backwards; (b) `Over0` covers
   every equation of c in its set. `honest_unique` proves no room is left.
2. Law 8 false for the plan: Chinneck's deletion filter on every
   conflict (PLAN S3); `ConflictMin` is now true for the plan.
3. Law 18 overclaims: restated (12), with `solve_refusal_explained` open.
4. Law 3's verdict checks: listed in 3. The explicit inverse is in PLAN's
   risks.
5. Merges in supports: merges are equations (Q29).
6. Comments: the `perfect` comment, the file header, "earlier", the
   Pappus note on Over, the "by 5 and 10" wording, and "irreducible, not
   unique" are all fixed in the draft and here.
7. Uncovered limits: open laws above.
8. Normal forms proven reduced: PLAN S1.

## Questions

1. Any changes to the spec or laws?
2. Should branch-selecting constraints (Phase 4) look different from amber
   in the page?
