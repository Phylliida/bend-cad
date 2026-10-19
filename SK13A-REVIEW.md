# sk-13a: the trusted part (v5, 2026-10-19)

What "correct" means once the solver reports redundant and conflicting
constraints (DESIGN §8.11, Q24, Q28–Q30).

History: four versions, each audited (AUDIT-sk13a-drafts.md, -v2, -v3,
-v4). The fourth audit found no counterexample to `honest_unique`. v5
keeps v4's logic and simplifies its form (Danielle, 2026-10-19):
- **one class per constraint** in place of parallel lists;
- **honesty stated locally**, each constraint given the classes before it;
- **structure read from what an equation depends on** (Q30), not from how
  it is written.

v5 also folds in the fourth audit's fixes. Danielle's standing rules:
verified and complete; the principled way; all limits proved, not stated.

The spec was drafted in two files, now in place (S0a, S0b):
- `spec/solve.bend` (was `spec/_draft13a.bend`): the classification
  section replaced and `Strict` refined;
- `spec/sketch.bend` (was `spec/_draft_sketch13a.bend`): merges as
  equations.

Both type-check; planted errors are rejected; the Bool helpers were run
on examples. The order of work is in PLAN-sk13a.md.

## The principle

Every judgment about a constraint is an (in)feasibility question about
solution sets, decided by a theorem of the alternative: Farkas and
Motzkin for the linear fragment, the Positivstellensatz for polynomials.

Such a theorem has two halves:
- **semantics**, which says nothing when premises are inconsistent;
- **derivations** (a proof system), which stay meaningful.

So each judgment carries its derivation in the layer's proof system:
constant multipliers, "degree 0", in sk-13a. The layer's completeness is
part of what "honest" means, and the semantic claims are proven
corollaries.

Over claims only a count, a structurally over-determined set, not
infeasibility; Pappus-type incidences are over-determined and consistent.
Phase 4 decides Over exactly. From sk-13b, nondegeneracy enters as
explicit geometric hypotheses from a fixed vocabulary in the spec.

## The answer

`Out{ok, cls, pins, gc, gr, plan}`: one class per constraint, by position.
- **`Kept{drops}`:** kept; these of its equations are left out of the
  system solved, each with a certificate.
- **`Amber{drops, refs}`:** redundant. All its equations are dropped,
  and its side conditions are implied by the premises before it, each by
  a refutation of the premises and the side's negation (`Ref{ls, ms, k}`,
  which the verdict checks).
- **`Over{j, s, w}`:** red. Its equation j lies in s, which has more
  equations than variables (in w). s is made of its own non-dropped
  equations and earlier solved ones.
- **`Conflict{s}`:** red. It cannot hold together with its support s:
  kept, driving constraints before it, irreducibly.

A constraint can't be red twice, red and amber, or red with drops: those
states can't be written. `reds`, `ambers`, `conflicts` and `dropped` are
derived, so the laws that use `mark(red, sk)` read as before.

## The spec

**`spec/sketch.bend`** (Q29, D3 revised):
- Coincident is x_a − x_b, y_a − y_b; Horizontal is y_a − y_b; Vertical
  is x_a − x_b; Concentric is the centres' differences; EqualRadius is
  r_a − r_b.
- `Constraint.wf` asks nothing beyond the references, and `means` is
  unchanged.
- The fourth audit checked the change is semantically clean:
  `means_sound` and `means_complete` stay true with a weaker hypothesis,
  `sketch_*` are unaffected, and a sketch that still shares variables
  means the same thing (its merges come out amber).

**`spec/solve.bend`: systems.**
- `solved`;
- `presolved(sk, red, ds, c)`: the solved equations of constraints before
  c;
- `own_rest(sk, c, d, i)`: c's equations before position i not in d;
- `eqs_of`, `csides`, `esides`, `kept_before`;
- `pre_eqs` and `pre_sides`: the premises before c, i.e. the kept
  constraints before it plus the entity sides;
- `neg_pre`, `only`, `picked`, `side_at`, `negate`.

**`spec/solve.bend`: derivations.**
- `Ident`: the same polynomial, equal at every rational point.
- `lin`, `slin`, `AllZero`.
- `Refutes0`, Motzkin's form: Σ lᵢeᵢ + Σ mₖsₖ = k identically, every
  mₖ ≥ 0, and k < 0, or k = 0 with a strict side's mₖ > 0.

**`spec/solve.bend`: dependence (Q30).** Structure is about what an
equation depends on, not how it is written:
- `Depends(e, v)`: the derivative of e in v (`spec/deriv.bend`) is not
  identically 0. In x − x + y, x doesn't count.
- `DependsWithin(e, w)`: e depends only on variables in w.
- `Overdet(es, s, w)`: distinct equations of es, depending only on w,
  with w shorter than s.
- `Matchable(es)`: a one-to-one matching of es with variables each
  depends on.
- `Perfect(es, vs, m)`: such a matching onto exactly vs, for
  `solve_total`.

This needs no new trust: it uses only the trusted derivative and `Ident`.
The solver builds its adjacency from normal forms, and the non-root lemma
proves the two notions agree.

**`spec/solve.bend`: classes.** `Ref`, `Class`, `class_at`, `kind`, `reds`,
`ambers`, `conflicts`, `dropped`, `support`, `driving`, `all_driving`,
`alldrop.go`, `unmark`.

**`Honest(sk, cls)`.** There is one class per constraint, and each
constraint c's class is the honest one given the classes before it. A
driven constraint is Kept with nothing dropped. For a driving c:
- **Conflict{s} (`ConflictOk`):**
  - s is distinct, before c, driving, and kept;
  - c and s have a degree-0 refutation;
  - without any one member of s they have none, so s is irreducible.
- **Kept{drops} (`KeptOk`):**
  - c with its premises has no degree-0 refutation (`NoRefute`);
  - the dropped equations are *exactly* the derivable ones (`DropsOk`):
    each equation of c is dropped iff it is a constant combination of
    the earlier solved equations and c's own earlier non-dropped ones;
  - what's left, with the earlier solved equations, is `Matchable`;
  - if every equation was dropped, some side condition is *not* implied
    (otherwise it would be amber).
- **Amber{drops} (`AmberOk`):** `NoRefute`, `DropsOk`, every equation
  dropped, and every side condition implied (the premises plus its
  negation have a refutation).
- **Over{j, s, w} (`OverOk`):**
  - `NoRefute`;
  - with c's derivable equations set aside (some d with `DropsOk`), j is
    c's, and s is made of c's other equations and earlier solved ones
    (`clean`);
  - `Overdet(s, w)`.

These cases exclude each other, so `honest_unique` is an induction along
the order (the fourth audit's proof, below). The global facts become
library theorems, not trust:
- the kept system has no refutation;
- the solved equations are independent modulo constants;
- the solved equations have a matching.

## The laws

A = `SO.solve_l(sk, g0, l)`, cls = `SO.Out.cls(A)`, red = `SV.reds(cls)`,
ds = `SV.dropped(cls)`, solved = `SV.solved(sk, red, ds)`.

**From the verdict** (when ok; independent of how the answer was found)
1. `solve_exists`, `solve_unique`, `solve_pins`: unchanged, over red.
2. `solve_regular`: the certified geometry is a regular point of the
   solved system in the free variables. The verdict checks that the
   plan's pins are the reported pins, and that the plan's variable and
   equation orders cover exactly the variables and the solved equations.
3. `solve_blame`: every conflict's support is consistent, because the
   certified geometry satisfies it.

The verdict also checks the drop certificates, and the amber side
conditions by their refutations in `Amber`'s refs (audit 4.7), not by
balls.

**Honesty** (about the search, for every wf sketch, ok or not)
4. **`solve_honest`**: `Honest(sk, cls)` at every level. (v4's
   `solve_red` is part of it now.)

**The spec pins the answer down** (about the spec alone)
5. **`honest_unique`**:
   ```
   law honest_unique:
     for +sk: SK.Sketch
     for  w: SK.Sketch.wf(sk)
     for +c1: List<&2, SV.Class>
     for  h1: SV.Honest(sk, c1)
     for +c2: List<&2, SV.Class>
     for  h2: SV.Honest(sk, c2)
     for +c: Nat
     for +j: Nat
     M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool})
   ```
   Every constraint gets the same kind, and every equation is dropped in
   both or in neither.
   - The induction (audit 4): agreement before c gives equal premises and
     equal earlier solved equations; then c's drops are forced, Conflict
     is forced by a refutation and excluded by its absence, Over by an
     over-determined set, and amber either way.
   - The delicate steps are list bookkeeping: `owners` is nondecreasing;
     support lists embed into the premises; side lists are re-indexed.
   - Only the shown Over witnesses, which irreducible support is shown,
     the pins and the box may differ between solvers.

**Semantic corollaries** (from 4 and the spec)
6. `solve_drop`: wherever the solved equations hold, every dropped
   equation holds.
7. `solve_amber`: deleting every amber constraint changes no solution.
8. `solve_conflict`: c and its support cannot all hold, so c cannot be
   restored. Blame is earned: the support alone has no refutation.

**Search facts**
9. `solve_total` v2: cls = `cls_of(sk)` (from the sketch alone);
   `wf_dec(mark(red, sk))`; distinct, in-range pins; and
   `&m -> Perfect(solved, free(nvars, 0n, pins_of), m)`.
10. `solve_complete` v2:
    - Regular for the solved system;
    - `dy` for kept constraints only;
    - `hs`: `Strict` over the side conditions of the kept *non-amber*
      constraints, i.e. `sides(mark(red ++ ambers, sk))`. Amber sides
      are certified by their refutations instead, so one that holds with
      equality is fine. `Strict` itself is refined: a ≥ 0 side whose
      variables are all pins may hold with equality.

**What a refusal means today**
11. `solve_refused`: if no level certifies, the drawing itself is not a
    regular solution of the solved system in the solver's free variables.
    That's all it says; the stronger forms are open laws.

## As written in ROADMAP (S0b, 2026-10-19)

The spec is now `spec/solve.bend` and `spec/sketch.bend`, and laws 1–11
are written out in ROADMAP.bend; `tools/stmtcheck.py` type-checks the open
ones. Choices made while writing them, for the S9 audit:
- **`Cert` is `Comb`.** The drop certificate's constructor clashed with
  the block certificate's (`lib/certdef.bend`); Bend's constructor names
  are global.
- **`cov`** (the sketch's variables are below `nvars`) is a hypothesis of
  `solve_honest`, `solve_drop`, `solve_amber` and `solve_conflict`, as it
  is of `solve_total`: the solver's structure stage assumes it.
- **`solve_regular`** is about any x in the box meaning the sketch less
  its red constraints (by `solve_unique`, the certified geometry).
- **`solve_blame`** holds for every position c: a constraint that is not
  a conflict has an empty support, which the certified geometry meets
  too.
- **`solve_refused`** takes x to be the drawing read in F
  (`N.ofkv(g0)`), with law 10's hypotheses at x and every level refusing.
- **`solve_complete`**'s `dy` is `dyadic(mark(red, sk))`: the constants
  of the kept constraints (amber ones included) only.

Until the sk-13a stage lands (PLAN S4), the solver's classes come from
sk-09's red stage (Over with its old syntactic witness at each red
constraint, Kept with nothing dropped elsewhere). The verdict laws
(`solve_exists`, `solve_unique`, `solve_pins`) are proven over
`reds(cls)`; sk-09's totality and completeness are proven in interim forms
over the classes (`total_now`, `complete_now` in tests/solve_laws.bend),
the latter with `Strict` and no pins. sk-09's `explained` and its witness
type live on in `lib/why.bend` as facts about the old stage; no law
mentions them, and the verdict no longer checks them.

## Open laws (in ROADMAP when their phase starts)

- `solve_refusal_explained` (sk-13e): every refusal is explained as a red
  constraint, a singular configuration naming the block, or a
  quantitative bound.
- Implicit equalities (with the simplex): an equation forced by side
  conditions alone is dropped and can be amber.
- A ≥ 0 side that is not amber and holds with equality on free variables
  (audit 4.7). Today `Strict` excludes it.
- Pins from the drawing (Q26, after sk-13a and the presolve). This
  removes `solve_complete`'s "in the solver's free variables".
- A red constraint's deviation at the solution (sk-19).
- Directions and lengths (sk-13b/c), with nondegeneracy hypotheses.
- Phase 4:
  - higher-degree derivations;
  - real-only implications;
  - branch-selecting constraints;
  - Over decided exactly (Q22).
- The solution nearest the layout (§10.3, Q27).
- The exact linear presolve (right after sk-13a), with its law.

## Where the fourth audit's findings went

1. The deletion filter tests members' full equations (PLAN S3).
2. `wfdec`'s `cmerge` goes with S0a, along with `wfcpf`, `covpf`,
   `sketch_demo`, the LAWS.bend comment, and saved IR unshared on load
   (PLAN S0a).
3. Syntactic structure: dependence by derivative (Q30).
4. Stale text: fixed in the drafts; the LAWS.bend comment is in S0a;
   DESIGN §4 and §8.11 are fixed.
5. `honest_unique` typed: above (it type-checked in the audit's scratch
   copy).
6. Proof sketch: Over's exclusion uses `clean` and the drop conditions;
   Conflict's uses `Drop0`-style rewriting and side re-indexing; no
   decision procedure (PLAN S6).
7. Amber sides certified by their certificates: law 10 and the verdict.
   The non-amber case is an open law.
8. "Driving" in place of "has an equation": `driving`, `all_driving`.
9. Open laws: Q26, sk-19, ≥ 0 at equality, added.

## Questions

1. Any changes to the spec or laws?
2. Should branch-selecting constraints (Phase 4) look different from amber
   in the page?
