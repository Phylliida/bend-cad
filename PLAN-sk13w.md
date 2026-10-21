# Plan: sk-13w, verified machine-word arithmetic (v1, 2026-10-21, for Danielle's review)

The solver's numbers become machine words at run time, and nothing about
what it computes changes. The fast solver is proven to return exactly what
today's returns, so every law keeps its statement and its proof. Nothing
new is believed without proof.

## Why

slowsketches sketch(6) and sketch(7) certify, but slowly (natively,
single-threaded, sketch 6: 13.6 s):

| stage | time |
|---|---|
| classification | 0.3 s |
| structure (blocks, pins) | 0.7 s |
| the plan (Newton and certificates for every block) | 8.1 s |
| the verdict | 2.5 s |
| the verdict again, in `seal` | about 2 s |

- One 32×32 block (sketch 7 has a 32×32 and a 12×12). Inside a block
  Newton's solves, the approximate inverse and the certificate check are
  dense and cubic in the block's size.
- Every number is the spec's binary list (`S.Pos`: one constructor per
  bit), so a 64-bit multiply is thousands of list steps.
- The verdict runs twice (the search's `accept`, then `seal`).

Block size is Q26's question (pins from the drawing). This plan is the
arithmetic, which speeds every sketch.

**Bend 2, as it is (no changes to Bend):**
- The C lane compiles base's `Nat.add`, `Nat.sub`, `Nat.mul`,
  `Nat.divmod`, `Nat.cmp` and `Nat.is_lt` to native instructions on
  packed words. A Nat below 2^48 lives in the word itself; a Nat past
  2^48−1 is a numbered fail-stop, never a wrong value (BendRT §Limits).
- The type checker treats Nat literals as unary (one `Succ` per step), and
  source literals stop at 256. So proofs must never compute with a large
  base: the library is proven for any base, and the solver picks 2^23 at
  run time.

## The idea

**Word numbers in exact correspondence with the spec's.**
- Word naturals: little-endian lists of limbs, each below a base B (a
  Nat), with no top zero limb, so equality is structural.
- Word integers: a sign and a word natural.
- Word dyadics: `WD{m, e}`, a word integer mantissa and a Nat exponent,
  read as m·2^−e.

Conversions both ways with the spec's `S.Pos`, `S.Z` and `S.D` are proven
inverse. Every operation the solver uses is proven to commute with them
*exactly*: the same mantissa and the same exponent, not just the same
value. So rounding to p bits, and even a zero's exponent (the 2026-10-18
slowness), behave identically.

**Fast twins, proven equal.**
- **The proposer:** lib/numer.bend and lib/dmat.bend (Newton, the
  approximate inverse, the radius search) get word twins. Each twin
  function is proven to return exactly its reference's result, by
  induction mirroring the reference's definition.
- **The verdict:** the checker (lib/plan.bend, lib/cert.bend,
  lib/kball.bend) is already generic over its computing numbers (`N.Num`,
  DESIGN Q17), so it runs as is at a word-dyadic instance. A parametricity
  lemma per checker function shows that for a map between two `N.Num`
  instances commuting with every operation, the checker returns the same
  answer at both.
- **The switch:** today's `solve_l` is renamed `solve_ref_l`, the new one
  calls the twins, and one theorem says `solve_l == solve_ref_l`. Every
  law, restated in tests/, rewrites with it once at the top. The laws'
  statements do not change, and neither do their proofs (completepf,
  regpf and the rest stay about the reference).

**Overflow.** Correctness never needs a bound (the type theory's Nat is
unbounded), but a run-time value past 2^48 would fail-stop. The plan proves
it cannot happen: limbs below B, so every native intermediate is below
B² + 2B, and B² + 2B < 2^48 for B = 2^23, by power lemmas over small
exponents (no large literal is ever computed). Shifts by k bits move
limbs and shift within one limb; 2^k is never built as a Nat.

**The demos.** Tests that evaluate the solver in the type checker
(plan_demo, circle_plan_demo, solve_demo, sketch_plan_demo, sides_demo)
evaluate `solve_ref` (bit lists, as today); the equality theorem carries
their results to `solve`.

## Steps

### W0. Measure first (a spike; nothing committed as design)

- An unverified prototype: limb multiply, a 32×32 dyadic matrix product and
  one Newton step at 64 bits, against the S.D versions, natively. It gives
  the real speedup, before any proof is written.
- Confirm the C lane's natives on this exact code (and the fail-stop past
  2^48).
- List every S.D primitive the proposer and the checker use (lib/numer,
  lib/dmat, lib/kinst, lib/dyadic, the D functions in spec/num.bend), so W2
  twins exactly those.

### W1. The verdict once (independent; small)

The search's acceptance and `seal`'s `ok` are the same check of the same
answer. `seal` takes the search's result, with a lemma that it is the same
Bool. About 15–20% of a solve today, and it stays a win after the switch.

**Done (2026-10-21).** The loop returns a `Run` (the answer and the verdict
it reached on it) and `seal` is gone. `lib/solvepf.bend`: `loop_ok`
(the loop's bit is accept of its answer, by induction on the precisions),
`start_ok`, `run_final`, and `verdict` (a True ok is a True `final` of the
solver's answer). The four verdict laws and solve_blame take it; the
completeness proof's last step got shorter (no `final_of`). No law's
statement changed. Gate and regression pass, the answers byte-identical.
Measured in user-mode instructions (the machine was loaded, so wall time
was noise): sketch 6 from 104.5 G to 91.7 G, sketch 7 from 141.2 G to
123.7 G, about 12% each, a little under the estimate.

### W2. Word naturals and integers (lib/wnat.bend, lib/wint.bend)

- The representation, normal forms, and conversions with `S.Pos` and `S.Z`,
  proven inverse.
- add, sub, neg, mul (schoolbook, carries by divmod by B), cmp, shifts,
  each with its commuting law, for any base B ≥ 2.
- Lemmas about base's Nat operations as the type theory defines them
  (divmod's quotient and remainder, the order), and the bounds lemmas for
  B = 2^23.

### W3. Word dyadics (lib/wdyad.bend)

- `WD`, conversions with `S.D` proven inverse.
- Every primitive from W0's list (add, mul, neg, cmp, the rounding to p bits
  and zero normalization of `dsig`/`dznorm`, `ofq`), each with an exact
  commuting law.
- The `N.Num` instance `wnum()` and its map from `KI.dnum()`, commuting with
  every field of `N.Num`.

### W4. The fast proposer (lib/wnumer.bend, lib/wdmat.bend; the large step)

- Twins of numer.bend and dmat.bend, written to mirror them function by
  function, and each function's equality with its reference.
- The plan comes out in word numbers. `Out.plan` and the box are converted
  back to `S.D` once (linear in their size), so `Out`'s types do not
  change.

### W5. The fast verdict

- The parametricity lemmas for the checker functions the verdict uses:
  `PL.check`, `PL.check_sides`, `KB.kball` and what they call, at a map
  between two `N.Num` instances.
- `final_fast` runs them at `wnum()` on the word plan; a lemma that it equals
  `final` on the converted answer.

### W6. The switch

- `solve_ref_l` (today's definition, renamed), `solve_l` on the twins, and
  `solve_l == solve_ref_l`.
- Every restated law rewrites once; the demos evaluate `solve_ref`.
- Gate and regression green; times for sketches 6 and 7 and every
  regression sketch, before and after; tools/README.md's numbers.

### W7. Audit and sign-off

No law's statement changes. The audit checks:
- that the restatements still say what ROADMAP.bend says (lawsync does
  this mechanically);
- that nothing is assumed: every conversion and twin is proven;
- the one new reliance (below).

## The trusted base

Today the solver's arithmetic runs on constructors through BendRT's generic
machinery. After this plan it also relies on BendRT's C implementations of
six Nat operations (`nat_add`, `nat_sub`, `nat_mul`, `nat_divmod`,
`nat_cmp`, `nat_is_lt`, a line of C each) agreeing with base.bend's
definitions below 2^48. BendRT is unverified already (its docs say so), and
every program here runs on it, so this narrows nothing that was proven; but
it is a new specific reliance, and DESIGN §14 should list it. It is
checkable by testing each operation against its base definition, which W0
does.

## Order and size

1. W1, the verdict once (small, a quick win).
2. W0, the measurement (small; it decides whether to go on).
3. W2 and W3 (moderate: a standard verified bignum, done generically in the
   base).
4. W4 (large: the twins of about 1300 lines, each with an equality proof).
5. W5 (moderate to large: parametricity over the generic checker).
6. W6 (moderate), W7.

## Expected gain

Unknown until W0. A 64-bit multiply goes from thousands of list steps to
about nine native multiply-adds, and arithmetic is most of the plan and the
verdict, so an order of magnitude on those stages is plausible. The
classification (exact rationals in the simplex) is unaffected; word
rationals are a natural follow-on, and sk-13s's deeper layers would want
them.

## Risks

- **Check time.** The twins and the parametricity lemmas add numeric code
  the gate checks, and the checker instantiated at `wnum()` is re-checked
  as a template instance. Small files, measured as they land.
- **Representation-exact twins.** S.D's behaviour depends on its
  representation (a zero's exponent), so the twins must reproduce
  representations, not only values. The correspondence is exact by design;
  the risk is a primitive missed in W0's list.
- **Proof size of W4 and W5.** Mechanical but long; the reference code stays
  as it is, so nothing already proven is reopened.
- **The demos** move to `solve_ref`; a demo that cannot is rewritten.

## Relation to the other plans

- Independent of sk-13s (PLAN-sk13s.md); word rationals later help its
  layers.
- Q26 (pins from the drawing) shrinks blocks; the two gains multiply (a
  32×32 block as two 16×16 is about four times less dense work).
