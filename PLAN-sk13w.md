# Plan: sk-13w, verified machine-word arithmetic (v1, 2026-10-21, for Danielle's review)

*Built 2026-10-22 (W0-W6; W7's audit: AUDIT-sk13w.md). The body below is
the v1 plan as reviewed; each step's "Done" note says what was built, and
where they differ the Done note holds: the proposer and the solver are
generic over their numbers rather than word twins, nothing was renamed
(the new law `fast_solve` links the solver that runs to `solve_l`), and
the CLI's base is 2^12, not 2^23.*

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

**Done (2026-10-21).** `proto/w0bench.bend` (untrusted, measurement
only) reads sketch(6)'s 32×32 Jacobian (proto/probe_block stage 4) and
runs each kernel both ways. Word dyadics are `WD{m: Big, e}` over sk-02's
verified runtime integers (rt/mag.bend, rt/big.bend) in base 2^23, with
shifts, bit length and rounding added. User-mode instructions
(tools/diag/icount.c); every word result converted back is the S.D result
exactly, mantissa and exponent:

| kernel (sketch 6's block) | S.D | words | ratio |
|---|---|---|---|
| the inverse at 96 bits (numer's dinverse: Newton's and Y's kernel) | 7.48 G | 0.55 G | 14× |
| Y·J through the checker's generic product (KA.kmatmul) | 4.02 G | 0.27 G | 15× |
| exact A·Aᵀ (ddot) | 0.67 G | 0.09 G | 7× |

- **Where S.D's time goes.** Alignment is part of it: `D.add` peels the
  common exponent one step at a time and multiplies the other mantissa by
  `Pos.pow2(k)`; `dcmp` cross-multiplies by powers of two. With alignment
  by shifting alone (k `XO` wraps, still bit lists), Y·J is 1.67 G, 2.4×;
  the rest of the 15× is limbs. So bit lists with shifts are not a
  substitute for words.
- **Where a solve's time goes** (sketch 6, 91.7 G after W1): classification
  about 3 G and structure about 6 G (exact rationals and graphs; this plan
  does not touch them), the plan about 58 G and the verdict about 19 G
  (nearly all dyadic arithmetic: Newton, Y and the radius search in the
  32×32 block, then the checker), and about 6 G after the verdict not yet
  attributed. At the kernels' 14–15× the solve would be about 20 G, some
  4–5× faster overall. That is an estimate: the slope evaluation and the
  radius search were not measured on their own.
- **Natives.** The bench runs natively with limbs below 2^23 (products and
  carries below 2^46 + 2^24). A Nat is exact through 2^48 − 1, and 2^48
  stops the run with "a Nat past the largest immediate 2^48-1" (exit 1),
  never a wrong value.
- **The primitives.** The checker (plan, cert, kball) uses only `N.Num`'s
  fields: zero, one, add, mul, neg, cmp, ofq. The proposer (numer.bend)
  also uses `dsig` and `dround` (rounding: bit length, shift right with
  rounding, `dznorm`), `dsdiv` (one per pivot, through ℚ), `dsigup` (the
  radius search, rarely), `dcmp`/`dabs`/`dmax`/`dclose`, and the checker's
  generic pieces at `dnum` (jac, vals, `CK.check`, `CK.svec`). The exact-ℚ
  inverse (`qinverse`) is no longer called.

**What W0 changes in the steps below.**
- W2 mostly exists: sk-02's `spec/big.bend`, `rt/mag.bend`, `rt/big.bend`
  with `lib/mag.bend` and `lib/big.bend` already prove add, sub, neg, mul
  and cmp refine `S.Z` for every base (`Big.val`), and `S.Z` has one
  representation per value, so value refinement is exact. W2 adds
  normalization, shifts and bit length for a base 2^L, the conversions
  with `S.Z` (proven inverse to `Big.val`), and the bounds lemma.
- Rare operations need no fast twin: `dsdiv`, `dsigup` and `ofq` can go
  through the conversions (to S.D, the S.D operation, back), and their
  equality with the reference is then immediate from the conversions being
  inverse. Only the hot ones (add, mul, neg, cmp, dsig, dround) get word
  algorithms with their own proofs.

### W1. The verdict once (independent; small)

The search's acceptance and `seal`'s `ok` are the same check of the same
answer. `seal` takes the search's result, with a lemma that it is the same
Bool. About 15–20% of a solve today, and it stays a win after the switch.

**Done (2026-10-21).** The loop returns a `Run` (the answer and the verdict
it reached on it) and `seal` is gone. `lib/solvepf.bend`: `loop_ok`
(the loop's bit is accept of its answer, by induction on the precisions),
`start_ok`, `run_final`, and `verdict` (a True ok is a True `final` of the
solver's answer). The verdict laws and solve_blame take it; the
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

**Done (2026-10-21).** Over sk-02's verified integers, for a base
2^(1 + lp) and every lp:
- `rt/wmag.bend` + `lib/wmagpf.bend`: shifts (`shl_val`: m 2^k;
  `shr_val`: the quotient by 2^k, pinned by inequalities, `Floor`), rounding
  to nearest (`round_val`), bit length (`bits_ok`, `Bits`; `ofpos_bits`:
  `Mag.bits(ofpos p) = QRD.size p`), conversions with `S.Pos`
  (`ofpos_nat`, `topos_ofpos`), well-formedness of every result, the
  uniqueness of a magnitude with no high zero limb (`canon_eq`), and the
  native bounds (`mul_bound`, `add_bound`: below 2^(2 L)).
- `rt/wint.bend` + `lib/wintpf.bend`: the canonical form (`Canon`;
  `Big.canon` keeps the value and is canonical), conversions with `S.Z`
  (`ofz_val`, `toz_ofz`), one canonical word integer per value
  (`canon_big_eq`, hence `ofz_of_val`), and `shl_zval` (a product with
  `Pos.pow2`).
- `tests/wmag_demo.bend` restates them at the base `wbp(lp)` for every lp
  and computes examples in base 4 by `{==}`.
- The bound's run-time instance is by reading: limbs below 2^L keep every
  native intermediate below 2^(2L), and at the CLI's L = 12 (W6) that is
  2^24; 24 <= 48 is a closed check (`l12`). A closed 2^48 cannot appear in
  a type (see W6).

The W3 twins take the shape `wop(s2w a, s2w b) == s2w(op(a, b))` for every
S.D input: the word result is canonical and has the right value, so
`ofz_of_val` makes it equal. No invariant is threaded through the solver.

### W3. Word dyadics (lib/wdyad.bend)

- `WD`, conversions with `S.D` proven inverse.
- Every primitive from W0's list (add, mul, neg, cmp, the rounding to p bits
  and zero normalization of `dsig`/`dznorm`, `ofq`), each with an exact
  commuting law.
- The `N.Num` instance `wnum()` and its map from `KI.dnum()`, commuting with
  every field of `N.Num`.

**Done (2026-10-21).** `rt/wdyad.bend`: `WD{m, e}`, `WD.ofd`/`WD.tod`,
`WD.add` (the larger exponent; the other mantissa shifted by the native
exponent comparison), `WD.mul`, `WD.neg`, `WD.cmp`, and the rounding
twins `WD.znorm`, `WD.sig`, `WD.round`; every result canonical.
`lib/wdyadpf.bend`: `tod_ofd`, `add_ok` (through S.D.add's closed form,
`dadd_le`/`dadd_ge`), `mul_ok`, `neg_ok`, `cmp_ok` (`WD.cmp` is
`KI.dcmp`). `lib/wsigpf.bend`: `znorm_ok`, `sig_ok`, `round_ok` (numer's
dznorm, dsig, dround), through numer's `pshr` as a quotient and the
word rounding's. Two quirks are mirrored, not fixed: the spec's
`QRD.size(zpos(0)) = 1`, and rounding by 2^0 adding one (never reached:
both callers round by k >= 1). `lib/wnum.bend`: the checker's `N.Num`
at words, and `lib/wnumpf.bend`: `WD.ofd` commutes with each of its
fields. Each law is `wop(ofd a, ofd b) == ofd(op(a, b))` for every S.D
input and every base; `tests/wmag_demo.bend` restates them.

### W4. The fast proposer (lib/wnumer.bend, lib/wdmat.bend; the large step)

- Twins of numer.bend and dmat.bend, written to mirror them function by
  function, and each function's equality with its reference.
- The plan comes out in word numbers. `Out.plan` and the box are converted
  back to `S.D` once (linear in their size), so `Out`'s types do not
  change.

**Done (2026-10-22), generic rather than word twins.** Bend instantiates
a template (`~K`) only at closed arguments, so the checker cannot run at
`wnum(bp, lp)` with a variable base; and the checker's numbers are unary,
so a closed computed base (2^23 - 1 from `wbp(22)`) is expanded and
compared digit by digit whenever two copies of the word instance meet,
which overflows the stack. So the proposer is written once over any
numbers (and proven once, generically), and the base is a literal at the
one closed instance:
- `lib/pops.bend`: `POps<K>`, the proposer's operations besides `N.Num`'s
  (ofd, tod, numer's dsig, dround, dsdiv, dsigup), and `PLaws<K, W>`: a
  map of computing numbers from `KI.dnum()` (lib/khom.bend, `Hom`) whose
  map is ofd, tod its left inverse, each operation numer's on the images.
  `lib/wnum.bend`: `wops`; `lib/wnumpf.bend`: `wlaws(bp, lp, hb)` for
  every base (rounding by W3's twins, the rare operations through S.D).
- `lib/gnumer.bend`: numer.bend's proposer over any K and W, function by
  function; numer's number-free functions are used as they are.
- `lib/gelimpf.bend` (the elimination), `lib/gnewtpf.bend` (Newton, Y,
  the radius search) and `lib/gplanpf.bend` (the block, the plan):
  `plan_t`, for every K, W and laws R, `GN.plan(W, es, nv, sk, h g0, p) =
  hpr(NU.plan(es, nv, sk, g0, p))`, by rewriting numer's images into
  gnumer's terms bottom up. `lib/gmap.bend` maps numer's result types.

### W5. The fast verdict

- The parametricity lemmas for the checker functions the verdict uses:
  `PL.check`, `PL.check_sides`, `KB.kball` and what they call, at a map
  between two `N.Num` instances.
- `final_fast` runs them at `wnum()` on the word plan; a lemma that it equals
  `final` on the converted answer.

**Done (2026-10-22).** `lib/khom.bend`: `Hom<K, L>` (h sends zero, one,
add, mul and neg to L's exactly, with the same comparisons and L holding
exactly the images of K's rationals) and the checker's data through it.
`lib/khompf.bend` (karith, kball), `lib/certhpf.bend` (cert:
`ccheck_h`, CK.check of a certificate's image is CK.check of the
certificate) and `lib/planhpf.bend` (`pcheck_h`, `check_sides_h`): every
checker function commutes with a Hom, each lemma by induction mirroring
its function. `lib/fast.bend`'s `final` is SO.final with its plan and
sides checked in K (lib/fastpf.bend).

### W6. The switch

**The base is a parameter (found in W2).** The checker evaluates closed
terms eagerly: a type mentioning `RW.wbp(22n)` (2^23 − 1, computed) builds
2^23 in unary and overflows the stack, while the same law with a variable
`lp` checks at once. So the fast solver takes `lp` as an argument, every
theorem holds for all lp (`solve_l(lp, ..) == solve_ref_l(..)` for every
lp), and only the CLI's `main` passes 22. (Superseded as built, below: a
template's arguments must be closed, so the libraries are proven for every
base and the solver runs at one closed instance with a literal base.)

- `solve_ref_l` (today's definition, renamed), `solve_l` on the twins, and
  `solve_l == solve_ref_l`.
- Every restated law rewrites once; the demos evaluate `solve_ref`.
- Gate and regression green; times for sketches 6 and 7 and every
  regression sketch, before and after; tools/README.md's numbers.

**Done (2026-10-22), with the law added rather than renamed.**
`lib/solve.bend` keeps its names and every law stays about `solve_l`; the
fast solver is `lib/fast.bend`, and one new law in ROADMAP.bend,
`fast_solve: FS.wsolve_l(sk, g0, l) == SO.solve_l(sk, g0, l)`, carries
every law to what runs (no law's statement or proof changed).
- `lib/fast.bend`: `solve_lw` etc. over any K and W (the same loop; the
  verdict with its plan and side checks in K and the rest read through
  tod; the answer sent back to S.D once). It computes the pass's results
  once (SO.solve_lw reruns the pass about ten times) and is definitionally
  SO.solve_lw's form with them substituted. `lib/fastpf.bend`:
  `solve_l_eq` for every K, W and laws R.
- The CLI's instance is base 2^12, a literal (`wk`, `wo`): the checker
  re-checks the generic proof at a closed instance, 47 s at 2^12 (98 s at
  2^13, a stack overflow at 2^14, from the unary base arithmetic it meets
  comparing word terms), and 2^14 ran sketch 6 only 4% faster.
  `tests/fast_laws.bend` restates `fast_solve` as `solve_l_eq` at `wk`,
  `wo`, `wlaws(4095, 11, {==})`, with 2^12 = 4095 + 1 evaluated by the
  checker (a planted 2^13 is refused).
- `gui/solve_cli.bend` and `proto/solve_run.bend` run `FS.wsolve`;
  solve_run also checks at run time that the reference gives the same
  boxes. Gate and regression pass; the regression takes about a minute
  (from about two).

| sketch | reference (S.D) | words, base 2^12 | ratio |
|---|---|---|---|
| sketch 6 (32x32 block) | 91.7 G | 16.5 G | 5.6x |
| sketch 7 | 123.7 G | 19.5 G | 6.3x |

(user-mode instructions; answers byte-identical.) About a factor of two
is the words; the rest is the pass run once (one walk, `walk2`, giving
both PA.pass's classes and PA.pass_st's state; fastpf's walk2_cls and
walk2_st). In the fast solve the runtime's memory management (about half,
callgrind's term_drop), the pass's exact simplex and the word arithmetic
remain, none dominant.

### W7. Audit and sign-off

**Signed off by Danielle (2026-10-31).**

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
