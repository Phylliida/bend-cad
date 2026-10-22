# Audit of sk-13w (machine words), W7

Independent audit by a separate Claude Opus 5.5 agent, 2026-10-22, of the
claim that the solver that runs (gui/solve_cli.bend → `FS.wsolve`) returns
exactly what `SO.solve_l` returns, through ROADMAP's `fast_solve`, proven in
tests/fast_laws.bend as lib/fastpf.bend's `solve_l_eq` at the word instance
in base 2^12. I checked against the tree at d275e98 with Bend. Every planted
error was made on scratch copies outside the repo. The only repository file
written is this one.

**Verdict: the claim holds. No blocker.** `fast_solve` says what is claimed,
for every sketch, drawing and level. Its proof reaches the whole chain, and
it relies on nothing unsafe or foreign. The instance it is proven at is the
one the CLI runs. Every planted error I tried was refused. Every draft
regenerates its lib file byte for byte. The gate passes (54 s), and so does
the regression (57 s). The PLAN's instruction counts reproduce exactly, and
the outputs are byte-identical. What remains is
stale documentation (two pointers to theorems that don't exist, and
leftovers of the 2^23 and 2^14 bases), one GUI rebuild gap, and some dead
code.

## Findings, most serious first

**1. Should fix: two header comments name theorems that don't exist, and
one gives the wrong base.**
- `lib/fastpf.bend:7-8` (and `tools/drafts/fastpf.draft:7-8`) says "At the
  CLI's word dyadics in base 2^14 (FS.wsolve), with the word laws at that
  base, it is SO.solve: wsolve_eq". There is no `wsolve_eq` anywhere. The
  instance is in tests/fast_laws.bend (`fast_solve`), and the base is 2^12.
- `lib/fast.bend:8` says "(lib/fastpf.bend: fsolve_eq)". No such def
  exists; the theorem is `solve_l_eq` (`lib/fastpf.bend:210`).
- `lib/pops.bend:7`, `lib/gnumer.bend:8`, `lib/gmap.bend:4` and
  `lib/wnumpf.bend:5` cite `lib/gnumerpf.bend`, which doesn't exist
  (`ls lib/gnumerpf.bend`: no such file). The proofs are in gelimpf,
  gnewtpf and gplanpf, and `plan_t` is in gplanpf.

These are the files a reviewer opens to find the main theorem, and they
send the reviewer to names that aren't there.

**2. Should fix: the base 2^23 survives in the bound comments, and in the
gate's only closed check of the run-time bound.**
- `tests/wmag_demo.bend:97-103`: `l23` proves `(1+22) + (1+22) <= 48`, and
  its comment says "the run time's 2 L = 46 is within BendRT's 48-bit
  immediates". The run time's L is 12, so 2L = 24.
- `tests/wmag_demo.bend:1-4` says "the base RW.wbp(lp) the solver uses ...
  (the CLI passes 22 ...)". The solver uses the literal bp = 4095, lp = 11
  (`lib/fast.bend:263-267`), and nothing passes 22.
- `lib/wmagpf.bend:6` ("the run time's is 2^23") and `:873-874` ("the run
  time's L = 23 gives 2 L = 46 <= 48"), and the same lines of the draft
  (`tools/drafts/wmagpf.draft:6, 887`).
- `rt/wmag.bend:1` ("2^23 at run time").
- PLAN-sk13w.md W2 "Done" (`:192-195`): "the solver's base `wbp(lp)`", and
  "limbs below 2^23 keep every native intermediate below 2^46, and 46 <= 48
  is a closed check".

The bound holds a fortiori at 2^12 (h·k + c ≤ (2^12−1)² + 2^12 − 1 < 2^24;
see "Run-time arithmetic" below). But the documented instance, and its one
closed check, are no longer the base that runs. Suggested fix: `l12` with
`(1+11) + (1+11) <= 48`, and the comments changed to L = 12, 2L = 24.

**3. Should fix: gui/serve.py doesn't rebuild the solver when rt/ changes.**
`gui/serve.py:106-113` (`sources()`) watches the CLI, `proto/block.bend`,
lib/ and spec/. Since sk-13w the CLI's import closure also includes
`rt/{mag,big,wmag,wint,wdyad}.bend` (through lib/wnum.bend). It also
includes `proto/int.bend`, which was already missing before sk-13w. After an
edit to rt/, the page keeps running a stale `gui/solve_cli`, so it runs code
other than what the gate proved. Add rt/ and `proto/int.bend` to
`sources()`, and to `gui/README.md:13`.

**4. Nit: DESIGN §14 slightly overstates what the bound lemmas cover.**
`DESIGN.md:1869-1871` says "With limbs below 2^12 every native intermediate
(a limb product plus carries) stays below 2^24 (lib/wmagpf.bend:
`mul_bound`, `add_bound`)". Two things are off:
- The lemmas are generic (below 2^(2L)). The L = 12 instance is by reading
  (PLAN W2 says so), and nothing in the gate instantiates them at 11.
- Exponents, shift amounts, bit counts and precisions are native Nats too,
  and no lemma bounds them. They are the reference's own values (the twins
  are exact, so the exponents are S.D's), so this is not a new reliance.

The native list (`:1866-1867`) also omits `Succ`/predecessor matching and
`nat_double`, which comp.ts compiles natively too (`OPTIMIZED.Nat.Succ`,
`nat_double`). Suggested wording: "every limb operation (a limb product plus
carries) stays below 2^24, by `mul_bound` and `add_bound` read at L = 12;
exponents and bit counts are S.D's own".

**5. Nit: PLAN-sk13w.md's v1 body contradicts its as-built notes, and isn't
marked as superseded.**
- `:38` and `:76`: the base 2^23.
- `:73-78`: "The plan proves it cannot happen". As built, the run-time
  instance is by reading.
- `:67-71`, `:80-83` and `:374`: `solve_ref_l` and demos moved to
  `solve_ref`. Nothing was renamed.
- `:168`: lib/wnat.bend. `:226`: lib/wnumer.bend and lib/wdmat.bend.
  `:261`: `final_fast`.
- `:341-342`: "testing each operation against its base definition, which
  W0 does". W0 compared whole kernels with S.D.
- `:161` pins a count ("The four verdict laws").

The Done notes are accurate. A line under the title ("v1 plan; each step's
Done note is as built") would do.

**6. Nit: other stale lines.**
- The HANDOFF title (`HANDOFF.md:1`) still reads "next: S5's laws 1–3,
  then S6". This predates sk-13w.
- `HANDOFF.md:280-281`: "The base is a parameter lp everywhere" is W2's
  state. As built, the libraries are generic and the instance is a literal.
- `tools/regress.sh:2`: "about 2 min". It takes about a minute, as
  tools/README.md and PLAN W6 now say.
- tools/README.md's regress paragraph doesn't mention the new "the
  reference agrees" line that solve_run prints.
- `rt/mag.bend:3` and `DESIGN.md:160`: "the runtime passes bp = 65535".
  That is sk-02's demo, but the solver now passes 4095.
- `rt/wmag.bend:159-160`: `wbp`'s rationale ("computed once at the top") is
  obsolete. `wbp` is now used only by tests/wmag_demo.bend and `wbp_ok`.
- `lib/wmagpf.bend:871`: "a limb against 2^r with r <= L". The code only
  uses r ≤ lp = L − 1 (with r = L, 2^r = B > bp breaks `mul_bound`'s
  premise).

**7. Nit: dead code.** These are defined and never used:
- `lib/wnumpf.bend:38` `w_ofq` (`wh` uses `wofq_mm`)
- `lib/certhpf.bend:104,109` `q_h`, `ym_h`
- `lib/fastpf.bend:213` `solve_eq`
- `lib/wmagpf.bend:894` `add_bound` (`mul_bound` is used only by the demo,
  at a variable lp)
- `RW.wbp` at run time

This is harmless, but every unused lemma is something a reviewer reads.

**8. Nit: seven of the eleven sk-13w generated libs lack the "Generated
from tools/drafts/X.draft ... edit the draft" header.** khompf, certhpf,
planhpf, gelimpf, gnewtpf, gplanpf and fastpf lack it; wmagpf, wintpf,
wdyadpf and wsigpf have it. The house is mixed (25 of the 70 drafted libs
lack it), but the W4-W6 files are the ones most likely to be hand-edited by
mistake.

**9. Nit (pre-existing, recorded for completeness): lawsync compares text
and ignores imports.** `tools/lawsync.py` compares a law with its
restatement token for token, but never reads what the aliases bind. In a
scratch copy, `import ../lib/solve.bend as FS` in tests/fast_laws.bend
still gave "ok fast_solve". I checked by hand that fast_laws's aliases (S,
SK, SO, FS) bind the same files as ROADMAP's. A changed conclusion is caught
("DIFF fast_solve").

**10. Recommendation (performance, not correctness): the pass is still
walked twice.** `FS.solve_da` (`lib/fast.bend:241-242`) computes `PA.pass`
for the classes and `PA.pass_st` for the solved positions: the same walk
twice, each with its simplex. By my count `SO.solve_lw` walks it nine times
(PLAN: "about ten"). The PLAN says the pass's exact simplex now dominates, so
one walk that returns both would be the next cheap win. Its equality with
the two would be one lemma by induction on the records.

## What was checked, and holds

**1. Nothing assumed.**
- The new files (rt/wmag, wint, wdyad; lib/wmagpf ... fastpf; the two tests;
  solve_cli; solve_run) have no `@unsafe`, no foreign code, no other
  attribute and no `law`. A body-less law anywhere in a loaded book fails
  the check with "TODO found" (`bend2/main.ts:774-777`).
- Every new lib/ and rt/ file is in the import closure of
  tests/fast_laws.bend, which check.sh checks as its own root.
  tests/wmag_demo.bend restates W2/W3, and tests/solve_demo.bend reaches
  lib/fast.bend through proto/solve_run.bend.
- The reliance report (`bend2/main.ts:688-724`) walks from the root's own
  defs through the names in each def's type and body, transitively. Because
  `fast_solve`'s type names `FS.wsolve_l`, the walk covers the fast
  solver's code as well as its proof. I confirmed this by planting:
  `@unsafe` on `pw_add` deep in lib/wmagpf.bend, and separately on `dapp_t`
  in lib/gelimpf.bend. Each gave "1 def relies on unsafe or foreign code:
  fast_solve". The gate fails on that, both by its grep and because the
  line is not the exact "All terms check.".
- gui/solve_cli.bend itself is outside the gate. regress.sh builds it, and
  the build type-checks it. It is the untrusted parse-and-print driver, and
  the solver it calls is covered through `fast_solve`'s type.
- `./check.sh`: GATE: PASS, 54 s (fast_laws.bend alone: 45 s).

**2. The law says what is claimed.**
- The CLI prints its answer from that call. `run.go` (`gui/solve_cli.bend:592-594`)
  prints `show(sk, FS.wsolve(sk, g0))`. `FS.wsolve` is `wsolve_l(sk, g0, 0n)`
  (`lib/fast.bend:273-274`), and `SO.solve` is `solve_l(sk, g0, 0n)`. Every
  printed field (ok, red, pins, cls, gc, gr) comes from that `SO.Out`,
  except `own`, which is `SV.owners(sk)` from the spec. The plan is not
  printed. No printed number comes from anything but the proven answer. The
  only remaining reliance is BendRT's natives, which DESIGN §14 lists.
- The instance is the one the CLI uses. `fast_solve` is
  `FP.solve_l_eq(~FS.wk(), ~FS.wo(), ~WP.wlaws(4095n, 11n, {==}), ...)`,
  and `wsolve_l` is `solve_l(~wk(), ~wo(), ...)`. They are the same defs, so
  `PLaws<FS.wk(), FS.wo()>` unfolds to `wlaws`'s type.
- Planted at the instance:
  - `wlaws(4095n, 12n, ..)` was refused ("expected 8192n, observed 4096n").
  - `wk`/`wo` and `wlaws` all moved to lp = 12 (base 2^13 claimed with
    bp = 4095) was refused the same way. So `hb` is really evaluated.
  - The conclusion changed to level `1n+l` was refused.
- The statement is unconditional (every sk, g0, l; no well-formedness), and
  it equates whole `SO.Out` values, plan included, so every law about
  `SO.solve_l` transfers by rewriting.
- lawsync really compares the restatement with ROADMAP's draft: "ok
  fast_solve", and "DIFF fast_solve" after a planted change in the
  conclusion (alias caveat in 9).

**3. The definitional step.** `solve_lw_unf` (`lib/fastpf.bend:197`) is
`{==}`. I unfolded both sides by hand:
- `cls` is `PA.pass(..)` = `PA.classes(sk)` = `cls_of(sk)`.
- `sp` is `PS.bp(pass_st ..)` = `solved_pos(sk)`.
- `ST.KD.red(kv)` is `pins(sk)`.
- The renum term is `PA.skel(sk)`.
- `SV.solved(sk, reds cls, dropped cls)` is `kept(sk)`, and `PA.nvars` is
  `nvars`.

So it is the same function, with shared values substituted. The equality is
not vacuous: in a scratch copy, passing `sp` as the pins in `solve_kv`
made lib/fastpf.bend fail at `solve_lw_unf`, both alone and through
fast_laws.

**4. Run-time arithmetic at base 2^12.** Here is every native operation on
limbs, with bp = 4095:
- `Mag.mul1` (h·k + c, carry ≤ bp): ≤ 2^24 − 2^12.
- `Mag.add.go` (a + b + carry ≤ 1) and `Mag.addc`: < 2^13.
- `Mag.sub.go` (B + ah, t = bh + w): < 2^13.
- Shifts multiply by `pw(r)` with r ≤ 11 (`rt/wmag.bend:38, 56`), so a
  factor ≤ 2^11. 2^k is built only for k < L.
- `Mag.ofpos.go`: cur + w < 2^12, w ≤ 2^11. `Mag.lb` and `Mag.nb` work on
  single limbs.

All of these are far below 2^48. The other native Nats are the exponents,
the shift amounts `e_b − e_a`, the bit counts (`Big.size`, a multiple of 12
plus a limb's), and the precisions (≤ 512 at level 0). They equal the
reference's own values, which were already native.

A fail-stop is reachable only for absurd input: a drawn exponent near
2^47 in sketch.in, or a level around 80, where the precision 64·2^(l/2)
passes 2^48 (memory would run out long before). Both would fail-stop the
reference just the same, and the CLI runs level 0 only.

Measured with tools/diag/icount on slowsketches 6 and 7 (replayed with
`--repeats`), against a scratch CLI calling `SO.solve`, the PLAN's numbers
reproduce exactly:

| sketch | reference | words | output |
|---|---|---|---|
| 6 | 91.739 G | 19.377 G | byte-identical |
| 7 | 123.747 G | 23.392 G | byte-identical |

**5. The generic proofs.**
- **Statements read against the definitions:**
  - khompf: `kball_h`, `held_h`, `keval_h`, `kvle_h`, `klen_h`
  - certhpf: `factor_h`, `shape_h`, `box_h`, `ccheck_h`
  - planhpf: `keq_h`, `kveq_h`, `side_ok_h`, `sides_ok_h`,
    `check_sides_h`, `pcheck_h`
  - gelimpf: `dpivot_t` (the pivot index is numer's), `dgj_t`, `dinverse_t`
  - gnewtpf: `newton_t`, `rsearch_t`, `grow_t`, `dclose_t`
  - gplanpf: `pblocks_t`, `plan_t`
  - gmap's maps
- **What they say, and how they are proven:**
  - Each states what its name says: the function in L (or at K) on the
    images equals the image of the function in K (or of numer's on S.D).
    Where the result is a verdict, an index or a length, it is the same
    value.
  - The proofs I read rewrite subterms with the commuting lemmas below them
    and close with `{==}`. None leans on anything but the Hom and PLaws
    fields.
- **PLaws can't be satisfied vacuously:**
  - `l_tod` makes the map injective: tod(h(x)) = x for every S.D x. A
    degenerate K can't satisfy it.
  - The Hom fields and `l_ofd` fix K's arithmetic on the image of ofd, and
    the fast solver only ever computes on such images.
  - PLaws is inhabited inside the gate, by `wlaws(4095n, 11n, {==})`.
  - `fast_solve`'s statement doesn't mention PLaws at all, so a weak PLaws
    could not have weakened the law. It needs only a checked inhabitant.
- **Planted errors** (beyond those in 2 and 3):
  - `wops`'s sig rounding to `1n+b` bits was refused at `wlaws`
    (`sig_ok`).
  - The two `@unsafe` plants in 1 were reported.

**6. Drafts.** `python3 tools/expand.py tools/drafts/X.draft <scratch>`,
then `cmp` against lib/X.bend: identical for all eleven (khompf, certhpf,
planhpf, gelimpf, gnewtpf, gplanpf, fastpf, wmagpf, wintpf, wdyadpf,
wsigpf). tools/README.md has a row for each.

**7. Docs.**
- These are true:
  - DESIGN §14 (but see 4)
  - ROADMAP's sk-13w comment and `fast_solve`
  - the HANDOFF sk-13w paragraph (but see 6)
  - tools/README.md's rows and its regress timing
  - gui/README.md's "What runs where" (but see 3)
  - the headers of tests/fast_laws.bend, rt/wdyad.bend, lib/khom.bend,
    lib/wnum.bend and lib/fast.bend's base comment
  - PLAN W4-W6 "Done": the 47 s (I measured 45 s), the 4.7x and 5.3x,
    "about a minute" (57 s), and "a planted 2^13 is refused" (confirmed)
- Stale lines are listed in 1, 2, 5 and 6.
- No new doc pins a count of laws or lemmas, except PLAN `:161`.

**8. Nothing else suspicious found.**
- The two mirrored quirks are mirrored on purpose and proven: rounding by
  2^0 adds one (never reached), and `QRD.size(zpos(0)) = 1`.
- solve_run's run-time agreement check compares ok, pins and boxes, not
  classes or plans. That is fine as a smoke test, since the law covers the
  rest.
- Dead code and the second walk of the pass are in 7 and 10.

## Commands run

From bend-cad/, with scratch at
`/tmp/claude-1000/-home-bepis-prog-verus-cad/45f9abcf-6a77-48c6-819a-5de706ebdf0f/scratchpad/audit13w/`:

- `./check.sh`: GATE: PASS, 54 s.
- `tools/regress.sh`: REGRESS: PASS, 57 s.
- `python3 tools/lawsync.py`: DRAFTS IN SYNC. Re-run on a scratch copy with
  a changed conclusion (DIFF) and with a changed alias (ok).
- `bin/bend tests/fast_laws.bend --check-only` on scratch trees (with
  `BEND_SRC=../bend`): the baseline, then
  - wlaws at lp = 12
  - the whole instance at lp = 12
  - the conclusion at level 1+l
  - `solve_kv` with the wrong pins (also `bin/bend lib/fastpf.bend
    --check-only`)
  - `wops` sig off by one bit
  - `@unsafe` on `wmagpf.pw_add`, then on `gelimpf.dapp_t`
- `python3 tools/expand.py tools/drafts/X.draft <scratch>/X.bend` and
  `cmp`, for the eleven drafts.
- Import-closure and unused-definition scans (scratch Python).
- `bin/bend gui/solve_cli.bend -o` and a scratch `solve_ref.bend` (the same
  CLI with `SO.solve`); `tools/diag/replay.mjs --repeats` and `totext.py`
  on slowsketches 6 and 7; `icount` on both binaries, and `cmp` of the
  outputs.
- Read: PLAN-sk13w.md, ROADMAP.bend, DESIGN.md §14, the HANDOFF paragraph,
  tools/README.md, gui/README.md, gui/serve.py, every new rt/ and lib/
  source file, and the drafts' statements; Bend's
  `bend2/main.ts` (`cli_report`, `book_read`), `comp.ts`'s native Nat
  table and base.bend's Nat definitions.

## Resolution (2026-10-22, the main session)

- Findings 1-3 (should fix) are fixed. The header pointers now name
  `solve_l_eq`, tests/fast_laws.bend's `fast_solve`, and gelimpf, gnewtpf
  and gplanpf. The 2^23 leftovers now say 2^12: the demo's closed bound
  check is `l12` (24 <= 48), and the wmagpf, rt/wmag and PLAN W2 comments
  are updated. gui/serve.py's `sources()` now watches rt/ and
  proto/int.bend.
- Nits: DESIGN §14 is reworded as suggested (the bounds read at L = 12,
  the native list completed, exponents being S.D's own). The PLAN has a
  note under its title saying its v1 body is superseded by the Done notes,
  and the pinned count is gone. The HANDOFF title, regress.sh, the
  tools/README regress paragraph and the `bp = 65535` comments are
  updated. The dead `w_ofq` and fastpf's `solve_eq` are removed. `q_h`,
  `ym_h` and `add_bound` stay: the first two complete the certificate
  fields' lemmas, and `add_bound` is half of the bound argument. The seven
  new drafts carry the generated-file header.
- The performance idea, one walk of the pass, was built just after this
  audit's snapshot. `walk2` gives both `PA.pass`'s classes and
  `PA.pass_st`'s state, and fastpf's `walk2_cls`/`walk2_st` are proven by
  induction. `solve_lw_unf` now rewrites with them instead of `{==}`, and a
  planted omission of the second rewrite is refused. Sketch 6 takes
  16.5 G instructions, sketch 7 19.5 G, with byte-identical answers.
- Also after the snapshot: the old thR/w2 hypotheses were removed from
  radpf, blockpf and scalepf (law 10's chain). That changed no law;
  tests/block_laws.bend's restatement of the library lemma `block_ok`
  lost its w2.
- Gate PASS (54 s) and regression PASS (57 s) on the result.
