# Drafting tools (untrusted)

Some library files are expanded from drafts; edit the draft and regenerate,
the checker verifies the output.

| Output | Source |
|---|---|
| `lib/flaws.bend`, `lib/fring.bend`, `lib/ford.bend`, `lib/meaning.bend`, `lib/qord.bend`, `lib/qemb.bend`, `lib/fmat.bend`, `lib/dmat.bend`, `lib/sb.bend`, `tests/fring_demo.bend` | `tools/drafts/*.draft` via `python3 tools/expand.py tools/drafts/X.draft <output>` |
| `lib/mforms.bend` | `python3 tools/mforms.py` (from `spec/sketch.bend`) |
| `lib/maxpf.bend` | `python3 tools/expand.py tools/drafts/maxpf.draft lib/maxpf.bend` |
| `lib/gjpf.bend` | `python3 tools/expand.py tools/drafts/gjpf.draft lib/gjpf.bend` |
| `lib/tarjanpf.bend` | `python3 tools/expand.py tools/drafts/tarjanpf.draft lib/tarjanpf.bend` |
| `lib/structpf.bend` | `python3 tools/expand.py tools/drafts/structpf.draft lib/structpf.bend` |
| `lib/keptpf.bend` | `python3 tools/expand.py tools/drafts/keptpf.draft lib/keptpf.bend` |
| `lib/permpf.bend` | `python3 tools/expand.py tools/drafts/permpf.draft lib/permpf.bend` |
| `lib/bndpf.bend` | `python3 tools/expand.py tools/drafts/bndpf.draft lib/bndpf.bend` |
| `lib/roundpf.bend` | `python3 tools/expand.py tools/drafts/roundpf.draft lib/roundpf.bend` |
| `lib/normpf.bend` | `python3 tools/expand.py tools/drafts/normpf.draft lib/normpf.bend` |
| `lib/dgjpf.bend` | `python3 tools/expand.py tools/drafts/dgjpf.draft lib/dgjpf.bend` |
| `lib/apxpf.bend` | `python3 tools/expand.py tools/drafts/apxpf.draft lib/apxpf.bend` |
| `lib/nwtpf.bend` | `python3 tools/expand.py tools/drafts/nwtpf.draft lib/nwtpf.bend` |
| `lib/radpf.bend` | `python3 tools/expand.py tools/drafts/radpf.draft lib/radpf.bend` |
| `lib/blockpf.bend` | `python3 tools/expand.py tools/drafts/blockpf.draft lib/blockpf.bend` |

`@MACRO NAME text` (a line) makes every `$NAME` below stand for `text`
(textual, longest names first, macros may use macros): long hypothesis lists
shared by many lemmas.
`@CONJ name` / `params: ...` / `- tag: expr` lines / `@END` (`tools/conj.py`)
defines `name(params)` as the conjunction (`SV.band`) of the exprs, with
an accessor lemma `name_tag` per conjunct and a constructor `name_mk`.
Draft macros (`tools/zexpr.py`): `@ATOMS name = a=term,, m:=expr,, ...`
names atoms and textual abbreviations; `@ZEQ[set | lhs | rhs]` is one
normalizer call; `@FT[set | e]` is the field term of `e`;
`@CERT[set | x | c1 ; r1 | ... || hyps]` proves `x = 0` from `ri = 0` with
one normalizer call (`x = Σ ci ri`); `@CERTEQ[set | X | Y | ...]` proves
`X = Y` the same way. For integers: `@RING[set | target | source]` is one
`R.ring_eq` call proving `{target == source}` in ℤ, and `@ZT[set | e]` is the
integer term of `e`. Then `tools/expand.py` turns the shorthand `@A(`,
`@M(`, `@S(`, `@N(`, `@0`, `@1`, `@T`, `@LK(` ... into Bend.

# Test-data generators (untrusted)

| Output | Source |
|---|---|
| `tests/cc_data.bend` (circle-circle block certificate) | `python3 tools/gen_cc.py` |
| `tests/chain_data.bend` (two-block plan, and the same system renumbered) | `python3 tools/gen_chain.py` |
| `proto/plan_chain.txt` (depth-N chain as a sketch + plan, read by `proto/plan_chain_run.bend`) | `python3 tools/gen_plan_chain.py [well\|flat] [P] [N] [ok\|halve:j\|shift:j]` |

`tools/axcheck.py` (run from `bend-cad/`) compares the Lean transcription
`lean/BendCad/Axioms.lean` with `spec/field.bend` and `spec/real.bend`.

# Gate helpers

- `tools/lawsync.py`: every ROADMAP.bend draft that some `tests/*.bend`
  restates (with its proof) must say exactly what the restatement says.
- `tools/stmtcheck.py`: every other (open) ROADMAP.bend law must
  type-check; each is filled by an extra False == True hypothesis in
  `proto/_stmtcheck.bend` (generated, ignored), so only the statement is
  checked.
- `tools/regress.sh` (not in the gate, ~40 s): builds `proto/solve_run.bend`
  natively and compares its answers with `proto/solve_run.expected` (the
  circle, the over-constrained pair, a free point, circles that cannot
  meet, the audit's midpoint and tiny-radius sketches); then builds
  `proto/skel_cmp.bend` and checks that the solver's structure of each
  kept system equals `structure(kept, nv)`.
