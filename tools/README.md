# Drafting tools (untrusted)

Some library files are expanded from drafts; edit the draft and regenerate,
the checker verifies the output.

| Output | Source |
|---|---|
| `lib/flaws.bend`, `lib/fring.bend`, `lib/ford.bend`, `lib/meaning.bend`, `tests/fring_demo.bend` | `tools/drafts/*.draft` via `python3 tools/expand.py tools/drafts/X.draft <output>` |
| `lib/mforms.bend` | `python3 tools/mforms.py` (from `spec/sketch.bend`) |

Draft macros (`tools/zexpr.py`): `@ATOMS name = a=term,, m:=expr,, ...`
names atoms and textual abbreviations; `@ZEQ[set | lhs | rhs]` is one
normalizer call; `@FT[set | e]` is the field term of `e`;
`@CERT[set | x | c1 ; r1 | ... || hyps]` proves `x = 0` from `ri = 0` with
one normalizer call (`x = Σ ci ri`); `@CERTEQ[set | X | Y | ...]` proves
`X = Y` the same way. Then `tools/expand.py` turns the shorthand `@A(`,
`@M(`, `@S(`, `@N(`, `@0`, `@1`, `@T`, `@LK(` ... into Bend.
