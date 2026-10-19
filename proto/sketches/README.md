# GUI sketches for the regression

Sketches Danielle drew in the sketcher (gui/) and exported, each kept as
its GUI export (`NAME.json`) and as the solver input it becomes
(`NAME.in`; `NAME.raw.in` keeps the repeats the page leaves out).
`tools/regress.sh` runs `gui/solve_cli` on each input and compares with
`expected`. `gen.sh` regenerates the inputs from the exports; run it only
when the page's request-building (gui/model.js, gui/relax.js) changes on
purpose, and check that the answers stay right.

| name | exported as | what it shows |
|---|---|---|
| zeros | sketch.json | zeros' exponents compounding in a sparse elimination; certifies in under a second since `dsig` puts zeros at exponent 0 (2026-10-18) |
| base | sketch(1).json | the drawing (2) and (3) build on; certifies |
| oncircle-thrice | sketch(2).json | the same OnCircle three times; the raw input keeps the repeats and is refused |
| oncircle-pairs | sketch(3).json | two OnCircle pairs repeated; raw is refused after every precision (the slowest here) |
| vertical-twice | sketch(4).json | (3) with a direction dependency: segment 28 is made vertical twice, through #25 perpendicular, #27 and #38 parallel (tools/diag/README.md §4); refused with or without repeats, which no structural count can see |

Since S0a (PLAN-sk13a.md, 2026-10-19) the inputs keep every variable and
send merges as equations (Q29); before, merged points shared variables.

The refusals are today's answers. sk-13 (PLAN-sk13.md) is to make each one
either amber (implied, holds anyway) or a stated conflict; update
`expected` as each phase changes them.
