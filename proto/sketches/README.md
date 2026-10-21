# GUI sketches for the regression

Sketches Danielle drew in the sketcher (gui/) and exported, each kept as
its GUI export (`NAME.json`) and as the solver input it becomes: `NAME.in`
with exact repeats left out (as the page sent before PLAN-sk13a S8), and
`NAME.raw.in` with them, as the page sends now (written only when it
differs).
`tools/regress.sh` runs `gui/solve_cli` on each input and compares with
`expected`. `gen.sh` regenerates the inputs from the exports; run it only
when the page's request-building (gui/model.js, gui/relax.js) changes on
purpose, and check that the answers stay right.

| name | exported as | what it shows |
|---|---|---|
| zeros | sketch.json | zeros' exponents compounding in a sparse elimination; certifies in under a second since `dsig` puts zeros at exponent 0 (2026-10-18) |
| base | sketch(1).json | the drawing (2) and (3) build on; certifies |
| oncircle-thrice | sketch(2).json | the same OnCircle three times; in the raw input the repeats are amber (refused before sk-13a) |
| oncircle-pairs | sketch(3).json | two OnCircle pairs repeated; in the raw input the repeats are amber (refused after every precision before sk-13a) |
| vertical-twice | sketch(4).json | (3) with a direction dependency: segment 28 is made vertical twice, through #25 perpendicular, #27 and #38 parallel (tools/diag/README.md §4); refused with or without repeats (Over at #32), a dependency of degree above 0, for sk-13b; the slowest here |
| angle-lines | slowsketches sketch(5).json | a right triangle (Perpendicular at P0) with a directed Angle of 47 from P3→P0 to P6→P3: as directed it cannot hold (the drawing has −133 = 47 − 180, so the angle's cross product holds and its dot > 0 fails), and the solver refuses after every precision (about 20 s); no degree-0 refutation sees it |

Since S0a (PLAN-sk13a.md, 2026-10-19) the inputs keep every variable and
send merges as equations (Q29); before, merged points shared variables.

The small sketches from hchain on are PLAN-sk13a S8's, built by code
(`s8.mjs`, with the page's model; then `gen.sh`): a consistent and an
inconsistent HDistance chain, a partly implied midpoint, Distance 5 and
-5, Radius 3 and -5, an angle against its opposite, EqualLength(a, a),
Horizontal with VDistance 3, a repeated Coincident, the v4 audit's
Vertical/Coincident/HDistance support case, and a point-line distance from
the segment's own endpoint, whose equation mentions coordinates it does not
depend on (x - x + y).

The refusals are today's answers. sk-13 (PLAN-sk13.md) is to make each one
either amber (implied, holds anyway) or a stated conflict; update
`expected` as each phase changes them.
