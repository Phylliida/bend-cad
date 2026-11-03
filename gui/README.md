# bend-cad sketcher (GUI)

A page for trying the verified solver by hand: draw points, lines and
circles, constrain and dimension them, and see what the solver certifies.

```
python3 gui/serve.py            # then open http://localhost:8480/
python3 gui/serve.py 9000       # another port
```

The first start builds the solver binary `gui/solve_cli` from
`gui/solve_cli.bend` with `bin/bend` (about 20 s); it rebuilds when that
file or any of the solver's sources (`lib/`, `spec/`, `rt/`,
`proto/block.bend`, `proto/int.bend`) is newer, when the server starts.

## What runs where

- **Verified:** the word solver `FS.wsolve` (lib/fast.bend) answers every
  request: the verdict, each constraint's class, the pins, and the
  certified box. It is proven to return exactly `SO.solve`'s answer
  (lib/solve.bend; ROADMAP: fast_solve), so the laws about `SO.solve`
  (ROADMAP.bend, all proven) hold for whatever it is given: among
  them, the classes are the honest ones (solve_honest), honest classes are
  unique (honest_unique), a redundant constraint holds wherever the rest do
  (solve_amber), and a conflict cannot hold together with its support
  (solve_conflict).
- **Untrusted, and only shaping the input:**
  - `gui/solve_cli.bend` parses the sketch file and prints the answer.
  - `gui/serve.py` writes the file and runs the binary.
  - The page builds the sketch: every variable is sent, merges such as
    coincident or horizontal are equations like any other (D3 as revised,
    Q29), starting from a drawing where they hold, and a fixed point
    becomes two `Fix` records.
  - Three settings change only the drawing or the variable order:
    - *Relax the drawing first*: a least-squares pass that moves the
      drawing as little as it can toward the constraints.
    - *Choose the variable order*: the solver's pins are the earliest
      variables, so the page orders the variables to leave a
      well-conditioned set to solve for.
    - *Dimensions as dyadics*: below.

## What the list says

Each constraint is numbered, and after a solve it says what the solver
made of it:

- **conflicts with #a, #b** (red): it cannot hold together with those,
  its support. Without any one of them the solver finds no conflict
  (degree 0 or by directions; the rest may still be impossible for a
  reason it does not look for, lengths for example). On a refusal it reads **cannot all hold with #a, #b**; with no support
  at all, **cannot hold** (a negative length, for example). The solver
  leaves it out and certifies the rest. A segment always has nonzero
  length, so a constraint that would make one a point is a conflict too
  (a Coincident on a segment's two ends, or a Horizontal and a Vertical on
  the same segment).
- **over-determined** (red): with the earlier constraints named it fixes
  more than the variables it uses can carry.
- **redundant** (amber): every equation follows from earlier constraints
  and every side condition is implied, so the solver drops it, and when
  the sketch certifies it **holds anyway**. An exact repeat is redundant.
- **partly implied by earlier ones**: kept, with some of its equations
  dropped because earlier constraints give them.

Hover a constraint for the longer reading: for a dropped equation, the
constraints it follows from, and whether it follows by directions.

An Angle is sent as its rotation rounded to a dyadic, so angles that close
a cycle exactly in degrees (a triangle's three angles, or 60, 60 and 240)
need not close as sent. The last one is then honestly red, and the page
says the angle's rotation was rounded. Multiples of 90 degrees are sent
exactly.

Red constraints are drawn red, redundant ones amber; points drawn hollow
have a coordinate the solver held at its drawn value.

## Two limits of the v1 solver this makes visible

Both are in solve_complete's hypotheses and stated in DESIGN.md.

- **Constants must be dyadic (Q19).** The certifying arithmetic holds only
  rationals with a power-of-two denominator, so a dimension of 3.6, or an
  angle other than a multiple of 90 degrees, never certifies exactly. With
  *Dimensions as dyadics* on (the default), the page sends the nearest
  multiple of 2^-40. An angle's rotation (c, s) need not be a unit vector:
  the constraint fixes the direction, so the angle certified is atan2(s, c).
  Each value is rounded on its own, so values that agree exactly in
  decimals need not agree as sent: horizontal distances 0.1, 0.1 and 0.2
  along a line come back as a conflict, and the page says a dimension was
  rounded.
- **The pins are chosen structurally.** v1 holds the free variables at
  their drawn values, choosing which ones by structure and variable order,
  not by conditioning. A horizontal segment with a length is singular if x
  is held and y solved. *Choose the variable order* avoids most such
  cases, and *Relax the drawing first* brings the drawing near a solution,
  which is where the solver is complete. Turn both off to see the raw
  behavior.

Redundancy and conflicts are found exactly for consequences that are
constant combinations of the equations (degree 0), and since sk-13b for
those among directions (Parallel, Perpendicular, an Angle with a constant
rotation, OnLine, and the horizontals and verticals they reach). A
direction made vertical twice through a chain of perpendiculars and
parallels (proto/sketches: vertical-twice) is now amber. Since Q15's
revision (2026-11-02) a segment has nonzero length, so a constraint that
would collapse one is red, in either order (proto/sketches: par-collapse,
collapse-par).

## Files

| file | what |
|---|---|
| `solve_cli.bend` | the solver as a command: reads `sketch.in`, prints the answer |
| `serve.py` | the local server (stdlib only) |
| `index.html`, `ui.js` | the page |
| `model.js` | the sketch model, merges, building the solver's input |
| `relax.js` | the relaxation and the variable order |
| `pipeline.js` | relax, order, solve, read back; the example sketch |
