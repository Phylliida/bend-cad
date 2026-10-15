# bend-cad sketcher (GUI)

A page for trying the verified solver by hand: draw points, lines and
circles, constrain and dimension them, and see what the solver certifies.

```
python3 gui/serve.py            # then open http://localhost:8480/
python3 gui/serve.py 9000       # another port
```

The first start builds the solver binary `gui/solve_cli` from
`gui/solve_cli.bend` with `bin/bend` (about 20 s); it rebuilds when the
`.bend` file is newer.

## What runs where

- **Verified:** `SO.solve` (lib/solve.bend) answers every request: the
  verdict, the red constraints, the pins, and the certified box. Its laws
  (solve_exists, solve_unique, solve_red, solve_pins, solve_total) hold for
  whatever it is given.
- **Untrusted, and only shaping the input:**
  - `gui/solve_cli.bend` parses the sketch file and prints the answer.
  - `gui/serve.py` writes the file and runs the binary.
  - The page builds the sketch: merges such as coincident or horizontal
    become shared variables, as the solver expects (D3), and a fixed
    point becomes two `Fix` records.
  - Three settings change only the drawing or the variable order:
    - *Relax the drawing first*: a least-squares pass that moves the
      drawing as little as it can toward the constraints.
    - *Choose the variable order*: the solver's pins are the earliest
      variables, so the page orders the variables to leave a
      well-conditioned set to solve for.
    - *Dimensions as dyadics*: below.

## Two limits of the v1 solver this makes visible

Both are already stated in DESIGN.md and in solve_complete's hypotheses.

- **Constants must be dyadic (Q19).** The certifying arithmetic holds only
  rationals with a power-of-two denominator, so a dimension of 3.6, or an
  angle other than a multiple of 90 degrees, never certifies exactly. With
  *Dimensions as dyadics* on (the default), the page sends the nearest
  multiple of 2^-40. An angle's rotation (c, s) need not be a unit vector:
  the constraint fixes the direction, so the angle certified is atan2(s, c).
- **The pins are chosen structurally.** v1 holds the free variables at
  their drawn values, choosing which ones by structure and variable order,
  not by conditioning. A horizontal segment with a length is singular if x
  is held and y solved. *Choose the variable order* avoids most such
  cases, and *Relax the drawing first* brings the drawing near a solution,
  which is where the solver is complete. Turn both off to see the raw
  behavior.

Points drawn hollow have a coordinate the solver held at its drawn value.
Red constraints are listed in red and drawn red.

## Files

| file | what |
|---|---|
| `solve_cli.bend` | the solver as a command: reads `sketch.in`, prints the answer |
| `serve.py` | the local server (stdlib only) |
| `index.html`, `ui.js` | the page |
| `model.js` | the sketch model, merges, building the solver's input |
| `relax.js` | the relaxation and the variable order |
| `pipeline.js` | relax, order, solve, read back; the example sketch |
