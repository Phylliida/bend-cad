# Diagnosing a sketch the solver is slow on or refuses (untrusted tools)

Built 2026-10-18 while finding why GUI sketches were slow. Two causes were
found: zeros whose exponents compounded (fixed in `dsig`), and dependent
constraints that the structural red stage cannot see (DESIGN §8.11). None
of these tools is in the gate; they only read the solver's behaviour.

`BUN` below is bun from the nix store (`ls -d /nix/store/*-bun-1.3.11/bin/bun`).

## 1. Replay what the page sends

```
$BUN tools/diag/replay.mjs sketch.json req.json      # relax, order, dyadics
python3 tools/diag/totext.py req.json > sketch.in    # solve_cli's input
```

`replay.mjs` runs `gui/pipeline.js`'s `prepare` with the page's defaults.
`totext.py` is `gui/serve.py`'s `sketch_text`. Then time the real solver:

```
(cd dir_with_sketch.in && time /path/to/bend-cad/gui/solve_cli --threads 1)
```

## 2. Which stage is slow: `proto/probe_stage.bend`

Build it once: `bin/bend proto/probe_stage.bend -o proto/probe_stage`
(about 20 s). It reads `./sketch.in` and `./stage.in` = `"k p"`. Write
`stage.in` with `printf`, not `echo`: a trailing newline makes the last
number unreadable, and it is then read as 0.

| k | prints |
|---|---|
| 0 | red constraints |
| 1 | pins |
| 2 | the structure: pins count, then each block as eqs x vars / params |
| 3 | the plan at precision p: POk, PRetry or PStop |
| 4 | the plan and the whole verdict at precision p |
| 5 | the whole solve |

Native stdout is buffered, so time each stage as its own run. Runs are
independent; run them in parallel. Rebuild the probe after any change in
lib/: a stale probe gives stale timings.

## 3. Which block, and why: `proto/probe_block.bend`

Build: `bin/bend proto/probe_block.bend -o proto/probe_block`. It reads
`./sketch.in` and `./stage.in` = `"k p j"`, for block j (in plan order)
at precision p. The parameters take their drawn values.

| k | prints |
|---|---|
| 0 | the block's size, offset, parameters and equation sizes |
| 1 | Newton: settled at step n, singular, or not settled |
| 2 | whether the Jacobian at the drawing has an inverse |
| 3 | the block's outcome: BOk, BRetry or BStop |
| 4 | J at Newton's end (or the drawing), one `row` of dyadics per line |
| 5 | each equation's owning constraint position, then the block's variables and parameters |

## 4. Name the dependency: exact null spaces

```
$BUN tools/diag/owners.mjs sketch.json > owners.json   # position -> GUI constraint
# stage 5 of block j -> block_owners.txt; stage 4 -> block_jac.txt
python3 tools/diag/nullspace.py owners.json block_owners.txt block_jac.txt
```

This prints the rank, each left null vector (which constraints depend on
each other) and each right null vector (what is left free). For the GUI's
`sketch(4).json`, block 7 (19×19) has rank 18. The dependency is #25
`perpendicular seg27 seg6`, #27 `parallel seg28 seg27` and #38
`parallel seg35 seg28`, with seg 35 vertical by a merge: seg 28 is made
vertical twice. Removing any one of the three makes the sketch certify.
