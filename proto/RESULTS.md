# sk-P1 results (prototype spike, untrusted code)

Measurements from `proto/`. Native = `bin/bend file.bend -o out`, run with
`--threads 1` on this machine; JS = `bin/bend file.bend` (includes ~1 s of
checking).

## Depth-30 circle chain (`chain.bend`, `gen_chain_run.py`)

Each step is one block (unknown P_k, parameters P_{k−2}, P_{k−1} within their
certified balls), certified exactly with the parametric contraction test of
DESIGN §8.3 at working precision P (scale 2^−P nm). Points at 50 mm spacing;
coordinates up to ~0.75 m, beyond F32's integer range at 1 nm.

| chain | true sensitivity (Python) | certified radius growth | smallest P reaching < 1 nm at depth 30 |
|---|---|---|---|
| well (near-equilateral strip) | 1.28 bits/step (38 bits total) | ~1.3 bits/step (39 bits) | 64 (radius 2^−25 nm) |
| flat (height 0.08·L, ill-conditioned) | 3.82 bits/step (115 bits total) | ~4.0 bits/step (119 bits) | 128 (radius 2^−9 nm) |

- Precision cost is **additive in depth**, and with the bound written as
  ‖Y·J_z‖·ρ (the actual sensitivity matrix) the certificate tracks the true
  sensitivity with essentially no slack. A cruder ‖Y‖·‖J_z‖·ρ bound plus a 2×
  radius safety factor cost an extra ~1–1.5 bits per step.
- Failure mode below the needed P: the contraction test fails (q ≥ 1) once the
  propagated radius approaches the geometric scale, at the step where it
  happens (e.g. flat chain, P = 96: fails at step 30).
- **Cost:** both chains certified (well at P = 96, flat at P = 192) in
  **0.16 s native, single thread**; 2.1 s on the JS lane.
- F32 initial guess + simplified Newton with an F32-built Y, residuals exact,
  converged in every block (each 2×2 block is locally well conditioned; the
  ill-conditioning is across blocks).

## One large cyclic block (`block.bend`, `gen_block.py`, `block_run.bend`)

A random Henneberg-II (edge-split) Laman framework: rigid, triangle-free, so
it cannot be solved triangle by triangle; one square block of m = 2n − 3
unknowns, pinned P0 and P1.y. **Shortcut:** x̃ (float64 Newton) and Y (an
F32-quality inverse: float32 Gauss–Jordan emulated exactly in Python) come from
Python; Bend loads them from text files, refines x̃ by simplified Newton in
exact arithmetic and checks the certificate exactly at P = 96. The exact work
is O(m²) bigint operations because J has ≤ 4 nonzeros per row.

Scaling (well-shaped frameworks, native, 1 thread):

| m (unknowns) | κ∞ | F32 ‖I − Y·J‖ | certified radius | time |
|---|---|---|---|---|
| 21 | 313 | 2^−17 | 2^−94 nm | 0.06 s |
| 47 | 714 | 2^−15 | 2^−94 nm | 0.28 s |
| 97 | 4.7e3 | 2^−12 | 2^−94 nm | 1.26 s |
| 197 | 5.6e3 | 2^−11 | 2^−94 nm | 5.24 s |

Breakdown at m = 197: parsing 0.22 s, certificate ~1.8 s, 10 exact Newton
steps ~3.3 s. With no exact Newton steps the float64 x̃ already certifies at
2^−19 nm (below the 1 nm grid): full-precision refinement is only needed when
later blocks need tiny parameter radii (chains).

Conditioning sweep (n = 25, framework flattened; drawing noise scaled with it):

| flatten | κ∞ | F32 ‖I − Y·J‖ | result |
|---|---|---|---|
| 0.1 | 4.3e3 | 2^−12 | certified |
| 0.01 | 8.5e4 | 2^−8 | certified |
| 0.001 | 5.4e5 | 2^−6 | certified |
| 0.0003 | 9.2e5 | 2^−4 | certified |
| 0.0001 | 2.4e9 | 74 | **fails** (Y unusable; Newton diverges, 43 s wasted) |

## Conclusions (go / no-go)

1. **Precision vs depth: GO.** Additive in depth and tight against the true
   sensitivity.
2. **Certification cost: GO, with headroom to win.** Chains: milliseconds per
   block. A 197-unknown cyclic block: ~2 s for the certificate in this
   list-of-limbs prototype; typical blocks (≤ 20 unknowns) are milliseconds.
   Headroom: limb representation, a block-floating Y (it only needs ~30
   significant bits but is carried at full scale), skipping refinement for
   standalone blocks.
3. **F32 preconditioner: GO up to κ ≈ 10^6, fallback needed beyond.** Matches
   κ·2^−24 < 1. Needed: a higher-precision approximate inverse for κ ≳ 10^7
   (dyadic elimination, which needs bigint reciprocal/division, or double-F32),
   and **check ‖I − Y·J‖ before refining** so a bad Y fails fast.
4. **Bend compiler limit:** large data literals fail natively ("arity over
   255", stack overflow), so data is loaded at runtime from files (sketches
   are loaded anyway).
5. **Tooling:** `bin/bend` disables the version-check request, and picks a nix
   clang wrapper when `CC` is unset or not clang (here `CC=gcc`, which Bend
   rejects; the system clang lacks libc headers).

## Not done yet in sk-P1

- The ink-metric proposer, pinning and block decomposition in Bend (the
  cyclic-block x̃ and Y came from Python).
- An F32 Gauss–Jordan in Bend (emulated in Python here).
