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
