# HANDOFF — bend-cad (2026-10-13)

Read first: `DESIGN.md` (v0.4, the plan and Danielle's decisions),
`proto/RESULTS.md` (sk-P1 spike results). Bend gotchas are in memory
(`reference_bend2_idioms`).

## State

- **sk-00 done:** `bin/bend` (runs `../bend` under bun, telemetry off, fixes
  CC), `check.sh` (gate; negative-tested), `LAWS.bend` / `PROOF.bend` /
  `ROADMAP.bend` (empty law set, gate green).
- **sk-P1 risk questions answered** (untrusted code in `proto/`): precision is
  additive in depth and tight; certification is fast for chains and ~2 s for a
  197-unknown cyclic block; the F32 preconditioner works to κ ≈ 10^6 and needs
  a higher-precision fallback beyond. Still open in sk-P1 (deferred to sk-09):
  ink-metric proposer, pinning, decomposition, F32 Gauss–Jordan in Bend.
- **Nothing is verified yet.** `proto/` is a throwaway prototype.

## sk-01 progress (2026-10-13, later)

Done and gated (`./check.sh` green, also checks `tests/*.bend`):
- `spec/num.bend`: Coq-shaped `Pos` (XH/XO/XI) and `Z` (Z0/Zpos/Zneg) — Danielle
  approved the Coq shape — with unary meaning `Pos.nat`, `Pos.of_succ`,
  `Z.of_diff(a, b)` (= a − b), `Z.pnat`/`Z.nnat`.
- `spec/ring.bend`: `ZExpr` + `eval` (trusted meaning of ring expressions).
- `lib/nat.bend` (Nat semiring), `lib/natring.bend` (bootstrap Nat normalizer,
  unary coefficients, `NDbl`), `lib/pos.bend` (Pos.nat hom + injective),
  `lib/z.bend` (of_diff is a ring hom), `lib/zpair.bend` (Z tactic via pairs),
  `lib/zlaws.bend` (15 Z ring laws, one call each), `lib/zring.bend` (the
  binary-coefficient Z normalizer, `ring_eq`).
- `LAWS.bend` (draft, awaiting Danielle's review): Pos/Z meaning, ring laws,
  `ring_eq`. Exit criterion met: `(a+b)^2` etc. in one call
  (`tests/zring_demo.bend`, incl. 2^128 constants); (a+b+c+d)^7 ≈ 0.9 s.

Idioms learned: lemmas stated `{target == source}` (a rewrite replaces the
marked source occurrences); `ring_eq(...)` can itself be a `%` rewrite;
generated case proofs (scratch scripts) are fine, Bend checks the output.

Next in sk-01: Z order (Pos/Z compare), spec rationals as *unnormalized*
pairs with `Q.eq` (cross-multiplication; gcd normalization is a runtime
optimization proven to preserve Q.eq) — recorded as a DESIGN v0.5 decision,
flagged to Danielle — a Q tactic via (num, den) translation to `ring_eq`,
dyadics (m, e) meaning m/2^e, binary N.

## Next: sk-01 — spec numbers + reflective ring normalizer

Exit criterion (DESIGN §15): normalizer soundness law closed; an identity like
(a+b)² = a² + 2ab + b² proven in one rewrite.

Plan:
1. **Binary spec numbers** (Danielle approved binary, Q8). Bend's checker does
   Peano `Nat` in unary, so constants must be small terms. Coq-style:
   positives `1 | 2p | 2p+1`, `N = 0 | pos`, integers `0 | +pos | −pos`
   (canonical zero). DESIGN §3 says "`ofNat n | negSucc n`"; with binary
   positives the Coq `Z0 | Zpos | Zneg` shape is the natural canonical form.
   Confirm with Danielle, it's a spec-level choice.
   - Constructor names are global across all modules: prefix them.
   - Coq's `Pos.add` / `Pos.add_carry` are mutually recursive; Bend forbids
     that, so use one def with a carry `Bool`.
2. **Ring laws** on the binary integers (comm, assoc, distrib, identities,
   negation), by induction on positives. Bend has no tactics: proofs are
   `match` + recursive calls + `%e : P` rewrites + `{==}`. Study
   `../bend/demos/proof_numerics`, `proof_insertion_sort`, `proof_typed_eval`.
3. **Reflective normalizer:** `Expr` AST (var, const, add, mul, neg),
   `eval(env, e)`, normalize to a sorted sparse polynomial (monomial = coef +
   variable multiset), `law norm_sound: eval(env, e) == evalPoly(env, norm(e))`.
   Usage: `norm(e1) == norm(e2)` by `{==}` (computed on concrete syntax), then
   rewrite through `norm_sound` twice.
4. Watch checker speed on the reflective `{==}` (the main sk-01 risk).

Laws go in `LAWS.bend` (human-owned: Danielle reviews), proofs in `PROOF.bend`,
not-yet-proven laws in `ROADMAP.bend`. Commit freely in `bend-cad/`.
