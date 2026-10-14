#!/usr/bin/env bash
# Cross-check bend-cad's field axioms against mathlib's ℝ (DESIGN §8.4, Q18):
# build lean/BendCad/Axioms.lean (ℝ satisfies every axiom; ℚ is not
# complete), print the axioms the results rest on, and compare the Lean
# transcription with the Bend spec mechanically (tools/axcheck.py).
# Uses the elan release toolchain (a Nix lake would rebuild mathlib).
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH"
case "$(command -v lake)" in
  "$HOME"/.elan/*) ;;
  *) echo "lake is not the elan toolchain's: $(command -v lake)"; exit 1 ;;
esac
lake build 2>&1 | tail -1
tmp=$(mktemp -d)
printf 'import BendCad.Axioms\n#print axioms BendCad.axioms_consistent\n#print axioms BendCad.rat_not_complete\n' > "$tmp/ax.lean"
out=$(lake env lean "$tmp/ax.lean")
rm -rf "$tmp"
echo "$out"
if echo "$out" | grep -q sorryAx; then echo "LEAN: uses sorry"; exit 1; fi
cd ..
python3 tools/axcheck.py | tail -1
echo "LEAN CROSS-CHECK: PASS"
