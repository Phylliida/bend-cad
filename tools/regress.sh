#!/usr/bin/env bash
# Native regression for the solver (not in the gate: ~40 s to build and
# run): proto/solve_run.bend's answers must match proto/solve_run.expected,
# and proto/skel_cmp.bend's two structures of each kept system must agree.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
out="${TMPDIR:-/tmp}/bend-cad-solve-run.$$"
bin/bend proto/solve_run.bend -o "$out" >/dev/null 2>&1 || { echo "REGRESS: FAIL (build)"; exit 1; }
if ! "$out" --threads 1 | diff -u proto/solve_run.expected - ; then
  echo "REGRESS: FAIL"; rm -f "$out"; exit 1
fi
bin/bend proto/skel_cmp.bend -o "$out" >/dev/null 2>&1 || { echo "REGRESS: FAIL (build skel_cmp)"; rm -f "$out"; exit 1; }
if ! "$out" --threads 1 | python3 -c '
import sys
blocks = sys.stdin.read().split("== ")[1:]
bad = [b.split("\n")[0] for b in blocks if b.split("\n", 1)[1].split("-- kept\n")[0].strip() != b.split("-- kept\n")[1].strip()]
print("structures differ: " + ", ".join(bad) if bad else "structures agree (%d sketches)" % len(blocks))
sys.exit(1 if bad or not blocks else 0)'; then
  echo "REGRESS: FAIL"; rm -f "$out"; exit 1
fi
rm -f "$out"
echo "REGRESS: PASS"
