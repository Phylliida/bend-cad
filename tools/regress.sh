#!/usr/bin/env bash
# Native regression for the solver (not in the gate: ~30 s to build and
# run): proto/solve_run.bend's answers must match proto/solve_run.expected.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
out="${TMPDIR:-/tmp}/bend-cad-solve-run.$$"
bin/bend proto/solve_run.bend -o "$out" >/dev/null 2>&1 || { echo "REGRESS: FAIL (build)"; exit 1; }
if "$out" --threads 1 | diff -u proto/solve_run.expected - ; then
  echo "REGRESS: PASS"
else
  echo "REGRESS: FAIL"; rm -f "$out"; exit 1
fi
rm -f "$out"
