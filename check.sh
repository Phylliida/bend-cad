#!/usr/bin/env bash
# The gate: PROOF.bend must check with every law proven and nothing relying on
# @unsafe or foreign code. Open (roadmap) laws live in ROADMAP.bend, which
# PROOF.bend does not import.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
out="$(bin/bend PROOF.bend --check-only 2>&1)"; code=$?
printf '%s\n' "$out"
if [ $code -ne 0 ]; then
  echo "GATE: FAIL (bend exited $code)"; exit 1
fi
if printf '%s\n' "$out" | command grep -q "unsafe or foreign"; then
  echo "GATE: FAIL (relies on unsafe or foreign code)"; exit 1
fi
if ! printf '%s\n' "$out" | command grep -qx "All terms check."; then
  echo "GATE: FAIL (no clean verdict)"; exit 1
fi
# the demos in tests/ must keep checking too
for t in tests/*.bend; do
  [ -e "$t" ] || continue
  tout="$(bin/bend "$t" --check-only 2>&1)"; tcode=$?
  if [ $tcode -ne 0 ] || ! printf '%s\n' "$tout" | command grep -qx "All terms check."; then
    printf '%s\n' "$tout"
    echo "GATE: FAIL ($t)"; exit 1
  fi
  if printf '%s\n' "$tout" | command grep -q "unsafe or foreign"; then
    echo "GATE: FAIL ($t relies on unsafe or foreign code)"; exit 1
  fi
done
echo "GATE: PASS"
