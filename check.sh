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
# the demos in tests/ must keep checking too. Each stays its own root (a
# check reports reliance on unsafe or foreign code only for the root's own
# defs), checked side by side: at most BEND_JOBS at once (default: one per
# core), the verdicts read back in order.
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
jobs_max="${BEND_JOBS:-$(nproc)}"
for t in tests/*.bend; do
  [ -e "$t" ] || continue
  while [ "$(jobs -rp | wc -l)" -ge "$jobs_max" ]; do wait -n; done
  b="$(basename "$t")"
  ( bin/bend "$t" --check-only > "$tmp/$b.out" 2>&1; echo $? > "$tmp/$b.code" ) &
done
wait
for t in tests/*.bend; do
  [ -e "$t" ] || continue
  b="$(basename "$t")"
  tout="$(cat "$tmp/$b.out")"; tcode="$(cat "$tmp/$b.code")"
  if [ "$tcode" -ne 0 ] || ! printf '%s\n' "$tout" | command grep -qx "All terms check."; then
    printf '%s\n' "$tout"
    echo "GATE: FAIL ($t)"; exit 1
  fi
  if printf '%s\n' "$tout" | command grep -q "unsafe or foreign"; then
    echo "GATE: FAIL ($t relies on unsafe or foreign code)"; exit 1
  fi
done
# drafts in ROADMAP.bend must match their gated restatements in tests/
if ! python3 tools/lawsync.py >/dev/null; then
  python3 tools/lawsync.py
  echo "GATE: FAIL (a ROADMAP.bend draft and its restatement in tests/ differ)"; exit 1
fi
# open law statements in ROADMAP.bend must type-check
if ! python3 tools/stmtcheck.py >/dev/null; then
  python3 tools/stmtcheck.py
  echo "GATE: FAIL (an open statement in ROADMAP.bend does not type-check)"; exit 1
fi
echo "GATE: PASS"
