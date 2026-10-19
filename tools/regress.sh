#!/usr/bin/env bash
# Native regression for the solver (not in the gate: about 2 min, most of it
# the slowest GUI sketch; builds and sketches run in parallel):
# - proto/solve_run.bend's answers must match proto/solve_run.expected;
# - proto/skel_cmp.bend's two structures of each kept system must agree;
# - gui/solve_cli.bend, built from this tree, must answer each GUI sketch
#   in proto/sketches/ as proto/sketches/expected says, within its limit.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fail() { echo "REGRESS: FAIL${1:+ ($1)}"; exit 1; }

for p in proto/solve_run proto/skel_cmp gui/solve_cli; do
  b="$(basename "$p")"
  bin/bend "$p.bend" -o "$tmp/$b" > "$tmp/$b.build" 2>&1 &
done
wait
for b in solve_run skel_cmp solve_cli; do
  [ -x "$tmp/$b" ] || { cat "$tmp/$b.build"; fail "build $b"; }
done

# the GUI sketches, in the background while the other two run (the loop
# reads a process substitution, not a pipe, so it runs in this shell and
# wait below waits for its jobs)
mkdir -p "$tmp/sk"
while read -r name limit want; do
  d="$tmp/sk/$name"; mkdir -p "$d"; cp "proto/sketches/$name.in" "$d/sketch.in"
  ( cd "$d" && s=$(date +%s%N)
    timeout "$limit" "$tmp/solve_cli" --threads 1 > out 2>&1; echo $? > code
    echo $(( ($(date +%s%N) - s) / 1000000 )) > ms ) &
done < <(command grep -v '^#' proto/sketches/expected)

ok=1
if ! "$tmp/solve_run" --threads 1 | diff -u proto/solve_run.expected - ; then ok=0; fi
if ! "$tmp/skel_cmp" --threads 1 | python3 -c '
import sys
blocks = sys.stdin.read().split("== ")[1:]
bad = [b.split("\n")[0] for b in blocks if b.split("\n", 1)[1].split("-- kept\n")[0].strip() != b.split("-- kept\n")[1].strip()]
print("structures differ: " + ", ".join(bad) if bad else "structures agree (%d sketches)" % len(blocks))
sys.exit(1 if bad or not blocks else 0)'; then ok=0; fi

wait
while read -r name limit want; do
  d="$tmp/sk/$name"
  code="$(cat "$d/code" 2>/dev/null || echo none)"
  got="$(head -3 "$d/out" | paste -sd ';' | sed 's/;/; /g')"
  t="$(awk -v m="$(cat "$d/ms" 2>/dev/null || echo 0)" 'BEGIN{printf "%.1f", m/1000}')"
  if [ "$code" = 124 ]; then
    echo "sketch $name: over its ${limit} s limit"; echo bad >> "$tmp/sk/bad"
  elif [ "$code" != 0 ] || [ "$got" != "$want" ]; then
    echo "sketch $name: got \"$got\" (exit $code), want \"$want\""; echo bad >> "$tmp/sk/bad"
  else
    printf 'sketch %-20s %6s s  %s\n' "$name" "$t" "$got"
  fi
done < <(command grep -v '^#' proto/sketches/expected)
[ -e "$tmp/sk/bad" ] && ok=0
[ "$ok" = 1 ] || fail
echo "REGRESS: PASS"
