#!/usr/bin/env bash
# Regenerates each sketch's solver input from its GUI export, as
# gui/pipeline.js's prepare makes it (relaxed, ordered, dyadic): NAME.in
# with exact repeats left out (the page's request before PLAN-sk13a S8),
# NAME.raw.in with them, the page's request now (written only when it
# differs). Needs bun (BUN=..., or the newest in the nix store).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
root=../..
bun="${BUN:-$(ls -d /nix/store/*-bun-[0-9]*/bin/bun | sort -V | tail -1)}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
for j in *.json; do
  n="${j%.json}"
  "$bun" "$root/tools/diag/replay.mjs" "$j" "$tmp/req.json" > /dev/null
  python3 "$root/tools/diag/totext.py" "$tmp/req.json" > "$n.in"
  "$bun" "$root/tools/diag/replay.mjs" "$j" "$tmp/raw.json" --repeats > /dev/null
  python3 "$root/tools/diag/totext.py" "$tmp/raw.json" > "$tmp/raw.in"
  if cmp -s "$n.in" "$tmp/raw.in"; then rm -f "$n.raw.in"; else cp "$tmp/raw.in" "$n.raw.in"; fi
done
