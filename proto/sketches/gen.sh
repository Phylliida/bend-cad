#!/usr/bin/env bash
# Regenerates each sketch's solver input from its GUI export: NAME.in is what
# the page sends (gui/pipeline.js's prepare: relaxed, ordered, dyadic),
# NAME.raw.in the same with the repeats the page leaves out (written only
# when it differs). Needs bun (BUN=..., or the newest in the nix store).
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
