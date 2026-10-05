#!/usr/bin/env bash
# public-gate.sh — the re-export ratchet (plan 0.92 S0).
#
# A `public` re-export scopes its names against every local import in the
# importer's cone; the cost lands on modules the author never looked at (plan
# 0.92 §1). This gate freezes the surface: a module may only LOWER its count of
# `public` lines below the baseline (then lower or delete its line there), and
# a module not listed must carry none. Re-exporting is kept only where it
# avoids re-instantiating a parameterised module, with a measurement (§2, S4).
#
# Usage (from formal/):  scripts/public-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

P='(^|[[:space:]])public[[:space:]]*$'
baseline=scripts/public-gate.baseline
declare -A allowed=()
while read -r path count; do
  [[ -z $path || $path == \#* ]] && continue
  allowed[$path]=$count
done < "$baseline"

bad=0; total=0
while IFS= read -r f; do
  n=$(grep -cE "$P" "$f" || true)
  total=$((total + n))
  a=${allowed[$f]:-0}
  if ((n > a)); then
    grep -nE "$P" "$f" | sed "s|^|$f:|"
    echo "public-gate: $f has $n, baseline allows $a"
    bad=1
  elif ((n < a)); then
    echo "public-gate: $f is down to $n (baseline $a) — lower its line in $baseline"
  fi
done < <(find Once -name '*.agda' | LC_ALL=C sort)
echo "public-gate: $total public re-export lines (baseline modules: ${#allowed[@]})"
if ((bad)); then
  echo "public-gate: FAIL — a new public re-export (plan 0.92 §2)"
  exit 1
fi
echo "public-gate: OK"
