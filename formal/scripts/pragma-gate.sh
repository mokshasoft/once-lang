#!/usr/bin/env bash
# pragma-gate.sh — the structured-recursion gate (D242), until the whole
# compiler builds with --safe.
#
# Once has structured recursion only (OCP-0003). Agda enforces that for us —
# termination and strict positivity — unless a pragma switches the check off.
# This gate fails if any module in the import closure of the apex
# (Once/Certified.agda) or of the extracted compiler (Once/Compiler.agda)
# carries a pragma that disables termination, positivity, coverage or universe
# checking.
#
# Usage (from formal/):  scripts/pragma-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

roots=(Once/Certified.agda Once/Compiler.agda)
# The pragma names are assembled so this script does not itself contain them.
P='{-#[[:space:]]*('"TERMIN"'ATING|NON_'"TERMIN"'ATING|NO_POSITIVITY_'"CHECK"'|NON_'"COVER"'ING|NO_UNIVERSE_'"CHECK"')'

declare -A seen=()
queue=("${roots[@]}")
while ((${#queue[@]})); do
  f=${queue[0]}; queue=("${queue[@]:1}")
  [[ -n ${seen[$f]:-} ]] && continue
  seen[$f]=1
  while read -r m; do
    g="${m//.//}.agda"
    [[ -f $g && -z ${seen[$g]:-} ]] && queue+=("$g")
  done < <(grep -oE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Once(\.[^[:space:]()]+)+' "$f" \
             | grep -oE 'Once(\.[^[:space:]()]+)+')
done

# The baseline: residuals that predate the gate. Each line is `path count`.
# A module may only DROP below its count (then lower or delete its line);
# anything not listed must carry none.
baseline=scripts/pragma-gate.baseline
declare -A allowed=()
while read -r path count; do
  [[ -z $path || $path == \#* ]] && continue
  allowed[$path]=$count
done < "$baseline"

bad=0
for f in "${!seen[@]}"; do
  n=$(grep -cE "$P" "$f" || true)
  a=${allowed[$f]:-0}
  if ((n > a)); then
    grep -nE "$P" "$f" | sed "s|^|$f:|"
    echo "pragma-gate: $f has $n, baseline allows $a"
    bad=1
  elif ((n < a)); then
    echo "pragma-gate: $f is down to $n (baseline $a) — lower its line in $baseline"
  fi
done
echo "pragma-gate: ${#seen[@]} modules in the closure of ${roots[*]}"
if ((bad)); then
  echo "pragma-gate: FAIL — a new check-disabling pragma in the certified/compiler closure (D242)"
  exit 1
fi
echo "pragma-gate: OK (baseline residuals: ${#allowed[@]} modules)"
