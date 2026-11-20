#!/usr/bin/env bash
# pragma-gate.sh — the structured-recursion gate (D242), until the whole
# compiler builds with --safe.
#
# Once has structured recursion only (OCP-0003). Agda enforces that for us —
# termination and strict positivity — unless a pragma switches the check off.
# This gate fails if any module in the import closure of the apex
# (Once/Certified.agda) or of the extracted compiler (Once/Extract/Root.agda)
# carries a pragma that disables termination, positivity, coverage or universe
# checking. Zero tolerance: there is no baseline (plan 0.153 removed the last
# residuals). Agda itself cannot do this short of --safe: such a pragma turns the
# check off silently (no warning for `-W error` to promote), and --safe also
# forbids every postulate, which the trust base still has.
#
# The pattern matches pragma text inside a comment too, so write the bare word
# in prose ("TERMINATING", "the termination pragma"); that keeps counts honest
# (the rule lint-pragmas.sh used to enforce).
#
# Usage (from formal/):  scripts/pragma-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

roots=(Once/Certified.agda Once/Extract/Root.agda)
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

bad=0
for f in "${!seen[@]}"; do
  if grep -nE "$P" "$f" | sed "s|^|$f:|"; then
    bad=1
  fi
done
echo "pragma-gate: ${#seen[@]} modules in the closure of ${roots[*]}"
if ((bad)); then
  echo "pragma-gate: FAIL — a check-disabling pragma in the certified/compiler closure (D242)"
  exit 1
fi
echo "pragma-gate: OK (no check-disabling pragma)"
