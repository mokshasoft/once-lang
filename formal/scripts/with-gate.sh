#!/usr/bin/env bash
# with-gate.sh — the checking-cost gate (plan 0.156): no new `with`/`rewrite`.
#
# A `with` abstracts the goal over its scrutinee; over the linear core's large
# goals that costs gigabytes and minutes per module (LowerSim, 2026-11-20: an
# OOM above 2.7 GB, 57 s / 1.4 GB once its `with`s became `case … of λ where`
# and typed continuations). `rewrite` is a `with` in disguise. A slow module
# slows every check of everything above it, so the count is a ratchet.
#
# This gate counts `with`/`rewrite` clauses (outside `--` comments) in every
# module in the import closure of the apex (Once/Certified.agda) and of the
# extracted compiler (Once/Extract/Root.agda). A module may only DROP below its
# baseline count (then lower or delete its line); a module not listed carries
# none. Write `case e of λ where …` (Function.case_of_) or a continuation of
# explicit type instead.
#
# Usage (from formal/):  scripts/with-gate.sh            check
#                        scripts/with-gate.sh --baseline  print a fresh baseline
set -euo pipefail
cd "$(dirname "$0")/.."

roots=(Once/Certified.agda Once/Extract/Root.agda)
W='(^|[[:space:](])(with|rewrite)([[:space:]]|$)'

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

count() { sed 's/--.*//' "$1" | grep -cE "$W" || true; }

if [[ ${1:-} == --baseline ]]; then
  echo "# with-gate baseline (plan 0.156): with/rewrite clauses per module in the closure of"
  echo "# Once/Certified.agda + Once/Extract/Root.agda. Counts may only go DOWN; the plan empties it."
  for f in "${!seen[@]}"; do
    n=$(count "$f")
    if ((n > 0)); then echo "$f $n"; fi
  done | sort
  exit 0
fi

baseline=scripts/with-gate.baseline
declare -A allowed=()
while read -r path n; do
  [[ -z $path || $path == \#* ]] && continue
  allowed[$path]=$n
done < "$baseline"

bad=0; total=0; down=0
for f in "${!seen[@]}"; do
  n=$(count "$f")
  total=$((total + n))
  a=${allowed[$f]:-0}
  if ((n > a)); then
    sed 's/--.*//' "$f" | grep -nE "$W" | sed "s|^|$f:|"
    echo "with-gate: $f has $n, baseline allows $a"
    bad=1
  elif ((n < a)); then
    echo "with-gate: $f is down to $n (baseline $a) — lower its line in $baseline"
    down=1
  fi
done
echo "with-gate: ${#seen[@]} modules, $total with/rewrite clauses (baseline modules: ${#allowed[@]})"
if ((bad)); then
  echo "with-gate: FAIL — a new with/rewrite (plan 0.156): use case … of λ where, or a typed continuation"
  exit 1
fi
if ((down)); then echo "with-gate: OK, and the baseline can be lowered (scripts/with-gate.sh --baseline)"; fi
echo "with-gate: OK"
