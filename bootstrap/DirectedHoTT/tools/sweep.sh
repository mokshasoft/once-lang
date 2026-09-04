#!/usr/bin/env bash
# ============================================================================
# DirectedHoTT sweep — builds THE LIVE PATH ONLY.
#
# ★ WHAT IS AND IS NOT BUILT, AND WHY THAT IS THE POINT.
#   Spec/ Metatheory/ Algorithm/ Lib/ Examples/ Trust.agda   -> BUILT
#   Comparison/                                              -> BUILT, reported apart
#   Negative/                                                -> NOT BUILT
#
# ★ COMPARISON/ AND NEGATIVE/ ARE OPPOSITE, DELIBERATELY.  `Negative/` holds
#   REFUTED results and must NOT build — one that still compiles is
#   indistinguishable from a live one.  `Comparison/` holds deliberately
#   REDUNDANT routes (gcd three ways; the concrete IndStep the generic
#   plumbing replaced) and MUST build, or the baseline rots exactly when the
#   WF-axis comparison needs it.  It is excluded from the <10s accounting
#   instead: a benchmark is not a proof to optimise.
#
#   `Negative/` holds dHoTT's own refuted approaches (the lexrec track).
#   It is kept readable, not verified.  ⚠ A parked result that still built
#   would be indistinguishable from a live one — the same hazard as
#   `verification-that-covers-less-than-it-claims`.  Not building it is
#   what makes parking it honest.  Build it deliberately with `--negative`.
#
#   The superseded `poc/OCP0009/` tree is likewise never built from here.
#
# ⚠ EXIT 143 IS NOT A VERDICT.  It has at least three causes: a real
#   memory wall, the wrong collector, and metas that never solved.  This
#   script retries once with the compacting collector before believing it.
#   See PERF-2026-08-21.md §3.
# ============================================================================
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BOOT="$(cd "$ROOT/.." && pwd)"
CHECK="$BOOT/check.sh"
LOGDIR="${TMPDIR:-/tmp}/dhott-sweep"; mkdir -p "$LOGDIR"
WITH_NEG=0; [ "${1:-}" = "--negative" ] && WITH_NEG=1

is_red()  { head -40 "$1" | grep -q 'IS \*\*RED\*\*'; }
needs_c() { head -40 "$1" | grep -qi 'COMPACTING COLLECTOR'; }

echo "== DirectedHoTT sweep"
"$ROOT/tools/check-trust.sh" || exit 2

declare -a RED=() TOBUILD=() ORDERED=() REST=() CMP=()
while IFS= read -r f; do
  rel="${f#$BOOT/}"
  case "$rel" in DirectedHoTT/Negative/*) [ "$WITH_NEG" -eq 1 ] || continue ;; esac
  if is_red "$f"; then RED+=("$rel"); continue; fi
  case "$rel" in DirectedHoTT/Comparison/*) CMP+=("$rel"); continue ;; esac
  if needs_c "$f"; then ORDERED+=("$rel"); else REST+=("$rel"); fi
done < <(find "$ROOT" -name '*.agda' | sort)
TOBUILD=("${ORDERED[@]:-}" "${REST[@]:-}" "${CMP[@]:-}")

echo "-- RED (deliberate negative results, NOT built): ${#RED[@]}"
for f in "${RED[@]:-}"; do [ -n "$f" ] && echo "     $f"; done
[ "$WITH_NEG" -eq 0 ] && echo "-- Negative/ SKIPPED (parked, not verified) — use --negative to build it"
echo "-- BUILDING ${#TOBUILD[@]} module(s), sequentially (RTS-special first)"

fail=0; failed=(); TIMES=(); CTIMES=(); unmeasured=()
for rel in "${TOBUILD[@]:-}"; do
  [ -n "$rel" ] || continue
  f="$BOOT/$rel"; tag="$(echo "${rel#DirectedHoTT/}" | tr '/' '.')"; tag="${tag%.agda}"
  rts="-A64m"; note=""
  needs_c "$f" && { rts="-A64m -c"; note=" (compacting GC, per header)"; }
  printf '   %-46s%s ' "$tag" "$note"
  t0=$SECONDS
  if AGDA_RTS="$rts" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1; then
    d=$((SECONDS-t0))
    case "$rel" in
      DirectedHoTT/Comparison/*) CTIMES+=("$d $tag"); echo "ok  ${d}s  [comparison]" ;;
      *) TIMES+=("$d $tag")
         [ "$d" -ge 10 ] && echo "ok  ${d}s  <-- SLOW" || echo "ok  ${d}s" ;;
    esac
  else
    rc=$?
    if [ "$rc" = 143 ] && [ "$rts" = "-A64m" ]; then
      printf 'KILLED(143) — retrying with compacting GC ... '
      # ⚠ NOT `if … then … fi; rc=$?`.  After an `if` whose condition
      #   FAILED and which has no `else`, `$?` is the status of the `if`
      #   STATEMENT — which is 0.  That reported a second memory kill as
      #   `FAIL(0)`, i.e. as a PROOF ERROR, and cost a session's worth of
      #   chasing a module that checks clean on its own.  Capture the
      #   retry's own status, then branch on it.
      AGDA_RTS="-A64m -c" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1
      rc=$?
      if [ "$rc" = 0 ]; then
        d=$((SECONDS-t0)); TIMES+=("$d $tag"); echo "ok (-c) ${d}s"; continue
      fi
      # ★★★ THIRD RUNG: A **SMALLER** NURSERY, NOT A BIGGER ONE.
      #
      # ⚠⚠ CORRECTION (same day): the causal story below is NOT
      #   ESTABLISHED.  `Trust` was killed while ANOTHER Agda run
      #   (`Once/Adequacy`, a different session) was resident on this
      #   7.6 GB box, and it later passed at plain `-A64m` in 13s once the
      #   box was quiet.  So "Trust wants a smaller nursery" is one
      #   explanation; CONTENTION is another, and the evidence does not
      #   separate them.  ⇒ keep the rung — it costs nothing when the
      #   first two work — but do not cite it as a measured fact.
      #   See `never-run-two-agda-checks-at-once`.
      #
      # ⚠⚠ THE LADDER USED TO STOP HERE, AND IT STOPPED IN THE WRONG
      #   DIRECTION.  `-A64m` trades memory for speed; a module whose cost
      #   is READING MANY INTERFACES rather than allocating deeply wants
      #   the opposite trade.  `Trust.agda` — which imports all 236
      #   modules and type-checks nothing — was KILLED(143) at `-A64m`
      #   AND at `-A64m -c`, then passed at `-A8m -c` in **20 seconds**.
      #   Two rungs of a ladder that only ever went up reported a 20s
      #   module as a sweep failure.
      #
      # ★ So the last resort shrinks the allocation area.  It costs
      #   nothing when the first two rungs work, and it is the rung that
      #   the one module with the largest import closure actually needs.
      printf 'still 143 — retrying with a smaller nursery ... '
      AGDA_RTS="-A8m -c" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1
      rc=$?
      if [ "$rc" = 0 ]; then
        d=$((SECONDS-t0)); TIMES+=("$d $tag"); echo "ok (-A8m -c) ${d}s"; continue
      fi
    fi
    # ★ IN Comparison/, A 143 IS A MEASUREMENT YOU DID NOT GET, NOT A BREAK.
    #   Those modules are BENCHMARKS — deliberately redundant routes kept so
    #   the WF axis can be measured. If the machine cannot fit one today, the
    #   benchmark is unavailable; nothing is wrong with the code. (Measured
    #   2026-08-22: GcdIndStepConcrete builds in ~157s with headroom and
    #   OOMs at 2 GB free, under -c, -A16m -c AND -A8m -c alike.)
    #   ⚠ A 42 in Comparison/ is still RED — that is broken code, and a
    #     baseline that no longer compiles is worse than none.
    case "$rel:$rc" in
      DirectedHoTT/Comparison/*:143)
        echo "UNMEASURABLE(143) — benchmark did not fit; not a proof error"
        unmeasured+=("$tag"); continue ;;
    esac
    [ "$rc" = 143 ] && echo "KILLED(143) — memory, NOT a proof error" || echo "FAIL($rc)"
    failed+=("$tag($rc)"); fail=$((fail+1))
  fi
done

if [ "${#TIMES[@]}" -gt 0 ]; then
  echo; echo "-- SLOWEST (>=10s):"
  printf '%s\n' "${TIMES[@]}" | sort -rn | awk '$1>=10 {printf "   %-46s %ss\n", $2, $1}'
  printf '%s\n' "${TIMES[@]}" | awk '{t+=$1} END {printf "   (total %ds across %d modules)\n", t, NR}'
fi
if [ "${#CTIMES[@]}" -gt 0 ]; then
  echo "-- COMPARISON (benchmarks — built, but NOT part of the <10s target):"
  printf '%s\n' "${CTIMES[@]}" | sort -rn | awk '{printf "   %-46s %ss\n", $2, $1}'
fi
if [ "${#unmeasured[@]}" -gt 0 ]; then
  echo "-- UNMEASURABLE benchmarks (machine too small today): ${unmeasured[*]}"
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "== ALL GREEN (${#TOBUILD[@]} modules).  RED skipped: ${#RED[@]}."
  exit 0
fi
echo "== $fail FAILED: ${failed[*]}" >&2
exit 1
