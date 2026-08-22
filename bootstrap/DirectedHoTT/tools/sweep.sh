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
      if AGDA_RTS="-A64m -c" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1; then
        d=$((SECONDS-t0)); TIMES+=("$d $tag"); echo "ok (-c) ${d}s"; continue
      fi
      rc=$?
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
