#!/usr/bin/env bash
# ============================================================================
# sweep.sh — BUILD EVERYTHING THAT IS SUPPOSED TO BE GREEN, AND ONLY THAT.
#
# WHY THIS EXISTS.  A naive `for f in *.agda; do check.sh $f; done` reports
# three classes of NON-problem as failures, and on 2026-08-13 that cost a
# long detour (a git worktree, a control run, and a misapplied D10) chasing
# a regression that did not exist:
#
#   1. RED modules — DELIBERATE negative results (e.g. the option-C lexrec
#      branches), kept so nobody re-attempts them.  They are SUPPOSED to
#      OOM, and their headers say so with the measured timings.
#   2. Modules needing a non-default RTS — `LexSS2` needs `+RTS -c` (the
#      compacting collector); under the default copying GC it is killed at
#      the cap.  Documented only in the module header.
#   3. PROBES (Spike*) — exploratory, several contain holes and were never
#      green.  They are not part of the tower; `build-tower.sh` never
#      mentions them.
#
# ⚠⚠ AND THE BIGGEST ONE, WHICH IS NOT ABOUT FILES AT ALL: running two
#    `agda` processes at once makes the heavy modules OOM-kill each other.
#    Every false alarm on 2026-08-13 traced back to that.  This script
#    REFUSES TO START if another agda is live, and runs strictly
#    sequentially.  See `never-run-two-agda-checks-at-once`.
#
# CLASSIFICATION IS READ FROM THE SOURCE, not from a list here — so a new
# module inherits the right treatment by saying so in its own header:
#
#   RED       header contains  "IS **RED**"
#   needs -c  header contains  "COMPACTING COLLECTOR"
#
# USAGE
#   ./sweep.sh              # kernel + libs + examples (the things that must be green)
#   ./sweep.sh kernel       # the tower only
#   ./sweep.sh libs
#   ./sweep.sh examples
#   ./sweep.sh probes       # Spike* — reported, never fails the sweep
#   ./sweep.sh --report     # classify only, build nothing
#
# EXIT STATUS: non-zero iff a module that is SUPPOSED to be green failed.
# ============================================================================
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
BOOT="$(cd "$HERE/../.." && pwd)"
CHECK="$BOOT/check.sh"
LOGDIR="${TMPDIR:-/tmp}/ocp0009-sweep"
mkdir -p "$LOGDIR"

WHAT="${1:-all}"

# --- the contention guard -------------------------------------------------
if pgrep -f '[b]in/agda' >/dev/null 2>&1; then
  echo "!! REFUSING TO START: another agda is already running."
  echo "   Two agda processes OOM-kill each other on this box; every"
  echo "   false alarm on 2026-08-13 came from exactly that."
  pgrep -af '[b]in/agda' | sed 's/^/     /' | cut -c1-140
  exit 2
fi

# --- classification -------------------------------------------------------
is_red()    { head -40 "$1" | grep -q 'IS \*\*RED\*\*'; }
needs_c()   { head -40 "$1" | grep -qi 'COMPACTING COLLECTOR'; }

KERNEL_RE='NbEPDirDB(Pi|Var|Type|SR|Conf|Inj|Subj|LR|SN|SNSig|Sig|FundSN|FundSem|Fund|Canon|Norm|Univ|Tr|Full|Core|Pass)\.agda$'

classify() {                       # → kernel | libs | examples | probes | other
  local b; b="$(basename "$1")"
  case "$b" in
    Spike*)              echo probes ;;
    NbEPDirDBLib*)       echo libs ;;
    NbEPDirDBExamples*)  echo examples ;;
    *) if [[ "$b" =~ $KERNEL_RE ]]; then echo kernel; else echo other; fi ;;
  esac
}

# --- gather ---------------------------------------------------------------
declare -a RED=() TOBUILD=() SKIPPED=()
for f in "$HERE"/NbEPDirDB*.agda "$HERE"/Spike*.agda; do
  [ -e "$f" ] || continue
  cat="$(classify "$f")"
  if is_red "$f"; then RED+=("$f"); continue; fi
  case "$WHAT" in
    all)      [ "$cat" = probes ] && { SKIPPED+=("$f"); continue; } ;;
    kernel|libs|examples|probes)
              [ "$cat" = "$WHAT" ] || { SKIPPED+=("$f"); continue; } ;;
    --report) : ;;
    *) echo "unknown target: $WHAT"; exit 2 ;;
  esac
  TOBUILD+=("$f")
done

echo "== OCP-0009 sweep — target: $WHAT"
echo
echo "-- RED (deliberate negative results, NOT built): ${#RED[@]}"
for f in "${RED[@]:-}"; do [ -n "$f" ] && echo "     $(basename "$f" .agda)"; done

# --- orphan report: nothing imports these ---------------------------------
echo
echo "-- ORPHANS (no other module imports them — review for supersession):"
for f in "$HERE"/NbEPDirDB*.agda; do
  m="$(basename "$f" .agda)"
  if ! grep -qh "poc\.OCP0009\.$m\b" "$HERE"/*.agda --exclude="$m.agda" 2>/dev/null; then
    printf '     %-38s [%s]\n' "$m" "$(classify "$f")"
  fi
done

if [ "$WHAT" = "--report" ]; then echo; echo "(report only; nothing built)"; exit 0; fi

# --- build ----------------------------------------------------------------
echo
# ⚠ ORDER MATTERS: a module needing a non-default RTS must be built BEFORE
#   anything that imports it.  `needs_c` reads a file's OWN header, so if a
#   heavy module is first pulled in as a DEPENDENCY of an earlier build, it
#   is compiled without its flag and dies of memory — which reads as a
#   SIGTERM on the IMPORTER, not on the module that actually needs the flag.
#   (Measured: LexAsm(143), whose log showed it checking LexSS2; LexAsm
#   builds clean in ~4s once LexSS2 is warm.)  So: RTS-special modules first.
ORDERED=(); REST=()
for f in "${TOBUILD[@]:-}"; do
  [ -n "$f" ] || continue
  if needs_c "$f"; then ORDERED+=("$f"); else REST+=("$f"); fi
done
TOBUILD=("${ORDERED[@]:-}" "${REST[@]:-}")

echo "-- BUILDING ${#TOBUILD[@]} module(s), sequentially (RTS-special first)"
fail=0; failed=(); TIMES=()
for f in "${TOBUILD[@]:-}"; do
  [ -n "$f" ] || continue
  m="$(basename "$f" .agda)"
  rts="-A64m"; note=""
  if needs_c "$f"; then rts="-A64m -c"; note=" (compacting GC, per header)"; fi
  printf '   %-40s%s ' "$m" "$note"
  _t0=$SECONDS
  if AGDA_RTS="$rts" "$CHECK" "poc/OCP0009/$m.agda" >"$LOGDIR/$m.log" 2>&1; then
    _d=$((SECONDS-_t0)); TIMES+=("$_d $m")
    if [ "$_d" -ge 10 ]; then echo "ok  ${_d}s  <-- SLOW"; else echo "ok  ${_d}s"; fi
  else
    rc=$?
    if [ "$rc" = 143 ] && [ "$rts" = "-A64m" ]; then
      # ★ MEASURED 2026-08-21: 143 under the COPYING collector is not a
      #   verdict — it is a collector choice.  `…ExamplesGcdLeMid` OOMs at
      #   113s under `-A64m` and COMPLETES IN 82s under `-A64m -c`, same
      #   machine, same minute.  The six-way `…GcdDvdA*` split re-merged
      #   into ONE 451-line module likewise OOMs under `-A64m` (339s) and
      #   builds under `-c` (147s).
      #   ⚠ So `needs_c`'s hand-written header list CANNOT be right: whether
      #   a module OOMs depends on how much RAM the machine has free, which
      #   no header comment can track.  Retry once, automatically.
      #   ⚠ This is a FALLBACK, not a default: `-c` costs ~45% wall on a
      #   module that does not need it (check.sh header: 13.7s vs 19.8s).
      printf 'KILLED(143) — retrying with compacting GC ... '
      if AGDA_RTS="-A64m -c" "$CHECK" "poc/OCP0009/$m.agda" >"$LOGDIR/$m.log" 2>&1; then
        echo "ok (-c)"
        continue
      fi
      rc=$?
    fi
    if [ "$rc" = 143 ]; then
      echo "KILLED(143) — SIGTERM: memory cap or contention, NOT a proof error"
    else
      echo "FAIL($rc)"
    fi
    failed+=("$m($rc)"); fail=$((fail+1))
  fi
done

# ★ SLOWEST MODULES — the standing perf target is EVERY EXAMPLE UNDER 10s.
if [ "${#TIMES[@]}" -gt 0 ]; then
  echo
  echo "-- SLOWEST (>=10s):"
  printf '%s\n' "${TIMES[@]}" | sort -rn | awk '$1>=10 {printf "   %-42s %ss\n", $2, $1}'
  printf '%s\n' "${TIMES[@]}" | awk '{t+=$1} END {printf "   (total build time %ds across %d modules)\n", t, NR}'
fi

echo
if [ "$fail" -eq 0 ]; then
  echo "== ALL GREEN (${#TOBUILD[@]} modules).  RED skipped: ${#RED[@]}."
  exit 0
else
  echo "== $fail FAILED: ${failed[*]}"
  echo "   logs in $LOGDIR"
  echo "   ⚠ exit 143 = SIGTERM (cap/contention), exit 42 = a real Agda error."
  exit 1
fi
