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
echo "-- BUILDING ${#TOBUILD[@]} module(s), sequentially"
fail=0; failed=()
for f in "${TOBUILD[@]:-}"; do
  [ -n "$f" ] || continue
  m="$(basename "$f" .agda)"
  rts="-A64m"; note=""
  if needs_c "$f"; then rts="-A64m -c"; note=" (compacting GC, per header)"; fi
  printf '   %-40s%s ' "$m" "$note"
  if AGDA_RTS="$rts" "$CHECK" "poc/OCP0009/$m.agda" >"$LOGDIR/$m.log" 2>&1; then
    echo "ok"
  else
    rc=$?
    if [ "$rc" = 143 ]; then
      echo "KILLED(143) — SIGTERM: memory cap or contention, NOT a proof error"
    else
      echo "FAIL($rc)"
    fi
    failed+=("$m($rc)"); fail=$((fail+1))
  fi
done

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
