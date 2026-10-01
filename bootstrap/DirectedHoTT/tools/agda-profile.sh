#!/usr/bin/env bash
# ============================================================================
# agda-profile.sh — WHERE DOES A SLOW MODULE SPEND ITS TIME?
#
# Runs under the patched Agda (the build `once-lang2`'s run-ast-dumps.sh
# uses; its `perf-intro.md` documents the reports) with, per SITE — each
# definition, and each `[positivity]`/`[termination]`/… check after a block:
#   --profile=definitions  CPU time        --profile=allocation  bytes allocated
#   --profile=reduction    unfoldings, and which site caused them
#   --profile=conversion   conversion checks per head
# Only the project's own modules are counted; every row names its file.
#
#   tools/agda-profile.sh DirectedHoTT/Examples/Knot/LookupCon.agda   # one module
#   tools/agda-profile.sh --survey    # COLD, every Trust root in turn: ranks
#                                     # every module and definition we build
#   HEAP=4G TIMEOUT=900 tools/agda-profile.sh <module.agda>
#
# The survey checks each `Trust/` root in its own process, in order, in the
# staged tree with IDENTICAL flags, so every module is checked (and counted)
# exactly once — in the report of the first root that reaches it.  A root
# that dies still leaves its last snapshot (`--counters-snapshot`), and the
# next root resumes from the interfaces already written.  Summary:
# `tools/profile-report.py $STAGE/reports/survey/*.json`.
#
# ★ WHAT WAS HARD TO GET RIGHT (each of these cost a run):
#   1. The patched Agda has its OWN version string, so it cannot reuse the
#      project's interfaces — and must not overwrite them.  It runs in a
#      STAGED COPY under $STAGE (bootstrap/ + formal/, sources only).  The
#      staged `_build` is kept across runs, so only changed modules recheck.
#   2. ★ ANY change of flags (`--profile=…`, `--no-fast-reduce`) INVALIDATES
#      the interfaces: the next run rechecks the dependencies UNDER the
#      profile, and the report then describes them, not the target
#      (measured: 8–11 modules, e.g. Spec.Syntax … Confluence).  So the
#      imports are built with EXACTLY the flags of the profiled run (their
#      counters go to a separate file), and the script lists what the
#      profiled run rechecked — anything but the target means a polluted report.
#   3. The report is written when the run stops on an error, a HEAP
#      EXHAUSTION or SIGINT (the 2026-09-29 build; `timeout --foreground -s
#      INT`), and rewritten every 60 s as a SNAPSHOT, which is what survives
#      a kill -9 / OOM kill.  The heap is still CAPPED (`HEAP`) so a runaway
#      module dies of heap exhaustion, with a complete report, rather than
#      of the OOM killer.
#   4. Without `--no-fast-reduce` the unfolding counts are near zero (the
#      fast evaluator is not counted); WITH it, rechecking the imports alone
#      exhausted 3 GB.  It is opt-in: NOFAST=1.  The conversion counts are
#      collected either way.
#   5. Agda prints non-ASCII; under a non-UTF-8 locale it dies mid-output.
#
# ⚠ Another session may be running agda on this box (7.5 GiB).  The script
#   prints what is running; it does not wait or kill anything.
# ============================================================================

set -uo pipefail

# OOM protection — the same cgroup re-exec as check.sh (read its rationale).
# 2026-10-01: without it, the dependency stage (a cold closure of ~40 modules
# under the profiling flags, -M5G on a 7.5 GiB box) reached 3.7 GB RSS plus
# swap; the global OOM killed agda, and systemd then stopped the terminal's
# whole scope, killing the claude session with it.  -M never fired: it sits
# above what the box had free.
if [ -z "${AGDA_SAFE_ACTIVE:-}" ] && [ -z "${AGDA_SAFE_DISABLE:-}" ] \
   && command -v systemd-run >/dev/null 2>&1 \
   && [ -e /sys/fs/cgroup/cgroup.controllers ] \
   && systemctl --user show-environment >/dev/null 2>&1; then
  export AGDA_SAFE_ACTIVE=1
  exec systemd-run --user --scope --quiet \
    -p MemoryMax="${AGDA_SAFE_MEM_MAX:-5500M}" \
    -p MemorySwapMax="${AGDA_SAFE_SWAP_MAX:-2G}" \
    -- bash -c '
      if [ -w /proc/self/oom_score_adj ]; then
        echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
      fi
      exec bash "$@"
    ' bash "$(readlink -f "$0")" "$@"
fi

TARGET="${1:?usage: $0 <module path relative to bootstrap/, e.g. DirectedHoTT/Examples/Knot/Lookup.agda> | --survey}"
SURVEY=0; [ "$TARGET" = --survey ] && SURVEY=1

HERE="$(cd "$(dirname "$0")" && pwd)"            # bootstrap/DirectedHoTT/tools
BOOT="$(cd "$HERE/../.." && pwd)"                # bootstrap/
REPO="$(cd "$BOOT/.." && pwd)"                   # repo root
STAGE="${STAGE:-$HOME/.cache/once-lang5-profile}"
OUT="${OUT:-$STAGE/reports}"
HEAP="${HEAP:-4G}"
COMPACT="${COMPACT:--c30}"
TIMEOUT="${TIMEOUT:-$([ "$SURVEY" = 1 ] && echo 14400 || echo 2400)}"
NOFAST="${NOFAST:-0}"
LOCALE="${LOCALE:-en_US.utf8}"

AGDA_TREE="${AGDA_TREE:-$HOME/Repo/OpenSource/agda/dist-newstyle}"
if [ -z "${AGDA:-}" ]; then
  AGDA="$(find "$AGDA_TREE" -type f -perm -u+x -name agda -path '*/x/agda/*' \
            -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)"
fi

say() { printf '%s  %s\n' "$(date +%H:%M:%S)" "$*"; }
die() { printf 'error: %s\n' "$*" >&2; exit 1; }

[ -n "${AGDA:-}" ] && [ -x "$AGDA" ] || die "no patched agda under $AGDA_TREE (set \$AGDA)"
[ "$SURVEY" = 1 ] || [ -f "$BOOT/$TARGET" ] || die "no such module: $BOOT/$TARGET"
case "$(LC_ALL="$LOCALE" "$AGDA" --help 2>&1)" in
  *--counters-folded*) ;;
  *) die "$AGDA has no --counters-folded; build the branch that adds it (perf-intro.md)" ;;
esac

STDLIB="$(find /nix/store -maxdepth 2 -name standard-library.agda-lib 2>/dev/null | head -1)"
[ -n "$STDLIB" ] || die "standard-library.agda-lib not found in /nix/store"

mkdir -p "$STAGE" "$OUT"
say "agda:   $AGDA"
say "stage:  $STAGE"
say "target: $TARGET   heap $HEAP $COMPACT, timeout ${TIMEOUT}s"
running="$(ps -eo pid,rss,args | grep '[b]in/agda' | awk '{printf "  pid %s  %d MB  %s\n", $1, $2/1024, $NF}')"
[ -n "$running" ] && { say "⚠ other agda running (timings are unreliable):"; printf '%s\n' "$running"; }

# 1. stage the sources (keep the staged _build)
rsync -a --delete --exclude=_build --exclude='*.agdai' --exclude=.git --exclude=tmp \
      "$BOOT/" "$STAGE/bootstrap/"
rsync -a --delete --exclude=_build --exclude='*.agdai' --exclude=.git \
      "$REPO/formal/" "$STAGE/formal/"
[ -d "$STAGE/.git" ] || git -C "$STAGE" init -q     # bounds Agda's project-root search
LIBS="$STAGE/libs.txt"
printf '%s\n' "$STDLIB" "$STAGE/formal/Once.agda-lib" "$STAGE/bootstrap/bootstrap.agda-lib" > "$LIBS"

run_agda() {  # heap-arg, then agda args
  local heap="$1"; shift
  ( cd "$STAGE/bootstrap" && LC_ALL="$LOCALE" "$AGDA" +RTS -M"$heap" "$COMPACT" -A64m -RTS \
      --library-file="$LIBS" --transliterate "$@" )
}

PFLAGS=(--profile=definitions --profile=allocation --profile=reduction --profile=conversion)
[ "$NOFAST" = 1 ] && PFLAGS=(--no-fast-reduce "${PFLAGS[@]}")

# ★ SURVEY: every Trust root, cold, one process each
if [ "$SURVEY" = 1 ]; then
  if [ "${KEEP:-0}" != 1 ]; then
    say "survey: COLD — removing the staged interfaces (KEEP=1 keeps them)"
    rm -rf "$STAGE/bootstrap/_build" "$STAGE/formal/_build"
    find "$STAGE/bootstrap" -name '*.agdai' -delete
  fi
  SDIR="$OUT/survey"; mkdir -p "$SDIR"
  ROOTS="${ROOTS:-Kernel Lib Knot1 Knot2 Knot3 Knot4 Knot5 Knot6 Knot7 Knot8 Examples Comparison}"
  for r in $ROOTS; do
    f="DirectedHoTT/Trust/$r.agda"
    [ -f "$STAGE/bootstrap/$f" ] || { say "survey: no $f, skipped"; continue; }
    start=$(date +%s)
    say "survey: $r"
    timeout --foreground -s INT "$TIMEOUT" bash -c "$(declare -f run_agda); STAGE='$STAGE' LOCALE='$LOCALE' AGDA='$AGDA' COMPACT='$COMPACT' LIBS='$LIBS' \
      run_agda '$HEAP' ${PFLAGS[*]} --counters-file='$SDIR/$r.json' --counters-folded='$SDIR/$r' '$f'" > "$SDIR/$r.log" 2>&1
    rc=$?
    n=$(grep -ac 'Checking' "$SDIR/$r.log")
    say "survey: $r exit $rc after $(( $(date +%s) - start ))s, $n module(s) checked"
    grep -q "Heap exhausted" "$SDIR/$r.log" && say "survey: ⚠ $r exhausted $HEAP — rerun with ROOTS=$r HEAP=5G KEEP=1"
    [ "$rc" -ne 0 ] && [ "${STOP_ON_FAIL:-0}" = 1 ] && break
  done
  say "survey done. Summary:"
  python3 "$HERE/profile-report.py" "$SDIR"/*.json | tee "$SDIR/SUMMARY.txt"
  say "summary: $SDIR/SUMMARY.txt   flame graphs: $SDIR/*.time.folded (speedscope.app)"
  exit 0
fi

# 2. the target's imports, with the SAME flags (else they are rechecked under the profile)
slug="$(basename "$TARGET" .agda)"
deplog="$OUT/$slug.deps.log"; : > "$deplog"
deps="$(grep -oE '^open import [A-Za-z0-9_.]+|^import [A-Za-z0-9_.]+' "$BOOT/$TARGET" | awk '{print $NF}' | sort -u)"
for m in $deps; do
  f="$(echo "$m" | tr . /).agda"
  [ -f "$STAGE/bootstrap/$f" ] || continue          # stdlib / Agda builtins
  say "deps:   $m"
  run_agda 5G "${PFLAGS[@]}" --counters-file="$OUT/$slug.deps-counters.txt" "$f" >> "$deplog" 2>&1 \
    || die "dependency $m failed; see $deplog"
done

# 3. the target, profiled
report="$OUT/$slug.json"; log="$OUT/$slug.log"; rm -f "$report"
say "profile: $TARGET  (report: $report)"
start=$(date +%s)
timeout --foreground -s INT "$TIMEOUT" bash -c "$(declare -f run_agda); STAGE='$STAGE' LOCALE='$LOCALE' AGDA='$AGDA' COMPACT='$COMPACT' LIBS='$LIBS' \
  run_agda '$HEAP' ${PFLAGS[*]} --counters-file='$report' --counters-folded='$OUT/$slug' '$TARGET'" > "$log" 2>&1
rc=$?
say "exit $rc after $(( $(date +%s) - start ))s  (log: $log)"
rechecked="$(grep -a 'Checking' "$log" | sed 's/^ *Checking //;s/ *(.*//' | grep -v "^$(echo "$TARGET" | sed 's|/|.|g;s|\.agda$||')$")"
[ -n "$rechecked" ] && { say "⚠ POLLUTED: the profiled run also rechecked:"; printf '    %s\n' $rechecked; }
grep -q "Heap exhausted" "$log" && say "heap exhausted at $HEAP — the report below is what it had counted"

if [ -s "$report" ]; then
  echo; python3 "$HERE/profile-report.py" "$report"
  say "flame graphs: $OUT/$slug.{time,allocation,unfoldings}.folded (speedscope.app)"
else
  say "no report written (a kill -9 before the first 60 s snapshot writes none)"
  exit 1
fi
