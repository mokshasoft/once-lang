#!/usr/bin/env bash
# ============================================================================
# agda-profile.sh — WHERE DOES A SLOW MODULE SPEND ITS TIME?
#
# Runs ONE module under the patched Agda (the build `once-lang2`'s
# run-ast-dumps.sh uses) with per-definition counters:
#   --profile=reduction    how often each definition is UNFOLDED
#   --profile=conversion   how often each definition is in a CONVERSION check
# The report names the definitions the checker keeps normalising — for the
# Knot that is typically `KD`/`SD`/`CtxD` under a substitution
# (memory: knot-description-normalisation-trap).
#
#   tools/agda-profile.sh DirectedHoTT/Examples/Knot/LookupCon.agda
#   HEAP=2G TIMEOUT=900 tools/agda-profile.sh <module.agda>
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
#   3. The report is written when the run stops on an error or a HEAP
#      EXHAUSTION — but NOT on a SIGTERM/SIGINT timeout (measured: a
#      `timeout -s INT` run left no report).  So the heap is CAPPED (`HEAP`):
#      a runaway module dies of heap exhaustion and the report is written.
#      The timeout is only a last resort.
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

TARGET="${1:?usage: $0 <module path relative to bootstrap/, e.g. DirectedHoTT/Examples/Knot/Lookup.agda>}"

HERE="$(cd "$(dirname "$0")" && pwd)"            # bootstrap/DirectedHoTT/tools
BOOT="$(cd "$HERE/../.." && pwd)"                # bootstrap/
REPO="$(cd "$BOOT/.." && pwd)"                   # repo root
STAGE="${STAGE:-$HOME/.cache/once-lang5-profile}"
OUT="${OUT:-$STAGE/reports}"
HEAP="${HEAP:-3G}"
COMPACT="${COMPACT:--c30}"
TIMEOUT="${TIMEOUT:-2400}"
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
[ -f "$BOOT/$TARGET" ] || die "no such module: $BOOT/$TARGET"
case "$(LC_ALL="$LOCALE" "$AGDA" --help 2>&1)" in
  *--counters-file*) ;;
  *) die "$AGDA has no --counters-file; build the branch that adds it" ;;
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

PFLAGS=(--profile=reduction --profile=conversion)
[ "$NOFAST" = 1 ] && PFLAGS=(--no-fast-reduce "${PFLAGS[@]}")

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
report="$OUT/$slug.counters.txt"; log="$OUT/$slug.log"; rm -f "$report"
say "profile: $TARGET  (report: $report)"
start=$(date +%s)
timeout -s INT "$TIMEOUT" bash -c "$(declare -f run_agda); STAGE='$STAGE' LOCALE='$LOCALE' AGDA='$AGDA' COMPACT='$COMPACT' LIBS='$LIBS' \
  run_agda '$HEAP' ${PFLAGS[*]} --counters-file='$report' --counters-format=text '$TARGET'" > "$log" 2>&1
rc=$?
say "exit $rc after $(( $(date +%s) - start ))s  (log: $log)"
rechecked="$(grep -a 'Checking' "$log" | sed 's/^ *Checking //;s/ *(.*//' | grep -v "^$(echo "$TARGET" | sed 's|/|.|g;s|\.agda$||')$")"
[ -n "$rechecked" ] && { say "⚠ POLLUTED: the profiled run also rechecked:"; printf '    %s\n' $rechecked; }
grep -q "Heap exhausted" "$log" && say "heap exhausted at $HEAP — the report below is what it had counted"

if [ -s "$report" ]; then
  echo; head -60 "$report"
else
  say "no report written (a timeout kill writes none — lower HEAP so it dies of heap instead)"
  exit 1
fi
