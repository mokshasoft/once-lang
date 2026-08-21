#!/usr/bin/env bash
# ============================================================================
# clean-agdai.sh — DELETE OCP0009's AGDA INTERFACES, FROM THE PLACE THEY
#                  ACTUALLY LIVE, AND SAY SO OUT LOUD.
#
# WHY THIS EXISTS.  On 2026-08-16 a cold-vs-warm timing comparison (the cost
# of re-exports) was run by deleting `poc/OCP0009/.agdai/`.  That directory
# holds ZERO files: it is not where agda writes.  Every deletion was a
# silent no-op, so both runs were WARM and the numbers — 4.0s "cold" vs
# 11.5s "warm" — measured cache state, not the thing under test.  The
# conclusion drawn from them was wrong and had to be retracted.
#
# ⚠ THE BUG WAS NOT "WRONG PATH".  A wrong path is easy to spot.  The bug
#   was that deleting nothing LOOKS EXACTLY LIKE deleting everything: both
#   print nothing and both exit 0.  So the contract of this script is:
#
#       IT IS AN ERROR TO DELETE ZERO FILES.
#
#   If nothing matched, this exits 2 and complains.  A cold-cache
#   measurement that silently skipped its own cache-clear can no longer
#   pass for a successful one.  (Same failure shape as
#   `sweep-refusal-exits-zero` and `appends-need-absolute-paths`: the
#   dangerous outcome is the one that is indistinguishable from success.)
#
# WHERE THE INTERFACES REALLY ARE.  `bootstrap/check.sh` does `cd bootstrap`
# and invokes `agda poc/OCP0009/M.agda`.  Agda writes interfaces under the
# project root's build directory, keyed by version:
#
#       bootstrap/_build/<agda-version>/agda/poc/OCP0009/<Module>.agdai
#
# The version is READ FROM `agda --version`, never hardcoded — after a
# toolchain bump a hardcoded "2.8.0" would silently stop matching and we
# would be right back to deleting nothing.
#
# USAGE
#   ./clean-agdai.sh                     # every OCP0009 interface
#   ./clean-agdai.sh NbEPDirDBLibAmrec   # named modules (.agda/.agdai optional)
#   ./clean-agdai.sh 'NbEPDirDBExamplesGcd*'   # globs (quote them!)
#   ./clean-agdai.sh -n ...              # dry run: list, delete nothing
#   ./clean-agdai.sh --deps M            # M *and every module that imports it*,
#                                        #   transitively — what you actually
#                                        #   want before re-timing M's clients
#
# EXIT STATUS
#   0  deleted (or, under -n, would have deleted) at least one file
#   2  matched nothing — TREAT AS A FAILED CACHE-CLEAR, NOT AS "already clean"
#   3  refused: another agda is running
# ============================================================================
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
BOOT="$(cd "$HERE/../.." && pwd)"

DRY=0; DEPS=0; ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    -n|--dry-run) DRY=1 ;;
    --deps)       DEPS=1 ;;
    -h|--help)    sed -n '2,50p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*)           echo "clean-agdai.sh: unknown flag $1" >&2; exit 64 ;;
    *)            ARGS+=("$1") ;;
  esac
  shift
done

# --- contention guard -----------------------------------------------------
# Deleting an interface out from under a live agda gives it a torn view of
# the build dir. Same rule as sweep.sh. Dry runs are harmless, so allow them.
if [ "$DRY" -eq 0 ] && pgrep -f '[b]in/agda' >/dev/null 2>&1; then
  echo "!! REFUSING: another agda is running — deleting interfaces now would" >&2
  echo "   pull the build dir out from under it. Wait for it to finish." >&2
  pgrep -af '[b]in/agda' | sed 's/^/     /' | cut -c1-140 >&2
  exit 3
fi

VER="$(agda --version 2>/dev/null | head -1 | grep -oP '\d+\.\d+(\.\d+)*')"
[ -z "$VER" ] && { echo "clean-agdai.sh: cannot read 'agda --version'" >&2; exit 1; }
IDIR="$BOOT/_build/$VER/agda/poc/OCP0009"

echo "-- agda $VER"
echo "-- interface dir: $IDIR"
if [ ! -d "$IDIR" ]; then
  echo "!! NO SUCH DIRECTORY. Either nothing has ever been built with agda $VER," >&2
  echo "   or the build layout moved. Deleting nothing is NOT success — fix this." >&2
  exit 2
fi

# --- expand the requested module set --------------------------------------
declare -a MODS=()
if [ "${#ARGS[@]}" -eq 0 ]; then
  MODS=('*')
else
  for a in "${ARGS[@]}"; do
    MODS+=("$(basename "$a" .agda | sed 's/\.agdai$//')")
  done
  # --deps: close the set upward over the import graph (clients of clients).
  # An interface is only stale-proof if its importers are cleared too.
  if [ "$DEPS" -eq 1 ]; then
    changed=1
    while [ "$changed" -eq 1 ]; do
      changed=0
      for m in "${MODS[@]}"; do
        while IFS= read -r c; do
          [ -z "$c" ] && continue
          for seen in "${MODS[@]}"; do [ "$seen" = "$c" ] && continue 2; done
          MODS+=("$c"); changed=1
        done < <(grep -l "poc\.OCP0009\.$m\b" "$HERE"/*.agda 2>/dev/null \
                   | xargs -r -n1 basename | sed 's/\.agda$//')
      done
    done
    echo "-- --deps closed the set to ${#MODS[@]} module(s)"
  fi
  # Typo guard: a module named on the command line that has no source file
  # is almost certainly a misspelling, and would otherwise just match nothing.
  for m in "${MODS[@]}"; do
    case "$m" in *'*'*|*'?'*|*'['*) continue ;; esac
    [ -f "$HERE/$m.agda" ] || echo "   ?? no source '$m.agda' — typo?" >&2
  done
fi

# --- collect, then act ----------------------------------------------------
# NB: plain globbing under `nullglob`, NOT `compgen -G` — compgen is absent
# in some non-interactive shells here and expanded to nothing WITHOUT error,
# i.e. exactly the silent no-op this script exists to make impossible.
shopt -s nullglob
declare -a HITS=()
for m in "${MODS[@]}"; do
  # `-e` is load-bearing: a pattern with NO metacharacters is not a glob,
  # so nullglob does not apply and a non-existent literal name would sail
  # through as a phantom hit — making a 0-file clear report as a 1-file one.
  for f in "$IDIR"/$m.agdai; do [ -e "$f" ] && HITS+=("$f"); done
done
shopt -u nullglob
# de-duplicate (--deps and globs can overlap)
if [ "${#HITS[@]}" -gt 0 ]; then
  mapfile -t HITS < <(printf '%s\n' "${HITS[@]}" | sort -u)
fi

N="${#HITS[@]}"
if [ "$N" -eq 0 ]; then
  echo "" >&2
  echo "############################################################" >&2
  echo "## clean-agdai.sh DELETED NOTHING — matched 0 interfaces." >&2
  echo "## Do NOT read this as 'the cache was already clear'. If you" >&2
  echo "## are about to take a cold-cache measurement, that run will" >&2
  echo "## be WARM and the number will be wrong. Check the module" >&2
  echo "## names and the interface dir printed above." >&2
  echo "############################################################" >&2
  exit 2
fi

BYTES=$(du -ch "${HITS[@]}" 2>/dev/null | tail -1 | cut -f1)
if [ "$DRY" -eq 1 ]; then
  printf '%s\n' "${HITS[@]}" | xargs -r -n1 basename | sed 's/^/   would delete /'
  echo "== DRY RUN: $N interface(s), $BYTES — nothing deleted"
else
  rm -f -- "${HITS[@]}"
  left=0
  for f in "${HITS[@]}"; do [ -e "$f" ] && left=$((left+1)); done
  if [ "$left" -ne 0 ]; then
    echo "!! $left file(s) survived deletion (permissions?)" >&2; exit 1
  fi
  echo "== DELETED $N interface(s), $BYTES"
fi
