#!/usr/bin/env bash
# ============================================================================
# DirectedHoTT — CHECK WHAT YOU JUST BROKE.
#
# `sweep.sh` answers "is everything still fine?" and costs ~11 minutes.
# During an edit loop the question is narrower — "what did THIS change
# break?" — and the answer is the changed modules plus everything that
# imports them, transitively.  Nothing else can have been affected.
#
# ★ IT IS NOT A "SKIP THE KERNEL" SCRIPT, and that idea does not pay:
#   MEASURED 2026-09-01 on a full sweep — `Spec/` is 1s and `Metatheory/`
#   21s of 657s, about 3%.  Agda already skips unchanged modules; what
#   costs time is DOWNSTREAM rebuilds, and those are exactly what tells
#   you the change is safe.  ⇒ the saving here comes from checking FEWER
#   modules, not from checking cheaper ones.
#
#   Editing a leaf (`Examples/Knot/Pw`) checks 1 module instead of 161.
#   Editing `Lib/IWk` still checks most of the tree — correctly, because
#   most of the tree depends on it.
#
# ⚠ THIS IS NOT A SUBSTITUTE FOR THE SWEEP BEFORE A COMMIT.  It cannot
#   see a module made stale by anything other than an import edge — a
#   regenerated file, a deleted definition, a `.agdai` cleared by hand.
#   Green here means "nothing that imports my edit broke", which is a
#   strictly weaker claim than the sweep's.  Committing on it alone is
#   `verification-that-covers-less-than-it-claims`.
#
# Usage:
#   tools/affected.sh                  # modules changed per `git status`
#   tools/affected.sh Lib/IPay.agda …  # explicit, paths under DirectedHoTT/
#   tools/affected.sh --list           # print the closure, check nothing
# ============================================================================
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BOOT="$(cd "$ROOT/.." && pwd)"
CHECK="$BOOT/check.sh"
LOGDIR="${TMPDIR:-/tmp}/dhott-affected"; mkdir -p "$LOGDIR"

LIST=0; [ "${1:-}" = "--list" ] && { LIST=1; shift; }

mod_of() { echo "DirectedHoTT.$(echo "${1#DirectedHoTT/}" | tr '/' '.' | sed 's/\.agda$//')"; }

# ---- the seed: explicit arguments, else whatever git says changed ---------
declare -a SEED=()
if [ "$#" -gt 0 ]; then
  for a in "$@"; do case "$a" in DirectedHoTT/*) SEED+=("$a") ;; *) SEED+=("DirectedHoTT/$a") ;; esac; done
else
  # ⚠ `git status` prints paths relative to the REPO ROOT, not to
  #   `bootstrap/` — so strip everything up to `DirectedHoTT/` rather than
  #   matching on it.  The first version silently found nothing.
  while IFS= read -r f; do
    case "$f" in *DirectedHoTT/*.agda) SEED+=("DirectedHoTT/${f#*DirectedHoTT/}") ;; esac
  done < <(git -C "$BOOT" status --porcelain | awk '{print $NF}')
fi
[ "${#SEED[@]}" -eq 0 ] && { echo "== nothing changed under DirectedHoTT/ — nothing to check"; exit 0; }

echo "== affected-by:"; for s in "${SEED[@]}"; do echo "     $s"; done

# ---- reverse closure over the import graph -------------------------------
# ⚠ THE GRAPH IS READ **ONCE**.  The first version grepped every file for
#   every seed on every round — O(rounds × files × seeds) `grep`s, which
#   took longer than the check it was meant to save.  One pass builds
#   `who-imports-what`, then the closure is a walk over that.
declare -A IMPORTEDBY=()
while IFS=: read -r f imp; do
  rel="${f#$BOOT/}"
  dep="DirectedHoTT/$(echo "${imp#open import DirectedHoTT.}" | tr '.' '/').agda"
  IMPORTEDBY["$dep"]="${IMPORTEDBY[$dep]:-} $rel"
done < <(grep -rhoH '^open import DirectedHoTT\.[A-Za-z0-9.]*' \
           --include='*.agda' "$ROOT" 2>/dev/null)

declare -A HIT=(); QUEUE=()
for s0 in "${SEED[@]}"; do HIT["$s0"]=1; QUEUE+=("$s0"); done
while [ "${#QUEUE[@]}" -gt 0 ]; do
  cur="${QUEUE[0]}"; QUEUE=("${QUEUE[@]:1}")
  for d in ${IMPORTEDBY[$cur]:-}; do
    case "$d" in *"/Negative/"*) continue ;; esac
    [ -n "${HIT[$d]:-}" ] && continue
    HIT["$d"]=1; QUEUE+=("$d")
  done
done

# ---- order: dependencies before dependents, cheaply (by import count) ----
declare -a TOBUILD=()
while IFS= read -r rel; do TOBUILD+=("$rel"); done < <(
  for rel in "${!HIT[@]}"; do
    printf '%s %s\n' "$(grep -c '^open import DirectedHoTT' "$BOOT/$rel" 2>/dev/null || echo 0)" "$rel"
  done | sort -n | awk '{print $2}')

echo "-- ${#TOBUILD[@]} module(s) affected (of $(find "$ROOT" -name '*.agda' | wc -l) total)"
if [ "$LIST" -eq 1 ]; then printf '     %s\n' "${TOBUILD[@]}"; exit 0; fi

needs_c() { head -40 "$1" | grep -qi 'COMPACTING COLLECTOR'; }
fail=0; failed=()
for rel in "${TOBUILD[@]}"; do
  f="$BOOT/$rel"; tag="$(echo "${rel#DirectedHoTT/}" | tr '/' '.')"; tag="${tag%.agda}"
  rts="-A64m"; needs_c "$f" && rts="-A64m -c"
  printf '   %-46s ' "$tag"; t0=$SECONDS
  if AGDA_RTS="$rts" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1; then
    echo "ok  $((SECONDS-t0))s"
  else
    rc=$?
    # ⚠ the same 143 retry `sweep.sh` documents — a memory kill is not a
    #   verdict, and capturing the RETRY's status (not the `if`'s) is the
    #   bug that once reported a second kill as a proof error.
    if [ "$rc" = 143 ] && [ "$rts" = "-A64m" ]; then
      printf 'KILLED(143), retrying -c ... '
      AGDA_RTS="-A64m -c" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1; rc=$?
      [ "$rc" = 0 ] && { echo "ok (-c) $((SECONDS-t0))s"; continue; }
    fi
    echo "FAIL($rc)  — $LOGDIR/$tag.log"; fail=1; failed+=("$tag")
  fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "== affected modules GREEN (${#TOBUILD[@]}).  ⚠ NOT a sweep — run tools/sweep.sh before committing."
else
  echo "== ${#failed[@]} FAILED: ${failed[*]}"; exit 1
fi
