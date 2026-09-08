#!/usr/bin/env bash
# ============================================================================
# DirectedHoTT sweep — builds THE LIVE PATH ONLY.
#
# ★ WHAT IS AND IS NOT BUILT, AND WHY THAT IS THE POINT.
#   Spec/ Metatheory/ Algorithm/ Lib/ Examples/ Trust/       -> BUILT
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

# ============================================================================
# ★★★ DISK GUARDRAIL — REFUSE TO SWEEP WITHOUT UNALLOCATED SPACE.
#
# 2026-09-07: a sweep took the WHOLE FILESYSTEM READ-ONLY, mid-run, and the
# session's uncommitted work had to be rescued to a USB stick.  btrfs could
# not carve a new METADATA chunk, aborted the transaction, and remounted ro:
#
#     Device size:        106.42 GiB
#     Device allocated:   106.42 GiB
#     Device unallocated:      1.00 MiB   <-- the actual problem
#     Free (estimated):    12.92 GiB      <-- what `df` shows; MISLEADING
#
# ⚠ `df` IS THE WRONG NUMBER, AND IT LOOKED FINE.  13 GiB "free" was free
#   space INSIDE already-allocated chunks.  A new chunk can only come from
#   UNALLOCATED space, so that is what this checks.  Checking `df` here
#   would have passed happily on the very run that broke the filesystem.
#
# ⚠ THE ABORT IS NOT RECOVERABLE IN-PLACE.  After it, btrfs refuses a rw
#   remount for the rest of the boot BY DESIGN (`state EMA`), so a reboot is
#   required, and then a `btrfs balance` — a reboot alone leaves unallocated
#   at ~1 MiB and it happens again.  That is why this is a PRE-flight check:
#   there is no cheap repair once a sweep has tripped it.
#
# ★ WHY A SWEEP IS THE TRIGGER: it rewrites ~470 `.agdai` interfaces
#   (~172 MB in `bootstrap/_build`).  That is exactly the data+metadata
#   churn that needs fresh chunks on a disk already near full.
#
# ⚠⚠ THIS MUST EXIT NON-ZERO.  A refusal that exits 0 is indistinguishable
#   from a passing sweep — the same hazard as `sweep-refusal-exits-zero`,
#   where a refused sweep was read as ALL GREEN and ~300 lines went
#   unverified.  Exit 3, distinct from 2 (check-trust) and 1 (a real FAIL).
#
# Not btrfs, or `btrfs` not installed?  Skip silently — the check is
# advisory infrastructure, not a proof obligation.  Override the threshold
# with SWEEP_MIN_UNALLOC (bytes), or set SWEEP_SKIP_DISK_CHECK=1 to bypass.
# ============================================================================
check_disk() {
  [ -n "${SWEEP_SKIP_DISK_CHECK:-}" ] && return 0
  command -v btrfs >/dev/null 2>&1 || return 0
  [ "$(stat -f -c %T "$BOOT" 2>/dev/null)" = "btrfs" ] || return 0

  # `btrfs filesystem usage -b` works unprivileged: it warns on stderr that
  # per-device detail needs root, but the Overall section — which is all we
  # want — still prints.  Hence 2>/dev/null, not a sudo call.
  local unalloc min
  unalloc="$(btrfs filesystem usage -b "$BOOT" 2>/dev/null \
             | awk '/Device unallocated:/ {gsub(/[^0-9]/,"",$3); print $3; exit}')"
  [ -n "$unalloc" ] || return 0          # unparseable -> do not block the sweep

  min="${SWEEP_MIN_UNALLOC:-1073741824}" # 1 GiB
  if [ "$unalloc" -lt "$min" ]; then
    echo "== REFUSING TO SWEEP — btrfs is nearly out of UNALLOCATED space." >&2
    echo "   unallocated: $((unalloc/1024/1024)) MiB   (need >= $((min/1024/1024)) MiB)" >&2
    echo "   NOTE: \`df\` will look fine; its free space is inside chunks" >&2
    echo "   already allocated, and a new chunk cannot come from there." >&2
    echo "   Sweeping now risks forcing the filesystem READ-ONLY mid-run." >&2
    echo "   Fix:  sudo btrfs balance start -dusage=0  /   # then -dusage=50" >&2
    echo "         sudo btrfs filesystem usage /           # confirm it rose" >&2
    echo "   Bypass (you have been warned): SWEEP_SKIP_DISK_CHECK=1" >&2
    exit 3
  fi
  echo "-- disk ok: $((unalloc/1024/1024/1024)) GiB unallocated"
}

is_red()  { head -40 "$1" | grep -q 'IS \*\*RED\*\*'; }
needs_c() { head -40 "$1" | grep -qi 'COMPACTING COLLECTOR'; }

# ============================================================================
# ★★★ BUILD ORDER IS BOTTOM-UP: LEAVES FIRST, TOPOLOGICALLY.
#
# ⚠⚠ THE OLD ORDER WAS "RTS-SPECIAL FIRST", AND IT WAS THE WORST POSSIBLE
#   ONE.  Modules whose header asks for the compacting collector are the
#   HEAVIEST in the tree — and putting them first meant each one ran when
#   NOTHING was warm, so a single agda process had to type-check the whole
#   cold import closure in one address space.  On 2026-09-07 that killed
#   seven modules in a row (JudgeWfAA..AG, all 143) on a 7.5 GB box; the
#   process died every time at the same place, `Checking …Knot.JudgeWfZ`
#   — a DEPENDENCY that had not been built yet.
#
# ★ THE FIX IS ORDERING, NOT FLAGS.  Agda writes an interface per module.
#   If every dependency already has its `.agdai`, the process checking a
#   module deserialises them and type-checks ONE module's worth of new
#   work.  Peak memory then tracks the biggest SINGLE module rather than
#   the biggest CLOSURE — which is the quantity that was blowing up.
#   Same total work, same modules, spread across processes instead of
#   piled into the first one.  See `sweep-first-module-eats-the-closure`.
#
# ★ This also makes the per-module timings mean something.  Before, the
#   first module in a cold tree absorbed its whole closure (2295s once,
#   against 5s for a bigger sibling) and the <10s target was noise.  Now
#   each number is that module's own cost.
#
# ⚠ Ordering does NOT reduce total work and is not a substitute for the
#   RTS ladder — a single module can still be too big for the box.  It
#   removes the ARTIFICIAL peak created by build order, nothing more.
#
# Deps come from the import lines; only imports INSIDE the build set
# constrain the order (stdlib/`normalizer`/`Once` are outside it and get
# built once, by whoever reaches them first).  Agda forbids import cycles,
# so this is a DAG; if one ever appears, we emit the stragglers in name
# order rather than dropping them — a sweep that silently skipped modules
# would be `verification-that-covers-less-than-it-claims` all over again.
# ============================================================================
toposort() {
  [ "$#" -eq 0 ] && return 0
  BOOT="$BOOT" python3 -c '
import os, re, sys, heapq
boot = os.environ["BOOT"]
rels = sys.argv[1:]
inset = set(rels)
mod2rel = {r[:-5].replace("/", "."): r for r in rels}
imp = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)")
deps, rdeps, indeg = {}, {}, {}
for r in rels:
    d = set()
    try:
        with open(os.path.join(boot, r), encoding="utf-8") as fh:
            for line in fh:
                m = imp.match(line)
                if m:
                    t = mod2rel.get(m.group(1))
                    if t is not None and t != r:
                        d.add(t)
    except OSError:
        pass
    deps[r] = d
    indeg[r] = len(d)
for r, d in deps.items():
    for t in d:
        rdeps.setdefault(t, []).append(r)
ready = [r for r in rels if indeg[r] == 0]
heapq.heapify(ready)
out = []
while ready:
    r = heapq.heappop(ready)
    out.append(r)
    for c in sorted(rdeps.get(r, [])):
        indeg[c] -= 1
        if indeg[c] == 0:
            heapq.heappush(ready, c)
if len(out) < len(rels):
    left = sorted(set(rels) - set(out))
    print("WARNING: import cycle — %d module(s) not ordered" % len(left),
          file=sys.stderr)
    out.extend(left)
print("\n".join(out))
' "$@"
}


# ============================================================================
# ★★★ THE GENERATED TREE MUST BE THE GENERATOR'S OWN OUTPUT.
#
# ⚠⚠ A GREEN SWEEP DID NOT COVER THIS, AND THAT WAS MEASURED, NOT FEARED.
#   On 2026-09-08 a commit passed ALL GREEN over 291 modules while leaving
#   `gen-knot.py` UNABLE TO RUN: a retrofit moved two lemma bodies so they
#   no longer mentioned `ielim KnotD`, their `_WRAP_LEDGER` entries went
#   stale, and the generator asserts on a stale entry.  The sweep
#   type-checks the tree and never invokes the generator, so nothing
#   noticed until someone regenerated by hand.
#
# ★ SO THIS CHECKS TWO THINGS A TYPE-CHECK CANNOT:
#     1. the generator still RUNS (its own assertions hold — the ledger
#        is the important one: it is what asks for adequacy proofs);
#     2. the tree on disk IS what the generator emits, i.e. nobody has
#        edited a file whose header says "GENERATED — do not edit".
#   Both are `verification-that-covers-less-than-it-claims`: green, and
#   quietly covering less than it says.
#
# ⚠⚠ IT MUST NOT DESTROY A HAND EDIT WHILE DETECTING ONE.  The naive
#   version — regenerate, then diff — OVERWRITES the very edit it is
#   trying to report.  So: snapshot the generated set, regenerate,
#   compare, and RESTORE THE SNAPSHOT before failing.  The tree is left
#   exactly as it was found; the report says what differed.
#
# Skip with SWEEP_SKIP_GEN_CHECK=1 (e.g. mid-edit on the generator).
# ============================================================================
check_generated() {
  [ -n "${SWEEP_SKIP_GEN_CHECK:-}" ] && return 0
  command -v python3 >/dev/null 2>&1 || return 0
  [ -f "$ROOT/tools/gen-knot.py" ] || return 0

  local snap rc=0
  snap="$(mktemp -d)"
  # the generated set: every file that says so, plus the Trust roots
  ( cd "$BOOT" && grep -rl 'GENERATED by tools/gen-knot.py' --include='*.agda' \
       DirectedHoTT 2>/dev/null; ls DirectedHoTT/Trust/*.agda 2>/dev/null ) \
    | sort -u > "$snap/list"
  while IFS= read -r rel; do
    mkdir -p "$snap/tree/$(dirname "$rel")"
    cp "$BOOT/$rel" "$snap/tree/$rel"
  done < "$snap/list"

  if ! ( cd "$BOOT" && python3 "$ROOT/tools/gen-knot.py" >"$snap/gen.log" 2>&1 \
         && "$ROOT/tools/gen-trust.sh" >>"$snap/gen.log" 2>&1 ); then
    echo "== REFUSING TO SWEEP — the generator does not run." >&2
    tail -5 "$snap/gen.log" | sed 's/^/   /' >&2
    echo "   ⚠ A stale \`_WRAP_LEDGER\` entry does this: a body that no" >&2
    echo "     longer mentions \`ielim KnotD\` stops being scanned, and the" >&2
    echo "     generator asserts rather than quietly asking for less." >&2
    rc=4
  else
    # anything the regeneration CHANGED, plus anything it newly emitted
    local changed=""
    while IFS= read -r rel; do
      cmp -s "$BOOT/$rel" "$snap/tree/$rel" || changed="$changed $rel"
    done < "$snap/list"
    if [ -n "$changed" ]; then
      echo "== REFUSING TO SWEEP — the tree is not the generator's output." >&2
      for f in $changed; do echo "   differs: $f" >&2; done
      echo "   Either the generator was not re-run after a change to its" >&2
      echo "   input, or a GENERATED file was hand-edited.  Both make the" >&2
      echo "   sweep verify something the generator would not produce." >&2
      rc=5
    fi
  fi

  # ★ RESTORE UNCONDITIONALLY.  Detecting a hand edit must not delete it.
  while IFS= read -r rel; do cp "$snap/tree/$rel" "$BOOT/$rel"; done < "$snap/list"
  rm -rf "$snap"
  [ "$rc" -eq 0 ] || exit "$rc"
  echo "-- generated tree is current"
}

echo "== DirectedHoTT sweep"
check_disk
check_generated
"$ROOT/tools/check-trust.sh" || exit 2

declare -a RED=() TOBUILD=() MAIN=() CMP=()
while IFS= read -r f; do
  rel="${f#$BOOT/}"
  case "$rel" in DirectedHoTT/Negative/*) [ "$WITH_NEG" -eq 1 ] || continue ;; esac
  if is_red "$f"; then RED+=("$rel"); continue; fi
  case "$rel" in DirectedHoTT/Comparison/*) CMP+=("$rel"); continue ;; esac
  MAIN+=("$rel")
done < <(find "$ROOT" -name '*.agda' | sort)

# Comparison/ is ordered too, but stays LAST: it is reported apart, and a
# benchmark must never delay the modules the sweep actually verifies.
mapfile -t MAIN < <(toposort "${MAIN[@]:-}")
mapfile -t CMP  < <(toposort "${CMP[@]:-}")
TOBUILD=("${MAIN[@]:-}" "${CMP[@]:-}")

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
    # ★★★ THE RUNGS ARE A LADDER, AND EVERY MODULE ENTERS IT SOMEWHERE.
    #
    # ⚠⚠ FIXED 2026-09-07: this used to read
    #        if [ "$rc" = 143 ] && [ "$rts" = "-A64m" ]
    #   — so a module whose HEADER asks for the compacting collector
    #   entered at `-A64m -c` and got NO RETRY AT ALL, not even the
    #   `-A8m -c` rung that exists precisely for closure-heavy modules.
    #   It failed on its first kill.  That is exactly backwards: the
    #   modules that ask for `-c` are the ones most likely to need the
    #   rung below it.  A whole sweep died this way — JudgeWfAA..AG, all
    #   143, none retried, because all seven carry the `-c` header.
    #
    # ★ So the ladder is now a LIST, and a module resumes it from
    #   wherever its header put it.  A module at `-A64m` still gets both
    #   remaining rungs; one at `-A64m -c` gets the last one.
    #
    # ⚠ A non-143 failure STOPS the descent.  Climbing down the ladder is
    #   only meaningful for kills — retrying a type error at a smaller
    #   nursery just burns minutes to reprint the same error.
    LADDER=("-A64m" "-A64m -c" "-A8m -c")
    start=0
    for i in "${!LADDER[@]}"; do [ "${LADDER[$i]}" = "$rts" ] && start=$i; done
    if [ "$rc" = 143 ]; then
      for ((i=start+1; i<${#LADDER[@]}; i++)); do
        next="${LADDER[$i]}"
        printf 'KILLED(143) — retrying at %s ... ' "$next"
      # ⚠ NOT `if … then … fi; rc=$?`.  After an `if` whose condition
      #   FAILED and which has no `else`, `$?` is the status of the `if`
      #   STATEMENT — which is 0.  That reported a second memory kill as
      #   `FAIL(0)`, i.e. as a PROOF ERROR, and cost a session's worth of
      #   chasing a module that checks clean on its own.  Capture the
      #   retry's own status, then branch on it.
        AGDA_RTS="$next" "$CHECK" "$rel" >"$LOGDIR/$tag.log" 2>&1
        rc=$?
        if [ "$rc" = 0 ]; then
          d=$((SECONDS-t0)); TIMES+=("$d $tag"); echo "ok ($next) ${d}s"; break
        fi
        [ "$rc" = 143 ] || break
      done
      [ "$rc" = 0 ] && continue
    fi

    # ---- HISTORY OF THE LAST RUNG (kept: it explains the -A8m choice) ----
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
    #   the opposite trade.
    #
    # ⚠⚠ HISTORICAL: this rung was added for `Trust.agda`, which imported
    #   all 239 modules and type-checked nothing.  That module is GONE —
    #   split into the `Trust/` roots on 2026-09-05, because no RTS
    #   setting could build it once `Knot/RenAgree` landed (`-A64m`,
    #   `-A64m -c` all OOM-killed; `-A8m -c` still grinding at 10 min on
    #   a QUIET box with 4.8 GB free).  ⇒ the rung stays as cheap
    #   insurance, but its original customer was fixed by ARCHITECTURE,
    #   not by a flag — which is the better repair whenever it is
    #   available.
    #
    # ★ So the last resort shrinks the allocation area.  It costs
    #   nothing when the first two rungs work, and it is the rung that
    #   the one module with the largest import closure actually needs.
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
