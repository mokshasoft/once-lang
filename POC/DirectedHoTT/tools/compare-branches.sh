#!/usr/bin/env bash
# ============================================================================
# Compare two versions of the POC module by module: COLD sweep times.
#
# Usage (from anywhere in the repo):
#   POC/DirectedHoTT/tools/compare-branches.sh [BASE] [CAND] [OUTDIR]
#     BASE    default dt-dhott-poc
#     CAND    default spike-generic-syntax
#     OUTDIR  default ~/.cache/once-lang5-compare/<BASE>-vs-<CAND>
#
# Meant to run OFFLINE, on a quiet machine (overnight): two cold sweeps of
# about an hour each, ONE AFTER THE OTHER (two agda builds at once OOM-kill
# each other, see LESSONS / the memory notes).
#
# For each ref:
#   * a git worktree at OUTDIR/wt/<ref>, detached at the ref, with an EMPTY
#     `POC/_build`, so the sweep is cold (its stamps live in `_build`);
#   * the ref's OWN `tools/sweep.sh` (the two module sets differ), run under
#     this checkout's `tools/mem-guard.sh`: it yields to other agda jobs and
#     restarts by itself, and the sweep's content-keyed stamps make a
#     restart resume instead of start over;
#   * its own TMPDIR, because the sweep writes per-module logs to
#     `${TMPDIR:-/tmp}/dhott-sweep` and the two runs must not share it.
#
# Then the per-module times are joined into OUTDIR/compare.md:
#   * every module in both, sorted by the change, flagged where the change is
#     beyond the noise floor (default ±12%, and at least 2 s: one sample each,
#     and a 3 s module moves by a second for nothing);
#   * modules only in one version (the switch may delete or add modules);
#   * failures, kills and refusals (a refused sweep EXITS 0: the ALL GREEN
#     line is what counts, not the exit code);
#   * totals.
#
# Options (environment):
#   NOISE=0.12  MINDELTA=2    the noise floor
#   SKIP_GEN=1                pass SWEEP_SKIP_GEN_CHECK=1 to both sweeps
#                             (the spike branch's generators may lag)
#   ONLY=cand|base            run one side only (e.g. to redo a failed run);
#                             the other side's earlier result is reused
#   ONLY=report               run no sweep; rebuild compare.md from the logs
#
# Nothing is committed or pushed; the worktrees are left for inspection
# (`git worktree remove OUTDIR/wt/<ref>` to delete them).
# ============================================================================
set -uo pipefail

BASE="${1:-dt-dhott-poc}"
CAND="${2:-spike-generic-syntax}"
REPO="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
OUT="${3:-$HOME/.cache/once-lang5-compare/${BASE//\//_}-vs-${CAND//\//_}}"
GUARD="$REPO/POC/DirectedHoTT/tools/mem-guard.sh"
NOISE="${NOISE:-0.12}"; MINDELTA="${MINDELTA:-2}"
mkdir -p "$OUT/wt"

side() {  # side REF -> runs a cold sweep of REF, writes OUT/<name>.{sweep.log,times.tsv}
  local ref="$1" name="${1//\//_}" wt="$OUT/wt/${1//\//_}"
  git -C "$REPO" rev-parse --verify --quiet "$ref^{commit}" >/dev/null \
    || { echo "== unknown ref: $ref" >&2; return 2; }
  if [ -d "$wt" ]; then
    git -C "$wt" checkout --quiet --detach "$ref" || return 2
  else
    git -C "$REPO" worktree add --quiet --detach "$wt" "$ref" || return 2
  fi
  rm -rf "$wt/POC/_build"                        # COLD: interfaces and stamps
  mkdir -p "$OUT/$name.tmp"
  echo "== $ref ($(git -C "$wt" rev-parse --short HEAD)): cold sweep, log $OUT/$name.sweep.log"
  ( cd "$wt/POC" && TMPDIR="$OUT/$name.tmp" \
      ${SKIP_GEN:+SWEEP_SKIP_GEN_CHECK=1} \
      "$GUARD" "$OUT/$name.guard.log" -- ./DirectedHoTT/tools/sweep.sh ) \
    > "$OUT/$name.sweep.log" 2>&1
  echo "   sweep exit $?; $(grep -E '^== ' "$OUT/$name.sweep.log" | tail -1)"
  # per-module lines: "[ n/N] Tag   ok  12s ..." / "ok (-A8m -c) 12s" / FAILED / KILLED / BLOCKED
  python3 - "$OUT/$name.sweep.log" > "$OUT/$name.times.tsv" <<'PY'
import re, sys
pat = re.compile(r'\[\s*\d+/\d+\]\s+(\S+)\s+(.*)$')
for line in open(sys.argv[1], errors='replace'):
    m = pat.search(line)
    if not m: continue
    tag, rest = m.group(1), m.group(2)
    t = re.search(r'\bok\b(?:\s*\([^)]*\))?\s+(\d+)s', rest)
    if t:   print(f"{tag}\tok\t{t.group(1)}")
    elif 'cached' in rest:  print(f"{tag}\tcached\t")
    elif 'BLOCKED' in rest: print(f"{tag}\tblocked\t")
    else:   print(f"{tag}\tfailed\t")
PY
}

case "${ONLY:-}" in
  cand) side "$CAND" ;;
  base) side "$BASE" ;;
  report) ;;
  *)    side "$BASE"; side "$CAND" ;;
esac

python3 - "$OUT" "${BASE//\//_}" "${CAND//\//_}" "$BASE" "$CAND" "$NOISE" "$MINDELTA" > "$OUT/compare.md" <<'PY'
import sys, os
out, bn, cn, B, C, noise, mind = sys.argv[1:8]; noise = float(noise); mind = int(mind)
def load(n):
    d = {}
    p = os.path.join(out, n + '.times.tsv')
    if os.path.exists(p):
        for l in open(p):
            tag, st, s = (l.rstrip('\n').split('\t') + ['', ''])[:3]
            d[tag] = (st, int(s) if s else None)
    return d
b, c = load(bn), load(cn)
def last(n):
    p = os.path.join(out, n + '.sweep.log')
    if not os.path.exists(p): return '(no log)'
    ls = [l.strip() for l in open(p, errors='replace') if l.startswith('== ')]
    return ls[-1] if ls else '(no verdict line: refused or interrupted?)'
print(f"# Cold sweep, module by module: `{B}` vs `{C}`\n")
print(f"- `{B}`: {last(bn)}\n- `{C}`: {last(cn)}")
print(f"- noise floor: ±{noise:.0%} and at least {mind} s (one sample each)\n")
both = [t for t in b if t in c and b[t][0] == 'ok' and c[t][0] == 'ok']
rows = []
for t in both:
    x, y = b[t][1], c[t][1]
    d = y - x
    r = (y / x) if x else float('inf')
    flag = ''
    if abs(d) >= mind and x and abs(r - 1) > noise:
        flag = 'SLOWER' if d > 0 else 'faster'
    rows.append((d, t, x, y, r, flag))
rows.sort(key=lambda z: -z[0])
tb = sum(z[2] for z in rows); tc = sum(z[3] for z in rows)
print(f"## Totals over the {len(rows)} modules in both\n")
print(f"| | `{B}` | `{C}` | change |\n|---|---|---|---|")
print(f"| seconds | {tb} | {tc} | {tc - tb:+d} ({(tc / tb - 1) if tb else 0:+.1%}) |\n")
print("## Beyond the noise floor\n")
sig = [z for z in rows if z[5]]
if sig:
    print(f"| module | `{B}` s | `{C}` s | change | ratio |\n|---|---|---|---|---|")
    for d, t, x, y, r, f in sig:
        print(f"| {t} | {x} | {y} | {d:+d} | {r:.2f}× {f} |")
else:
    print("(none)")
print("\n## Only in one version\n")
ob = sorted(t for t in b if t not in c); oc = sorted(t for t in c if t not in b)
print(f"- only in `{B}` ({len(ob)}): " + (', '.join(ob) or '—'))
print(f"- only in `{C}` ({len(oc)}): " + (', '.join(oc) or '—'))
print("\n## Not measured (failed, blocked, cached)\n")
for n, d in ((B, b), (C, c)):
    bad = sorted(f"{t} ({v[0]})" for t, v in d.items() if v[0] != 'ok')
    print(f"- `{n}`: " + (', '.join(bad) or '—'))
print("\n## All modules in both, by change\n")
print(f"| module | `{B}` s | `{C}` s | change |\n|---|---|---|---|")
for d, t, x, y, r, f in rows:
    print(f"| {t} | {x} | {y} | {d:+d} |")
PY
echo "== report: $OUT/compare.md"
