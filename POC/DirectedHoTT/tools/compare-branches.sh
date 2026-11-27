#!/usr/bin/env bash
# ============================================================================
# Compare two versions of the POC module by module: wall time AND memory.
#
# Usage (from anywhere in the repo):
#   POC/DirectedHoTT/tools/compare-branches.sh [BASE] [CAND] [OUTDIR]
#     BASE    default dt-dhott-poc
#     CAND    default spike-generic-syntax
#     OUTDIR  default ~/.cache/once-lang5-compare/<BASE>-vs-<CAND>
#
# Meant to run OFFLINE, on a quiet machine (overnight): every module of each
# ref is checked cold, one per Agda process, ONE REF AFTER THE OTHER.
#
# Each side is `tools/agda-profile-modules.py --ref <ref>` (this checkout's
# copy, so both refs are measured by the same profiler): the ref's POC tree is
# staged by `git archive` with an empty `_build`, every module is checked in
# its own process under the cgroup cap, and wall time, peak RSS, max
# residency, allocation and the RTS rung that worked are recorded. It WAITS
# while another session's agda runs, so a busy machine delays the run instead
# of distorting it, and a rerun RESUMES (rows keyed by content).
#
# Then OUTDIR/compare.md joins the two `profile.tsv`:
#   * totals (wall, and the sum of peaks as a crude memory total);
#   * modules beyond the noise floor, for wall time and for peak RSS
#     (defaults ±12%, and at least 2 s / 100 MB: one sample each);
#   * modules that needed the compacting collector on one side only;
#   * modules only in one version (the switch may delete or add modules);
#   * failures, OOMs and blocked modules;
#   * every module, by wall-time change.
#
# Options (environment):
#   NOISE=0.12  MINS=2  MINMB=100   the noise floor
#   ONLY=base|cand                  measure one side only (the other is reused)
#   ONLY=report                     measure nothing; rebuild compare.md
#   PROFILE_MEM_MAX, PROFILE_SWAP_MAX, PROFILE_RTS   passed to the profiler
#
# Nothing in your checkout is touched; the staged trees stay in OUTDIR.
# ============================================================================
set -uo pipefail

BASE="${1:-dt-dhott-poc}"
CAND="${2:-spike-generic-syntax}"
HERE="$(cd "$(dirname "$0")" && pwd)"
PROF="$HERE/agda-profile-modules.py"
lab() { echo "${1//[^A-Za-z0-9._-]/_}"; }
OUT="${3:-$HOME/.cache/once-lang5-compare/$(lab "$BASE")-vs-$(lab "$CAND")}"
mkdir -p "$OUT"

side() {
  local ref="$1" w="$OUT/$(lab "$1")"
  echo "== measuring $ref -> $w/profile.tsv (log $w.log)"
  "$PROF" --ref "$ref" --work "$w" > "$w.log" 2>&1
  echo "   profiler exit $? ($(grep -c . "$w/profile.tsv" 2>/dev/null || echo 0) rows)"
}

case "${ONLY:-}" in
  base)   side "$BASE" ;;
  cand)   side "$CAND" ;;
  report) ;;
  *)      side "$BASE"; side "$CAND" ;;
esac

python3 - "$OUT/$(lab "$BASE")/profile.tsv" "$OUT/$(lab "$CAND")/profile.tsv" "$BASE" "$CAND" \
         "${NOISE:-0.12}" "${MINS:-2}" "${MINMB:-100}" > "$OUT/compare.md" <<'PY'
import sys, os
pb, pc, B, C, noise, mins, minmb = sys.argv[1:8]
noise, mins, minmb = float(noise), float(mins), float(minmb)
def load(p):
    rows = {}
    if not os.path.exists(p): return rows
    L = open(p, encoding='utf-8').read().splitlines()
    if not L: return rows
    head = L[0].split('\t')
    for l in L[1:]:
        v = l.split('\t')
        if len(v) == len(head): rows[v[0]] = dict(zip(head, v))
    return rows
def num(r, k):
    try: return float(r.get(k) or 0)
    except ValueError: return 0.0
b, c = load(pb), load(pc)
print(f"# Module by module: `{B}` vs `{C}`\n")
print(f"- `{B}`: {len(b)} rows ({pb})\n- `{C}`: {len(c)} rows ({pc})")
print(f"- noise floor: ±{noise:.0%}, and at least {mins:g} s / {minmb:g} MB (one sample each)\n")
both = sorted(m for m in b if m in c and b[m]['status'] == 'ok' and c[m]['status'] == 'ok')
def beyond(x, y, floor):
    return abs(y - x) >= floor and x > 0 and abs(y / x - 1) > noise
tw = (sum(num(b[m], 'wall_s') for m in both), sum(num(c[m], 'wall_s') for m in both))
tr = (sum(num(b[m], 'maxrss_mb') for m in both), sum(num(c[m], 'maxrss_mb') for m in both))
pk = (max([num(b[m], 'maxrss_mb') for m in both] or [0]), max([num(c[m], 'maxrss_mb') for m in both] or [0]))
pct = lambda x, y: f"{(y / x - 1):+.1%}" if x else "n/a"
print(f"## Totals over the {len(both)} modules measured in both\n")
print(f"| | `{B}` | `{C}` | change |\n|---|---|---|---|")
print(f"| wall (s) | {tw[0]:.0f} | {tw[1]:.0f} | {tw[1]-tw[0]:+.0f} ({pct(*tw)}) |")
print(f"| sum of peak RSS (MB) | {tr[0]:.0f} | {tr[1]:.0f} | {tr[1]-tr[0]:+.0f} ({pct(*tr)}) |")
print(f"| largest peak RSS (MB) | {pk[0]:.0f} | {pk[1]:.0f} | {pk[1]-pk[0]:+.0f} |\n")
for title, key, floor, unit in (("Wall time", 'wall_s', mins, 's'), ("Peak RSS", 'maxrss_mb', minmb, 'MB')):
    rows = []
    for m in both:
        x, y = num(b[m], key), num(c[m], key)
        if beyond(x, y, floor): rows.append((y - x, m, x, y))
    rows.sort(key=lambda z: -z[0])
    print(f"## {title} beyond the noise floor ({len(rows)})\n")
    if not rows: print("(none)\n"); continue
    print(f"| module | `{B}` {unit} | `{C}` {unit} | change | ratio |\n|---|---|---|---|---|")
    for d, m, x, y in rows:
        print(f"| {m} | {x:.0f} | {y:.0f} | {d:+.0f} | {y / x:.2f}× {'WORSE' if d > 0 else 'better'} |")
    print()
rung = [m for m in both if b[m]['rung'] != c[m]['rung']]
print(f"## Collector rung differs ({len(rung)})\n")
print('\n'.join(f"- {m}: `{B}` {b[m]['rung']}, `{C}` {c[m]['rung']}" for m in rung) or "(none)")
ob = sorted(m for m in b if m not in c); oc = sorted(m for m in c if m not in b)
print(f"\n## Only in one version\n\n- only in `{B}` ({len(ob)}): " + (', '.join(ob) or '—'))
print(f"- only in `{C}` ({len(oc)}): " + (', '.join(oc) or '—'))
print("\n## Not ok (failed, OOM, blocked)\n")
for n, d in ((B, b), (C, c)):
    bad = sorted(f"{m} ({r['status']})" for m, r in d.items() if r['status'] != 'ok')
    print(f"- `{n}`: " + (', '.join(bad) or '—'))
print(f"\n## Every module measured in both, by wall-time change\n")
print(f"| module | wall `{B}` | wall `{C}` | Δ s | rss `{B}` | rss `{C}` | Δ MB |\n|---|---|---|---|---|---|---|")
for m in sorted(both, key=lambda m: num(b[m], 'wall_s') - num(c[m], 'wall_s')):
    x, y, p, q = num(b[m], 'wall_s'), num(c[m], 'wall_s'), num(b[m], 'maxrss_mb'), num(c[m], 'maxrss_mb')
    print(f"| {m} | {x:.0f} | {y:.0f} | {y-x:+.0f} | {p:.0f} | {q:.0f} | {q-p:+.0f} |")
PY
echo "== report: $OUT/compare.md"
