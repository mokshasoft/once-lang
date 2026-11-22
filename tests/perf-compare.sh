#!/usr/bin/env bash
#
# perf-compare.sh — what the emitted code costs to run, and where its instructions go
# (plan 0.146 §5 item 8 b, D474). x86_64, native; needs `perf` (user-mode instructions retired).
#
#   tests/perf-compare.sh measure OUTDIR [ONCE]   # OUTDIR/perf.tsv, OUTDIR/bench.tsv
#   tests/perf-compare.sh compare A_DIR B_DIR     # totals, ratios, the benchmarks' growth
#   tests/perf-compare.sh master OUTDIR           # measure origin/master (a cached worktree) and this tree
#
# perf.tsv, one row per corpus program (compiler/test, examples, tests), run with empty stdin (5 s cap):
#   run         user instructions retired (NA: did not build, or no count)
#   text        .text bytes
#   static      emitted instructions in the assembly
#   checks slot-moves reg-moves heap-moves alloc-rec frames calls rets
#               emitted instructions by kind (a room check counts its cmp, jbe and call)
# bench.tsv, one row per bench/*.once at each size N (its `BENCH_N`):
#   run instructions retired, and the program's exit status (`exhausted` runs abort).
# A benchmark's growth with N is the point: doubling N should double `run`.

set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SIZES=(${BENCH_SIZES:-250 500 1000})
die() { echo "perf-compare: $*" >&2; exit 2; }
default_once() { (cd "$ROOT/compiler" && cabal list-bin once 2>/dev/null); }
command -v perf >/dev/null || die "needs perf"

# corpus DIR — the corpus programs of the tree at DIR
corpus() {
  for f in "$1"/compiler/test/*.once "$1"/examples/*.once "$1"/tests/*.once; do
    [ -f "$f" ] && echo "$f"
  done
}
key() { local r=${1#"$2"/}; r=${r%.once}; printf '%s' "${r//\//_}"; }

# run-count BIN — user instructions retired by BIN on empty stdin
run_count() {
  local n
  n=$(cd "$(dirname "$1")" && timeout 5 perf stat -x, -e instructions:u "./$(basename "$1")" </dev/null 2>&1 >/dev/null \
        | grep instructions | cut -d, -f1)
  case "$n" in ''|*[!0-9]*) echo NA ;; *) echo "$n" ;; esac
}

text_size() { size -A "$1" 2>/dev/null | awk '$1==".text"{print $2}'; }

# kinds ASM — the emitted instructions of an x86_64 assembly file, by kind
kinds() {
  grep -E '^    [a-z]' "$1" | awk '
    /call once_exhausted/ || (/cmpq/ && /%rsp/) || /jbe 1f/ {k["checks"]++; t++; next}
    /once_alloc_record/                        {k["alloc-rec"]++; t++; next}
    /^ *movq/ && /\(%rsp\)/                    {k["slot-moves"]++; t++; next}
    /^ *movq/ && /\(%r[a-z0-9]+\)/             {k["heap-moves"]++; t++; next}
    /^ *movq %r[a-z0-9]+, %r/                  {k["reg-moves"]++; t++; next}
    /^ *(sub|add)q \$[0-9]+, %rsp/             {k["frames"]++; t++; next}
    /^ *call/                                  {k["calls"]++; t++; next}
    /^ *ret/                                   {k["rets"]++; t++; next}
    {t++}
    END {printf "%d %d %d %d %d %d %d %d %d", t, k["checks"], k["slot-moves"], k["reg-moves"], k["heap-moves"], k["alloc-rec"], k["frames"], k["calls"], k["rets"]}'
}

# measure OUT ONCE TREE — the corpus of TREE built from TREE (its own libraries); this tree's benchmarks
measure() {
  local out=$1 once=$2 tree=$3 tmp; tmp=$(mktemp -d); mkdir -p "$out"
  printf 'program\trun\ttext\tstatic\tchecks\tslot-moves\treg-moves\theap-moves\talloc-rec\tframes\tcalls\trets\n' > "$out/perf.tsv"
  while read -r f; do
    cp "$f" "$tmp/p.once"; rm -f "$tmp/p" "$tmp/p.s"
    if (cd "$tree" && "$once" build --target x86_64 --exe "$tmp/p.once" -o "$tmp/p" --save-temps >/dev/null 2>&1); then
      printf '%s\t%s\t%s\t%s\n' "$(key "$f" "$tree")" "$(run_count "$tmp/p")" "$(text_size "$tmp/p")" "$(kinds "$tmp/p.s" | tr ' ' '\t')"
    else
      printf '%s\tNA\tNA\tNA\tNA\tNA\tNA\tNA\tNA\tNA\tNA\tNA\n' "$(key "$f" "$tree")"
    fi >> "$out/perf.tsv"
  done < <(corpus "$tree")
  printf 'bench\tN\trun\tstatus\n' > "$out/bench.tsv"
  for f in "$ROOT"/bench/*.once; do
    for n in "${SIZES[@]}"; do
      sed "s/BENCH_N/$n/" "$f" > "$tmp/b.once"; rm -f "$tmp/b"
      if (cd "$tree" && "$once" build --target x86_64 "$tmp/b.once" -o "$tmp/b" >/dev/null 2>&1); then
        (cd "$tmp" && timeout 60 ./b </dev/null >/dev/null 2>&1); st=$?
        printf '%s\t%s\t%s\t%s\n' "$(basename "$f" .once)" "$n" "$(run_count "$tmp/b")" "$st"
      else
        printf '%s\t%s\tNA\tNA\n' "$(basename "$f" .once)" "$n"
      fi >> "$out/bench.tsv"
    done
  done
  rm -rf "$tmp"
}

compare() {
  local a=$1 b=$2
  echo "== corpus, programs measured on both sides (totals; B/A)"
  python3 -I - "$a/perf.tsv" "$b/perf.tsv" <<'PY'
import sys, statistics
def load(p):
    rows = [l.rstrip('\n').split('\t') for l in open(p)]
    return rows[0], {r[0]: r[1:] for r in rows[1:]}
h, A = load(sys.argv[1]); _, B = load(sys.argv[2])
common = [k for k in A if k in B and 'NA' not in A[k] and 'NA' not in B[k]]
print(f"programs: {len(common)}")
for i, name in enumerate(h[1:]):
    sa = sum(int(A[k][i]) for k in common); sb = sum(int(B[k][i]) for k in common)
    r = f"{sb/sa:6.2f}x" if sa else "   new"
    print(f"  {name:11s} {sa:>12d} {sb:>12d} {r}")
rs = sorted(int(B[k][0]) / int(A[k][0]) for k in common if int(A[k][0]) > 0)
if rs: print(f"run ratio per program: min {rs[0]:.2f}x median {statistics.median(rs):.2f}x max {rs[-1]:.2f}x")
PY
  echo "== benchmarks (run at each N; status 0 = finished)"
  join -t$'\t' <(tail -n+2 "$a/bench.tsv" | awk -F'\t' '{print $1"@"$2"\t"$3"\t"$4}' | sort) \
               <(tail -n+2 "$b/bench.tsv" | awk -F'\t' '{print $1"@"$2"\t"$3"\t"$4}' | sort) \
    | sort -t@ -k1,1 -k2,2n | awk -F'\t' '{printf "  %-28s A %14s (st %s)   B %14s (st %s)\n", $1, $2, $3, $4, $5}'
}

case "${1:-}" in
  measure) [ $# -ge 2 ] || die "measure OUTDIR [ONCE]"; measure "$2" "${3:-$(default_once)}" "$ROOT" ;;
  compare) [ $# -eq 3 ] || die "compare A_DIR B_DIR"; compare "$2" "$3" ;;
  master)
    [ $# -eq 2 ] || die "master OUTDIR"
    git -C "$ROOT" fetch -q origin master || die "fetch failed"
    sha=$(git -C "$ROOT" rev-parse --short origin/master)
    wt="${XDG_CACHE_HOME:-$HOME/.cache}/once-perf/master-$sha"
    [ -d "$wt" ] || git -C "$ROOT" worktree add -q "$wt" "$sha" || die "worktree failed"
    (cd "$wt/compiler" && cabal build -v0 exe:once >/dev/null 2>&1) || die "master build failed"
    mone=$(cd "$wt/compiler" && cabal list-bin once)
    # master's corpus from master's tree; the benchmarks are this tree's
    measure "$2/master" "$mone" "$wt"; measure "$2/branch" "$(default_once)" "$ROOT"
    compare "$2/master" "$2/branch" ;;
  *) die "usage: measure OUTDIR [ONCE] | compare A_DIR B_DIR | master OUTDIR" ;;
esac
