#!/usr/bin/env bash
#
# codegen-measure.sh — what the emitted code costs, per corpus program
# (MERGE.md §1 "Emitted code and its cost"; §4 re-runs it after the rebase).
#
#   tests/codegen-measure.sh measure OUTDIR [ONCE]     # OUTDIR/costs.tsv + totals
#   tests/codegen-measure.sh compare A.tsv B.tsv       # totals, and every program that got worse
#   tests/codegen-measure.sh same ONCE_A ONCE_B OUTDIR # are the binaries byte-identical, per arch?
#
# Columns of costs.tsv, one row per corpus program (compiler/test, examples, tests):
#   ir          IR tokens after `once optimize`
#   instrs heap-sites heap-cells frames frame-max frame-sum
#               static costs of the program image (`once stats`, `Once.Measure`): the
#               same on every arch; a site counts once however often it runs
#   text-<arch> .text bytes of the linked binary, x86_64 / x86_32 / riscv64
# A program that does not build on an arch has `NA` there. Run-time counts are
# plan 0.130. Flags: MEASURE_FLAGS (default `--alloc heap`); ONCE defaults to
# the cabal-built compiler. riscv64 needs the cross binutils
# (riscv64-unknown-linux-gnu-{as,ld,objcopy}); without them its column is NA.

set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STRATA="$ROOT/Strata"
FLAGS="${MEASURE_FLAGS:---alloc heap}"
ARCHES=(x86_64 x86_32 riscv64)
RV="riscv64-unknown-linux-gnu"

die() { echo "codegen-measure: $*" >&2; exit 2; }
default_once() { (cd "$ROOT/compiler" && cabal list-bin once 2>/dev/null); }

corpus() {
  for f in "$ROOT"/compiler/test/*.once "$ROOT"/examples/*.once "$ROOT"/tests/*.once; do
    [ -f "$f" ] && echo "$f"
  done
}

# build ONCE ARCH FILE OUT — a binary at OUT, or nothing
build() {
  local once=$1 arch=$2 f=$3 out=$4
  if [ "$arch" = riscv64 ]; then
    command -v "$RV-as" >/dev/null || return 1
    AS="$RV-as" LD="$RV-ld" OBJCOPY="$RV-objcopy" \
      "$once" build --target "$arch" $FLAGS --strata "$STRATA" "$f" -o "$out" >/dev/null 2>&1
  else
    "$once" build --target "$arch" $FLAGS --strata "$STRATA" "$f" -o "$out" >/dev/null 2>&1
  fi
}

# text-size FILE — the ELF's .text size in bytes (any arch, 32 or 64 bit)
text_size() {
  python3 -I - "$1" <<'PY'
import struct, sys
d = open(sys.argv[1], 'rb').read()
if d[:4] != b'\x7fELF': print('NA'); sys.exit()
b64, le = d[4] == 2, d[5] == 1
e = '<' if le else '>'
if b64:
    shoff, = struct.unpack_from(e + 'Q', d, 0x28); shentsize, shnum, shstrndx = struct.unpack_from(e + 'HHH', d, 0x3A)
else:
    shoff, = struct.unpack_from(e + 'I', d, 0x20); shentsize, shnum, shstrndx = struct.unpack_from(e + 'HHH', d, 0x2E)
def sec(i):
    o = shoff + i * shentsize
    if b64:
        name, = struct.unpack_from(e + 'I', d, o); off, size = struct.unpack_from(e + 'QQ', d, o + 0x18)
    else:
        name, = struct.unpack_from(e + 'I', d, o); off, size = struct.unpack_from(e + 'II', d, o + 0x10)
    return name, off, size
_, stroff, _ = sec(shstrndx)
for i in range(shnum):
    name, _, size = sec(i)
    n = d[stroff + name:d.index(b'\0', stroff + name)]
    if n == b'.text': print(size); sys.exit()
print('NA')
PY
}

measure() {
  local out once=${2:-$(default_once)}
  out=$(realpath -m "$1")
  [ -x "$once" ] || die "no once binary (cd compiler && cabal build exe:once)"
  mkdir -p "$out/bin"
  local tsv="$out/costs.tsv"
  printf 'program\tir\tinstrs\theap-sites\theap-cells\tframes\tframe-max\tframe-sum' > "$tsv"
  for a in "${ARCHES[@]}"; do printf '\ttext-%s' "$a" >> "$tsv"; done
  printf '\n' >> "$tsv"
  while read -r f; do
    local n; n=$(basename "$f" .once)
    local ir; ir=$( (cd "$ROOT" && "$once" optimize "$f") 2>/dev/null | grep '^  = ' \
                    | grep -oE "[A-Za-z_][A-Za-z0-9_.'-]*|<|\[|-?[0-9]+" | wc -l)
    local st; st=$( (cd "$ROOT" && "$once" stats "$f") 2>/dev/null )
    local row="$n	$ir"
    for k in instrs heap-sites heap-cells frames frame-max frame-sum; do
      local v; v=$(printf '%s\n' "$st" | awk -v k="$k" '$1==k{print $2}')
      row="$row	${v:-NA}"
    done
    for a in "${ARCHES[@]}"; do
      local bin="$out/bin/$n.$a"
      rm -f "$bin"
      if (cd "$out/bin" && build "$once" "$a" "$f" "$bin") && [ -f "$bin" ]; then
        row="$row	$(text_size "$bin")"
      else
        row="$row	NA"
      fi
    done
    printf '%s\n' "$row" >> "$tsv"
  done < <(corpus)
  totals "$tsv"
}

# totals TSV — the column sums over the programs that have a number there
totals() {
  awk -F'\t' 'NR==1{for(i=2;i<=NF;i++)h[i]=$i; nf=NF; next}
              {for(i=2;i<=NF;i++) if($i!="NA"){s[i]+=$i; c[i]++}}
              END{for(i=2;i<=nf;i++) printf "%s=%d (%d programs)\n", h[i], s[i], c[i]}' "$1"
}

# compare A B — totals side by side, then each program and column that grew
compare() {
  local a=$1 b=$2
  echo "== totals: $a -> $b"
  paste <(totals "$a") <(totals "$b") | awk -F'\t' '{print "  " $1 "  ->  " $2}'
  echo "== worse (program column before after)"
  awk -F'\t' 'FNR==1{next} NR==FNR{for(i=2;i<=NF;i++)v[$1,i]=$i; next}
              {for(i=2;i<=NF;i++){o=v[$1,i]; if(o!="" && o!="NA" && $i!="NA" && $i+0>o+0) print "  " $1, i, o, $i}}' \
      "$a" "$b" | while read -r p i o n; do
        printf '  %s %s %s %s\n' "$p" "$(head -1 "$a" | cut -f"$i")" "$o" "$n"
      done
}

# same ONCE_A ONCE_B OUT — byte identity of every binary, per arch
same() {
  local A=$1 B=$2 out
  out=$(realpath -m "$3")
  mkdir -p "$out/a" "$out/b"
  for arch in "${ARCHES[@]}"; do
    local s=0 d=0 nb=0 diffs=()
    while read -r f; do
      local n; n=$(basename "$f" .once)
      rm -f "$out/a/$n" "$out/b/$n"
      (cd "$out/a" && build "$A" "$arch" "$f" "$out/a/$n")
      (cd "$out/b" && build "$B" "$arch" "$f" "$out/b/$n")
      if [ -f "$out/a/$n" ] && [ -f "$out/b/$n" ]; then
        if cmp -s "$out/a/$n" "$out/b/$n"; then s=$((s+1)); else d=$((d+1)); diffs+=("$n"); fi
      elif [ -f "$out/a/$n" ] || [ -f "$out/b/$n" ]; then
        d=$((d+1)); diffs+=("$n (builds on one side only)")
      else nb=$((nb+1)); fi
    done < <(corpus)
    echo "$arch: same=$s differ=$d nobuild=$nb"
    for x in "${diffs[@]}"; do echo "  $x"; done
  done
}

case "${1:-}" in
  measure) shift; [ $# -ge 1 ] || die "measure OUTDIR [ONCE]"; measure "$@" ;;
  compare) shift; [ $# -eq 2 ] || die "compare A.tsv B.tsv"; compare "$@" ;;
  same)    shift; [ $# -eq 3 ] || die "same ONCE_A ONCE_B OUTDIR"; same "$@" ;;
  *) sed -n '3,20p' "$0"; exit 2 ;;
esac
