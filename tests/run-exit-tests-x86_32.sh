#!/usr/bin/env bash
# x86-32 (i386) runtime regression net — mirror of run-exit-tests.sh.
#
# Builds each compiler/test/*.once that declares an expected exit code for
# --target x86_32 and runs the resulting static ELF under qemu-i386 (user
# mode), checking the process exit code. Plan 0.57 wired the i386 toolchain
# into the CLI (as --32 / ld -m elf_i386), so no AS/LD wrappers are needed.
#
# Requires: a host `as`/`ld` able to emit 32-bit objects and qemu-i386.
#
# Usage: tests/run-exit-tests-x86_32.sh ["<default build flags>"]
set -u
# Each test runs twice, without and with the optimizer; both runs must exit
# with the expected code and emit the same output (the optimizer keeps the
# trace, D347). Given build flags, each test runs once with exactly those.
if [ $# -ge 1 ]; then DEFAULT_PARAMS="$1"; OPTS=(""); else DEFAULT_PARAMS=""; OPTS=("--no-optimize" ""); fi
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TESTDIR="$ROOT/compiler/test"
STRATA="$ROOT/Strata"
BUILD="$(mktemp -d)"
ONCE="$(cd "$ROOT/compiler" && cabal list-bin once 2>/dev/null)"
[ -x "$ONCE" ] || { echo "no once binary (run: cd compiler && cabal build exe:once)"; exit 2; }
QEMU="${QEMU_I386:-qemu-i386}"
command -v "$QEMU" >/dev/null 2>&1 || { echo "no $QEMU (set QEMU_I386)"; exit 2; }

pass=0; fail=0; skip=0; declare -a failed=()
for f in "$TESTDIR"/*.once; do
  name="$(basename "$f" .once)"
  grep -qiE '^--.*\bPENDING\b' "$f" && { skip=$((skip+1)); echo "SKIP $name (PENDING)"; continue; }
  exp="$(grep -oiE 'expected.*exit (code )?[0-9]+|exit code [0-9]+' "$f" | grep -oE '[0-9]+' | head -1)"
  [ -z "$exp" ] && continue
  params="$(grep -oiE '^-- *params:.*' "$f" | sed -E 's/^-- *params: *//I' | head -1)"
  [ -z "$params" ] && params="$DEFAULT_PARAMS"
  # Link each imported interpretation that ships an x86_32 implementation.
  Iargs=()
  while read -r mod; do
    rel="${mod#I.}"; rel="${rel//.//}"
    [ -f "$STRATA/Interpretations/$rel.x86_32" ] && Iargs+=(-I:x86_32 "$mod")
  done < <(grep -oE '^import +[A-Za-z0-9_.]+' "$f" | awk '{print $2}')
  for opt in "${OPTS[@]}"; do
    tag="${opt:+-noopt}"
    $ONCE build --exe --target x86_32 $params $opt "${Iargs[@]}" --strata "$STRATA" "$f" -o "$BUILD/$name$tag" >"$BUILD/$name$tag.log" 2>&1
    if [ ! -f "$BUILD/$name$tag" ]; then
      echo "FAIL(build) $name$tag (expected exit $exp) — see $BUILD/$name$tag.log"
      fail=$((fail+1)); failed+=("$name$tag"); continue
    fi
    # D220: `emit` is a REAL SigOp now, so an emitting test writes machine words
    # to stdout. Capture them next to the build log rather than into the terminal;
    # the two builds' outputs are compared below.
    timeout 10 "$QEMU" "$BUILD/$name$tag" > "$BUILD/$name$tag.trace" 2>/dev/null; got=$?
    if [ "$got" -eq 124 ]; then
      echo "FAIL $name$tag: TIMEOUT (hang) under qemu-i386, expected exit $exp"
      fail=$((fail+1)); failed+=("$name$tag")
    elif [ "$got" -eq "$exp" ]; then
      pass=$((pass+1))
    else
      echo "FAIL $name$tag: expected exit $exp, got $got (qemu-i386)"
      fail=$((fail+1)); failed+=("$name$tag")
    fi
  done
  if [ "${#OPTS[@]}" -eq 2 ] && ! cmp -s "$BUILD/$name-noopt.trace" "$BUILD/$name.trace"; then
    echo "FAIL $name: the optimized build emits other output than --no-optimize"
    fail=$((fail+1)); failed+=("$name")
  fi
done
echo "=== x86_32/qemu exit-code tests: $pass passed, $fail failed, $skip skipped ==="
[ "$fail" -eq 0 ]
