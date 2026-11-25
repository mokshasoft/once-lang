#!/usr/bin/env bash
# Heap-mode runtime regression net — RISC-V 64 under QEMU (Plan 0.53 Phase 4).
#
# Mirror of run-exit-tests.sh, but builds each compiler/test/*.once for
# --target riscv64 with the RISC-V cross toolchain and runs the resulting
# static ELF under qemu-riscv64 (user-mode), checking its trace and its end
# (`tests/check-trace.py`).
#
# Requires: the riscv64 cross binutils (as/ld/objcopy) and qemu-riscv64.
# The once build shells out to $AS/$LD/$OBJCOPY, so we point those at the
# cross tools. Assembly/linking is fully cross; execution is emulated.
#
# Usage: tests/run-exit-tests-riscv64.sh ["<default build flags>"]
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

# RISC-V cross toolchain + emulator.
CROSS="riscv64-unknown-linux-gnu"
QEMU="${QEMU_RISCV64:-qemu-riscv64}"
command -v "$CROSS-as" >/dev/null    || { echo "missing $CROSS-as"; exit 2; }
command -v "$CROSS-ld" >/dev/null    || { echo "missing $CROSS-ld"; exit 2; }
command -v "$CROSS-objcopy" >/dev/null || { echo "missing $CROSS-objcopy"; exit 2; }
command -v "$QEMU" >/dev/null        || { echo "missing $QEMU"; exit 2; }
export AS="$CROSS-as" LD="$CROSS-ld" OBJCOPY="$CROSS-objcopy"

# The Host the tests run under: ONCE_TEST_HOST=linux (default) or bare.
ARCH=riscv64; LINUX_RUN=("$QEMU")
source "$ROOT/tests/test-host.sh"

pass=0; fail=0; skip=0; declare -a failed=()
for f in "$TESTDIR"/*.once; do
  name="$(basename "$f" .once)"
  grep -qiE '^--.*\bPENDING\b' "$f" && { skip=$((skip+1)); echo "SKIP $name (PENDING)"; continue; }
  if why="$(host_skip "$f")"; then skip=$((skip+1)); echo "SKIP $name ($why)"; continue; fi
  # The expected observable (plan 0.140 §3.5): "Expected: trace [v, …]", and
  # ", end halted" / ", end exhausted" when the run does not return.
  line="$(grep -iE '^--.*expected[^:]*: *trace \[' "$f" | head -1)"
  [ -z "$line" ] && continue
  exp="$(printf '%s' "$line" | grep -oE 'trace \[[^]]*\]' | sed 's/^trace //')"
  end="$(printf '%s' "$line" | grep -oE 'end (returned|halted|exhausted)' | sed 's/^end //')"
  end="${end:-returned}"
  params="$(grep -oiE '^-- *params:.*' "$f" | sed -E 's/^-- *params: *//I' | head -1)"
  [ -z "$params" ] && params="$DEFAULT_PARAMS"
  # Link each imported interpretation that ships a riscv64 implementation.
  Iargs=()
  while read -r mod; do
    rel="${mod#I.}"; rel="${rel//.//}"
    [ -f "$STRATA/Interpretations/$rel.riscv64" ] && Iargs+=(-I:riscv64 "$mod")
  done < <(grep -oE '^import +[A-Za-z0-9_.]+' "$f" | awk '{print $2}')
  for opt in "${OPTS[@]}"; do
    tag="${opt:+-noopt}"
    $ONCE build --exe --target riscv64 "${HOST_FLAGS[@]}" $params $opt "${Iargs[@]}" --strata "$STRATA" "$f" -o "$BUILD/$name$tag" >"$BUILD/$name$tag.log" 2>&1
    if [ ! -f "$BUILD/$name$tag" ]; then
      echo "FAIL(build) $name$tag (expected trace $exp, end $end) — see $BUILD/$name$tag.log"
      fail=$((fail+1)); failed+=("$name$tag"); continue
    fi
    # Per-test wall-clock cap: a codegen bug can loop forever under qemu.
    # timeout exits 124 on expiry, which surfaces as a FAIL (never a hang).
    # The trace is machine words on stdout: captured next to the build log,
    # checked against the expectation, and compared between the two builds.
    "${RUN[@]}" "$BUILD/$name$tag" > "$BUILD/$name$tag.trace" 2>/dev/null; got=$?
    if why="$(python3 "$ROOT/tests/check-trace.py" "$END_TABLE" 8 "$BUILD/$name$tag.trace" "$got" "$exp" "$end")"; then
      pass=$((pass+1))
    else
      echo "FAIL $name$tag: $why"
      fail=$((fail+1)); failed+=("$name$tag")
    fi
  done
  if [ "${#OPTS[@]}" -eq 2 ] && ! cmp -s "$BUILD/$name-noopt.trace" "$BUILD/$name.trace"; then
    echo "FAIL $name: the optimized build emits other output than --no-optimize"
    fail=$((fail+1)); failed+=("$name")
  fi
done
echo "=== riscv64/$HOST_LABEL exit tests (trace and end): $pass passed, $fail failed, $skip skipped ==="
# The seL4 Host has its own runner; it runs with the Linux pass.
[ "$ONCE_TEST_HOST" = linux ] && { "$ROOT/tests/run-sel4-tests.sh" riscv64 || fail=$((fail+1)); }
[ "$fail" -eq 0 ]
