#!/usr/bin/env bash
# Heap-mode runtime regression net — RISC-V 64 under QEMU (Plan 0.53 Phase 4).
#
# Mirror of run-exit-tests.sh, but builds each compiler/test/*.once for
# --target riscv64 with the RISC-V cross toolchain and runs the resulting
# static ELF under qemu-riscv64 (user-mode), checking the process exit code.
#
# Requires: the riscv64 cross binutils (as/ld/objcopy) and qemu-riscv64.
# The once build shells out to $AS/$LD/$OBJCOPY, so we point those at the
# cross tools. Assembly/linking is fully cross; execution is emulated.
#
# Usage: tests/run-exit-tests-riscv64.sh ["<default build flags>"]
set -u
DEFAULT_PARAMS="${1:---alloc heap --no-optimize}"
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

pass=0; fail=0; skip=0; declare -a failed=()
for f in "$TESTDIR"/*.once; do
  name="$(basename "$f" .once)"
  grep -qiE '^--.*\bPENDING\b' "$f" && { skip=$((skip+1)); echo "SKIP $name (PENDING)"; continue; }
  exp="$(grep -oiE 'expected.*exit (code )?[0-9]+|exit code [0-9]+' "$f" | grep -oE '[0-9]+' | head -1)"
  [ -z "$exp" ] && continue
  params="$(grep -oiE '^-- *params:.*' "$f" | sed -E 's/^-- *params: *//I' | head -1)"
  [ -z "$params" ] && params="$DEFAULT_PARAMS"
  # Link each imported interpretation that ships a riscv64 implementation.
  Iargs=()
  while read -r mod; do
    rel="${mod#I.}"; rel="${rel//.//}"
    [ -f "$STRATA/Interpretations/$rel.riscv64" ] && Iargs+=(-I:riscv64 "$mod")
  done < <(grep -oE '^import +[A-Za-z0-9_.]+' "$f" | awk '{print $2}')
  $ONCE build --exe --target riscv64 $params "${Iargs[@]}" --strata "$STRATA" "$f" -o "$BUILD/$name" >"$BUILD/$name.log" 2>&1
  if [ ! -f "$BUILD/$name" ]; then
    echo "FAIL(build) $name (expected exit $exp) — see $BUILD/$name.log"
    fail=$((fail+1)); failed+=("$name"); continue
  fi
  "$QEMU" "$BUILD/$name"; got=$?
  if [ "$got" -eq "$exp" ]; then
    pass=$((pass+1))
  else
    echo "FAIL $name: expected exit $exp, got $got (qemu-riscv64)"
    fail=$((fail+1)); failed+=("$name")
  fi
done
echo "=== riscv64/qemu exit-code tests: $pass passed, $fail failed, $skip skipped ==="
[ "$fail" -eq 0 ]
