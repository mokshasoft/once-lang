#!/usr/bin/env bash
# Heap-mode runtime regression net.
#
# For every compiler/test/*.once that declares an expected exit code
# ("-- Expected: exit N"), build it for x86_64 and run the binary, checking
# the process exit code. This catches regressions that are invisible to the
# Agda proofs because the proofs are value-level while the observable is the
# SigOp trace (e.g. the optimizer's `→Unit ⇒ terminal` rule dropping
# effectful SigOps so a program silently exits 0).
#
# Canonical build params for the heap-mode suite are `--alloc heap
# --no-optimize`. A test may override them with a line:
#     -- params: <flags>
# A test may be skipped (not yet implemented) with a line containing:
#     -- PENDING
#
# Usage: tests/run-exit-tests.sh ["<default build flags>"]
set -u
DEFAULT_PARAMS="${1:---alloc heap --no-optimize}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TESTDIR="$ROOT/compiler/test"
STRATA="$ROOT/Strata"
BUILD="$(mktemp -d)"
ONCE="$(cd "$ROOT/compiler" && cabal list-bin once 2>/dev/null)"
[ -x "$ONCE" ] || { echo "no once binary (run: cd compiler && cabal build exe:once)"; exit 2; }

pass=0; fail=0; skip=0; declare -a failed=()
for f in "$TESTDIR"/*.once; do
  name="$(basename "$f" .once)"
  grep -qiE '^--.*\bPENDING\b' "$f" && { skip=$((skip+1)); echo "SKIP $name (PENDING)"; continue; }
  exp="$(grep -oiE 'expected.*exit (code )?[0-9]+|exit code [0-9]+' "$f" | grep -oE '[0-9]+' | head -1)"
  [ -z "$exp" ] && continue
  params="$(grep -oiE '^-- *params:.*' "$f" | sed -E 's/^-- *params: *//I' | head -1)"
  [ -z "$params" ] && params="$DEFAULT_PARAMS"
  # Link each imported interpretation that ships an x86_64 implementation.
  Iargs=()
  while read -r mod; do
    rel="${mod#I.}"; rel="${rel//.//}"
    [ -f "$STRATA/Interpretations/$rel.x86_64" ] && Iargs+=(-I:x86_64 "$mod")
  done < <(grep -oE '^import +[A-Za-z0-9_.]+' "$f" | awk '{print $2}')
  $ONCE build --exe --target x86_64 $params "${Iargs[@]}" --strata "$STRATA" "$f" -o "$BUILD/$name" >"$BUILD/$name.log" 2>&1
  if [ ! -x "$BUILD/$name" ]; then
    echo "FAIL(build) $name (expected exit $exp) — see $BUILD/$name.log"
    fail=$((fail+1)); failed+=("$name"); continue
  fi
  "$BUILD/$name"; got=$?
  if [ "$got" -eq "$exp" ]; then
    pass=$((pass+1))
  else
    echo "FAIL $name: expected exit $exp, got $got"
    fail=$((fail+1)); failed+=("$name")
  fi
done
echo "=== exit-code tests: $pass passed, $fail failed, $skip skipped ==="
[ "$fail" -eq 0 ]
