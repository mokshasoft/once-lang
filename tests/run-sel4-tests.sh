#!/usr/bin/env bash
# The seL4 tests of one architecture: every example booted under QEMU on the
# pinned kernel, and every seL4 number checked against it. Nix builds the
# compiler, the kernel and the images, and caches them, so a run after no
# change is quick. Each run-exit-tests script calls this for its architecture.
#
# Usage: tests/run-sel4-tests.sh x86_64|x86_32|riscv64
set -u
ARCH="${1:?usage: run-sel4-tests.sh x86_64|x86_32|riscv64}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
command -v nix >/dev/null || { echo "missing nix"; exit 2; }

log="$(mktemp)"
# One job on one core: the compiler's build takes most of a small machine.
# Capped per unit, not as a whole: each image's compile by the flake (`timeout`
# in mkImage), each boot by the flake (`timeout` around QEMU), and every other
# step by formal/scripts/watchdog.sh: with -L nix prints a line per GHC module,
# so SEL4_UNIT_SECS (default 600) of silence means one step is stuck, and the
# log's last line names it. The slowest step is reported on a pass.
if (cd "$ROOT/examples/seL4" && "$ROOT/formal/scripts/watchdog.sh" "${SEL4_UNIT_SECS:-600}" \
      nix build ".#all-$ARCH" --no-link -L --max-jobs 1 --cores 1) > "$log" 2>&1; then
  grep '^watchdog: slowest' "$log" | sed "s/^/$ARCH\/seL4 /"
  rm -f "$log"
  echo "=== $ARCH/seL4 tests: passed ==="
else
  tail -40 "$log"
  echo "=== $ARCH/seL4 tests: FAILED (full log: $log) ==="
  exit 1
fi
