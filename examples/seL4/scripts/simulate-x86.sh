#!/usr/bin/env bash
# Simulate seL4 + Once on x86_64 QEMU

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

KERNEL="${1:-$PROJECT_DIR/build/x86_64/kernel.elf}"

if [ ! -f "$KERNEL" ]; then
    echo "Error: Kernel not found at $KERNEL"
    echo "Build with: nix build .#seL4-x86_64"
    exit 1
fi

echo "Starting seL4 on x86_64 QEMU..."
echo "Kernel: $KERNEL"
echo "Press Ctrl-A X to exit"
echo ""

qemu-system-x86_64 \
    -machine q35 \
    -cpu Haswell \
    -m 512 \
    -nographic \
    -kernel "$KERNEL"
