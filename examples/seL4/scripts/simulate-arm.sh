#!/usr/bin/env bash
# Simulate seL4 + Once on ARM64 QEMU

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

KERNEL="${1:-$PROJECT_DIR/build/arm64/kernel.elf}"
ROOTSERVER="${2:-$PROJECT_DIR/build/arm64/rootserver.elf}"

if [ ! -f "$KERNEL" ]; then
    echo "Error: Kernel not found at $KERNEL"
    echo "Build with: nix build .#seL4-arm64"
    exit 1
fi

echo "Starting seL4 on ARM64 QEMU..."
echo "Kernel: $KERNEL"
echo "Press Ctrl-A X to exit"
echo ""

qemu-system-aarch64 \
    -machine virt \
    -cpu cortex-a53 \
    -m 512 \
    -nographic \
    -kernel "$KERNEL" \
    ${ROOTSERVER:+-device loader,file=$ROOTSERVER,addr=0x40100000}
