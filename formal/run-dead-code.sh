#!/bin/bash
# Run dead code analysis on the Once formal project
#
# Uses the patched Agda with --dead-code support from the local agda repo.
# Copies stdlib to a local writable location for interface caching.
#
# Usage: ./run-dead-code.sh [entry-point] [file.agda]
#
# Example:
#   ./run-dead-code.sh Once.Backend.X86v3.CodeGen.compile-ir Once/Backend/X86v3/CodeGen.agda

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
AGDA_BIN=$(ls -t /home/whatever/Repo/OpenSource/agda/dist-newstyle/build/x86_64-linux/ghc-*/Agda-2.8.0/x/agda/build/agda/agda 2>/dev/null | head -1)                   

ENTRY_POINT="${1:-Once.Backend.X86v3.WholeProgram.Correctness.compile-correct}"
AGDA_FILE="${2:-Once/Backend/X86v3/WholeProgram.agda}"

# Find standard library in nix store
NIX_STD_LIB=$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1)
if [ -z "$NIX_STD_LIB" ]; then
    echo "Error: standard-library not found in Nix store"
    exit 1
fi

NIX_STD_LIB_DIR=$(dirname "$NIX_STD_LIB")

# Create local writable copy of stdlib for interface caching
LOCAL_STD_LIB_DIR="$HOME/_stdlib-cache"
LOCAL_STD_LIB="$LOCAL_STD_LIB_DIR/standard-library.agda-lib"

if [ ! -f "$LOCAL_STD_LIB" ]; then
    echo "Creating local writable copy of stdlib for interface caching..."
    mkdir -p "$LOCAL_STD_LIB_DIR"
    cp -r "$NIX_STD_LIB_DIR"/* "$LOCAL_STD_LIB_DIR"/
    chmod -R u+w "$LOCAL_STD_LIB_DIR"
    echo "Done. First run will be slow, subsequent runs will be fast."
fi

cd "$SCRIPT_DIR"

echo "Running dead code analysis..."
echo "  Entry point: $ENTRY_POINT"
echo "  File: $AGDA_FILE"
echo ""

unset AGDA_DIR
"$AGDA_BIN" \
    --library-file=<(echo "$LOCAL_STD_LIB"; echo "Once.agda-lib") \
    --dead-code="$ENTRY_POINT" \
    "$AGDA_FILE"
