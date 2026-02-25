#!/bin/bash
# Run dead code analysis on the Once formal project
#
# Uses the patched Agda with --dead-code support from the local agda repo.
# Copies stdlib to a local writable location for interface caching.
#
# Usage: ./run-dead-code.sh [entry-point] [file.agda]
#
# Example:
#   ./run-dead-code.sh Once.CCC.Target.X86v3.WholeProgram.compile-correct Once/CCC/Target/X86v3/WholeProgram.agda

set -e

if [ $# -ne 2 ]; then
    echo "Usage: $0 <entry-point> <file.agda>"
    echo ""
    echo "Example:"
    echo "  $0 Once.CCC.Target.X86v3.WholeProgram.compile-correct Once/CCC/Target/X86v3/WholeProgram.agda"
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
AGDA_BIN=$(ls -t /home/whatever/Repo/OpenSource/agda/dist-newstyle/build/x86_64-linux/ghc-*/Agda-2.8.0/x/agda/build/agda/agda 2>/dev/null | head -1)

ENTRY_POINT="$1"
AGDA_FILE="$2"

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

# Clean interface files for the target module's directory tree
MODULE_DIR=$(dirname "$AGDA_FILE")
echo "Cleaning interface files in $MODULE_DIR/..."
find "$MODULE_DIR" -name "*.agdai" -delete 2>/dev/null || true

echo "Running dead code analysis..."
echo "  Entry point: $ENTRY_POINT"
echo "  File: $AGDA_FILE"
echo ""

unset AGDA_DIR
export LC_ALL=en_US.utf8
"$AGDA_BIN" \
    --library-file=<(echo "$LOCAL_STD_LIB"; echo "Once.agda-lib") \
    --transliterate \
    --dead-code="$ENTRY_POINT" \
    "$AGDA_FILE"
