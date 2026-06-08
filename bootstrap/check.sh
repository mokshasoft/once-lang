#!/usr/bin/env bash
# Typecheck a bootstrap module with the `Once` and `standard-library`
# dependencies registered (bootstrap.agda-lib now depends on both).
#
# Usage (path is relative to bootstrap/):
#   bootstrap/check.sh normalizer/Theory/Eval/Instance.agda
#
# Mirrors the --library-file pattern used by formal/Makefile. Modules that
# do not import Once still build fine; the dependency just makes Once
# available to those that do.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
STDLIB="$(find /nix/store -maxdepth 2 -name standard-library.agda-lib 2>/dev/null | head -1)"
[ -z "$STDLIB" ] && { echo "error: standard-library.agda-lib not found in /nix/store" >&2; exit 1; }
LIBF="$(mktemp)"
printf '%s\n' "$STDLIB" "$ROOT/formal/Once.agda-lib" "$ROOT/bootstrap/bootstrap.agda-lib" > "$LIBF"
cd "$HERE"
unset AGDA_DIR
agda --library-file="$LIBF" "$@"
rc=$?
rm -f "$LIBF"
exit $rc
