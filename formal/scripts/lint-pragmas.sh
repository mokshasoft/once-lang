#!/usr/bin/env bash
# lint-pragmas.sh — the pragma text is a COUNTABLE MARKER, so it must never
# appear inside a comment.
#
# `{-# TERMINATING #-}` in prose (a note about a pragma that was removed, or
# one a refactor is planning to avoid) makes every grep-based count wrong.
# This bit a merge analysis on 2026-09-03: 48 lines mentioned the pragma but
# only 22 were real, so a residual metric was overstated by more than 2x.
#
# Write the bare word instead: `TERMINATING`, or "the termination pragma".
set -uo pipefail
cd "$(dirname "$0")/.."

bad=$(grep -rnE '\{-# TERMINATING #-\}' Once --include='*.agda' \
      | grep -E '^[^:]*:[0-9]+:[[:space:]]*--' || true)

if [ -n "$bad" ]; then
  echo "lint-pragmas: pragma text inside a comment (write the bare word instead):"
  echo "$bad" | sed 's/^/  /'
  exit 1
fi

n=$(grep -rhE '^[[:space:]]*\{-# TERMINATING #-\}' Once --include='*.agda' | wc -l)
echo "lint-pragmas: clean. Real TERMINATING pragmas: $n"
