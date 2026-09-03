#!/usr/bin/env bash
# lint-imports.sh — fail on stale/duplicate/useless import directives.
#
# Agda only WARNS when a `using (...)` names something a module does not export,
# so every deletion leaves import lists stale, silently and forever. This turns
# those warnings into a build failure.
#
# Uses --only-scope-checking: ModuleDoesntExport, DuplicateUsing and
# UselessPublic are all SCOPE warnings, so no type-checking is needed. A full
# tree pass is therefore seconds per module -- and, unlike a normal build, it
# reports EVERY module rather than only the ones that happened to be rechecked.
set -uo pipefail
cd "$(dirname "$0")/.."

STD_LIB=$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1)
if [ -z "$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi
unset AGDA_DIR
LIBFILE=$(mktemp)
LOG=$(mktemp)
OUT=$(mktemp)
trap 'rm -f "$LIBFILE" "$LOG" "$OUT"' EXIT
printf '%s\nOnce.agda-lib\n' "$STD_LIB" > "$LIBFILE"

WARNS='ModuleDoesntExport|DuplicateUsing|UselessPublic'
bad=0

find Once -name '*.agda' | LC_ALL=C sort > "$OUT.files"
while IFS= read -r f; do
  timeout 120 agda --library-file="$LIBFILE" --only-scope-checking "$f" > "$OUT" 2>&1
  if grep -qE "$WARNS" "$OUT"; then
    grep -E "$WARNS" -A40 "$OUT" >> "$LOG"
    bad=$((bad+1))
  fi
done < "$OUT.files"
rm -f "$OUT.files"

if [ "$bad" -ne 0 ]; then
  cat "$LOG"
  echo
  echo "lint-imports: $bad module(s) have stale import directives (see above)."
  echo "A stale \`using\` list makes a genuinely wrong import indistinguishable"
  echo "from noise, and hides renames. See plans/0.82-import-hygiene.md."
  exit 1
fi
echo "lint-imports: clean."
