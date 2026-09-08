#!/usr/bin/env bash
# Extraction-sync check (D162).
#
# Two hand-maintained mirrors of the extraction drift silently, and only a
# build nobody had run in 84 commits ever noticed:
#
#   (1) `once.cabal`'s MAlonzo module list vs the modules actually extracted.
#       On 2026-09-08 it listed two modules that no longer exist and omitted
#       one that does; adding `Once.Extract.Names` re-broke it minutes later.
#   (2) hand-written references to extracted names, which carry AGDA'S
#       INTERNAL SERIAL (`d_resolveImports_1008`). Any Agda edit renumbers
#       them; that extraction cost 24 renames by hand.
#
# Neither is a correctness question — both fail loudly at compile time. This
# turns "discover it thirty minutes into a build" into "one command, with the
# replacement listed".
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
C="$ROOT/compiler"
status=0

disk=$(cd "$C" && find src/MAlonzo/Code/Once -name '*.hs' | sed 's|src/||; s|\.hs$||; s|/|.|g' | sort -u)
cabal=$(grep -oE "MAlonzo\.Code\.Once[A-Za-z0-9_.]*" "$C/once.cabal" | sort -u)
missing=$(comm -13 <(echo "$cabal") <(echo "$disk"))
stale=$(comm -23 <(echo "$cabal") <(echo "$disk"))
if [ -n "$missing" ]; then
  echo "once.cabal is MISSING extracted modules (add to other-modules):"
  echo "$missing" | sed 's/^/    /'; status=1
fi
if [ -n "$stale" ]; then
  echo "once.cabal lists modules that are NO LONGER extracted (remove):"
  echo "$stale" | sed 's/^/    /'; status=1
fi

bad=""
for ref in $(find "$C/src/Once" -name '*.hs' -exec grep -ohE "\b(d|C|T)_[A-Za-z0-9'_-]+_[0-9]+" {} + 2>/dev/null | sort -u); do
  grep -rqF -- "$ref" "$C/src/MAlonzo/Code/Once" 2>/dev/null || bad="$bad $ref"
done
if [ -n "$bad" ]; then
  echo "hand-written code references extracted names that no longer exist:"
  for b in $bad; do
    base="${b%_*}"
    now=$(grep -rhoE -- "${base}_[0-9]+" "$C/src/MAlonzo/Code/Once" 2>/dev/null | sort -u | tr '\n' ' ')
    echo "    $b   ->  ${now:-<gone: renamed or removed>}"
  done
  status=1
fi

[ "$status" -eq 0 ] && echo "extraction sync: OK (cabal module list and extracted-name references agree)"
exit $status
