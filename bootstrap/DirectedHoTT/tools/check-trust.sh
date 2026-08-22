#!/usr/bin/env bash
# Enforce DirectedHoTT/Trust.agda mechanically. Comments are stripped first,
# so a module may DISCUSS `postulate` in its header without tripping this.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
bad=0
while IFS= read -r f; do
  code="$(sed 's/--.*$//' "$f")"
  for pat in '\bpostulate\b' 'TERMINATING' 'NON_TERMINATING' 'primTrustMe' '\btrustMe\b' \
             'NO_POSITIVITY_CHECK' 'NO_UNIVERSE_CHECK' 'NO_TERMINATION_CHECK' '{![^}]*!}'; do
    if grep -qE "$pat" <<<"$code"; then
      echo "TRUST VIOLATION  $f  matches /$pat/" >&2; bad=1
    fi
  done
  if grep -q '{-# OPTIONS' "$f" && ! grep -E '\{-# OPTIONS' "$f" | grep -q -- '--safe'; then
    echo "TRUST VIOLATION  $f  has OPTIONS without --safe" >&2; bad=1
  fi
  grep -q '{-# OPTIONS' "$f" || { echo "TRUST VIOLATION  $f  has no OPTIONS/--safe line" >&2; bad=1; }
done < <(find "$ROOT" -name '*.agda')
n=$(find "$ROOT" -name '*.agda' | wc -l)
if [ "$bad" -eq 0 ]; then
  echo "== TRUST SURFACE EMPTY across $n modules (--safe, no postulates, no pragmas, no holes)."
else
  echo "== TRUST SURFACE VIOLATED — see above." >&2
fi
exit $bad
