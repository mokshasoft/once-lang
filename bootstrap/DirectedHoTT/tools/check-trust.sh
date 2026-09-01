#!/usr/bin/env bash
# ============================================================================
# DirectedHoTT — THE TRUST SURFACE, and what is left for a script to do.
#
# ★★★ ALMOST NOTHING, NOW.  This file used to scan every module for
#   `postulate`, `TERMINATING`, `NO_POSITIVITY_CHECK`, `primTrustMe`,
#   holes, and a missing `--safe`.  All of that is redundant — MEASURED
#   2026-09-01, both facts, because I had the first one backwards:
#
#       `--safe` BANS `postulate`            → SafeFlagPostulate
#       `--safe` PROPAGATES through imports  → CoInfectiveImport
#
#   ⇒ `Trust.agda` imports the WHOLE TREE under `--safe`, so AGDA rejects
#     any module that acquires one of those, transitively, in the sweep.
#     Control run: dropping `--safe` from `Knot/EWk` fails `Trust.agda`
#     with `CoInfectiveImport`.
#
# ⚠⚠ ONE QUESTION SURVIVES, AND IT IS NOT A PROPOSITION: does the trust
#   root REACH every file?  A module nothing imports is invisible to the
#   language however sound the language is — the same class as a stale
#   generated file the sweep still globs, and a `check.sh` returning 0 off
#   a cached `.agdai`.  COVERAGE, not correctness.
#
# ⇒ so this script now asks exactly that, by regenerating the list and
#   DIFFING.  Everything else is Agda's job and Agda does it.
# ============================================================================
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"

want="$("$HERE/gen-trust.sh")"
have="$(grep '^import ' "$ROOT/Trust.agda" | LC_ALL=C sort)"

if [ "$want" = "$have" ]; then
  n=$(printf '%s\n' "$want" | grep -c .)
  echo "== TRUST ROOT REACHES ALL $n modules (Negative/ excluded by design)."
  echo "   ⇒ --safe, no postulates, no pragmas, no holes: enforced BY AGDA,"
  echo "     transitively, when the sweep builds Trust.agda."
  exit 0
fi

echo "== TRUST ROOT INCOMPLETE — Trust.agda does not import every module." >&2
echo "   Regenerate with tools/gen-trust.sh.  Difference (want vs have):" >&2
diff <(printf '%s\n' "$want") <(printf '%s\n' "$have") >&2
exit 1
