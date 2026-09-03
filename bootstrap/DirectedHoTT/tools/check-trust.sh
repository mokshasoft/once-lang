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

# ============================================================================
# ★★★ GATE 2 — THE KERNEL DOES NOT DEPEND ON ANYTHING IT VOUCHES FOR.
#
# ⚠⚠ ASKED DIRECTLY: "I prove something against a kernel that is sound, but
#   use a library that has a bug — is my proof suddenly proving false?"
#   NO, and the reason is structural rather than a promise: `Spec/` and
#   `Metatheory/` import NOTHING from `Lib/` or `Examples/`.  The
#   dependency runs one way.  A defect in a library or an example cannot
#   reach consistency, canonicity or SN; the worst it can do is make a
#   TRUE theorem be about the wrong object.
#
# ★ THAT BOUND IS THE WHOLE REASON THE `wkK` CLASS IS SURVIVABLE.  `⊢wkK`
#   is true, non-vacuous, and used at real arguments; every theorem over
#   it is true.  What was wrong is which weakening it names — damage
#   confined to ADEQUACY, which is exactly the layer that owes a
#   specification anyway.
#
# ⇒ so it is checked here, because an invariant that matters that much
#   should not rest on nobody having added the import yet.
# ============================================================================
bad="$(grep -rn '^open import DirectedHoTT\.\(Examples\|Lib\)' \
         "$ROOT/Spec" "$ROOT/Metatheory" 2>/dev/null || true)"
if [ -n "$bad" ]; then
  echo "== KERNEL DEPENDS ON A LIBRARY — the one-way street is broken." >&2
  echo "   Spec/ and Metatheory/ must not import Lib/ or Examples/:" >&2
  printf '%s\n' "$bad" >&2
  exit 1
fi
echo "== KERNEL IS INDEPENDENT: Spec/ and Metatheory/ import no Lib/ or Examples/."
echo "   ⇒ a defect in a library cannot reach consistency, canonicity or SN."

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
