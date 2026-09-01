#!/usr/bin/env bash
# ============================================================================
# Regenerate `Trust.agda`'s import list — every module the sweep builds.
#
# ★★★ WHY THIS EXISTS.  `--safe` is CO-INFECTIVE (measured: a `--safe`
#   module importing a non-`--safe` one is `CoInfectiveImport`), and it
#   BANS `postulate` outright (`SafeFlagPostulate`).  So ONE `--safe`
#   module that imports the whole tree makes AGDA enforce the trust
#   surface — no scanner required.
# ⚠ `Trust.agda` claimed to be that module for weeks and imported ZERO.
#   The checking was entirely in `check-trust.sh`.
#
# ⚠ `import`, NOT `open import`: we want the DEPENDENCY EDGE, not the
#   names — 240 modules opened would collide immediately.
#
# ⚠ `Negative/` is EXCLUDED, deliberately.  It holds refuted results that
#   must NOT build; importing them would make the trust root fail for the
#   one reason that is not a trust violation.
# ============================================================================
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
find "$ROOT" -name '*.agda' \
  | grep -v '/Negative/' | grep -v '/Trust.agda$' \
  | sed "s|^$ROOT/||; s|\.agda$||; s|/|.|g; s|^|import DirectedHoTT.|" \
  | LC_ALL=C sort
