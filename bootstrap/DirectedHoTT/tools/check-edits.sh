#!/usr/bin/env bash
# ============================================================================
# check-edits.sh — CHEAP STRUCTURAL CHECKS, run BEFORE an Agda build.
#
# WHY THIS EXISTS.  During the §9 rework, self-inflicted EDIT errors cost
# more build cycles than every genuine proof difficulty combined.  Each was
# catchable by a one-second textual check; none was catchable by reading
# Agda's error, which typically pointed somewhere else entirely:
#
#   * a name appended AFTER a `using (…)` list's closing paren → Agda
#     reported "clause has type _1" several minutes later
#   * a `rindex`-based code move that deleted a DIFFERENT clause's local
#     helper → reported as a duplicate definition in the clause I was editing
#   * a block inserted between a type signature and its 54 clauses → reported
#     as "not in scope" for an unrelated name
#   * an import check using grep without -F (name contained `*`) and then
#     with -F but unanchored (`church-rosser` matched `church-rosserᵀ`)
#
# ⚠ SCOPE, STATED HONESTLY.  These are HYGIENE checks on file structure.
#   They prove nothing about the mathematics and replace no typecheck.
# ============================================================================
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FAIL=0

echo "== 1. import headers: parens balanced =="
for f in $(find "$ROOT" -name '*.agda' | sort); do
  h=$(awk '/^private|^  variable|^data |^-- ---/{exit} {print}' "$f")
  o=$(grep -o '(' <<<"$h" | wc -l); c=$(grep -o ')' <<<"$h" | wc -l)
  if [ "$o" -ne "$c" ]; then
    echo "  ✗ $(basename "$f"): $o open / $c close"; FAIL=1
  fi
done
[ $FAIL -eq 0 ] && echo "  ok"

# ⚠ A "signature followed by its own clauses" check was tried and REMOVED:
# mutual blocks legitimately interleave (`renTy-renTy` / `renTm-renTm`), so it
# produced 109 warnings and zero signal.  A check nobody can read is a check
# nobody runs.
#
# ⚠ A "duplicate local definition" check was tried and REMOVED too: splitting
# `where` blocks textually is unreliable, and it false-positived on `agree`.
# The real defence against the code-motion bugs is the discipline, not a
# scanner: COUNT OCCURRENCES IN THE TARGET REGION BEFORE MOVING OR DELETING,
# and assert the count. `rindex` over a whole file is a lottery — it deleted
# `ι-elim`'s local helper while editing `ι-ielim`.

exit $FAIL
