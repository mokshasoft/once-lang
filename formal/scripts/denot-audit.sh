#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# denot-audit.sh — FAST regression check (grep only, no Agda run) that the
# denotational meaning's transitive import closure is free of TP-breaking
# escape hatches: {-# TERMINATING #-} / {-# NON_TERMINATING #-} / primTrustMe /
# --sized-types, and reports any `postulate`s (D062).
#
# This is the iteration tracker. The rigorous machine-enforced gate is
# `make denot-safe` (Once.Verified.DenotClean under {-# OPTIONS --safe #-}).
set -euo pipefail
cd "$(dirname "$0")/.."   # -> formal/

# Roots default to the SEMANTIC CORE — the meaning functions `evalᴰ` (DenotTrace)
# and `⟦_⟧ˢ` (SourceDenote) + their recursion-scheme math. NOT the frontend:
# `faithful`/`⟦ src ⟧` additionally use `elaborate`/`moduleToIR` (parser +
# elaborator), whose termination is a separate concern. Override with args.
ROOTS="${*:-Once/Verified/DenotTrace Once/Verified/SourceDenote}"

declare -A seen
queue=()
for r in $ROOTS; do queue+=("$r"); done
closure=()

while [ ${#queue[@]} -gt 0 ]; do
  m="${queue[0]}"; queue=("${queue[@]:1}")
  [ -n "${seen[$m]:-}" ] && continue
  seen[$m]=1
  f="$m.agda"
  [ -f "$f" ] || continue
  closure+=("$f")
  while read -r mod; do
    [ -z "$mod" ] && continue
    path="Once/$(printf '%s' "$mod" | sed -E 's/^Once\.//; s/\./\//g')"
    [ -z "${seen[$path]:-}" ] && queue+=("$path")
  done < <(grep -hoE "(open import|import)[[:space:]]+Once\.[A-Za-z0-9._]+" "$f" \
             | sed -E 's/.*[[:space:]](Once\.[A-Za-z0-9._]+)/\1/' | sort -u)
done

echo "Denotational meaning closure: ${#closure[@]} modules"

term=$(grep -lE "\{-#[[:space:]]*(NON_)?TERMINATING" "${closure[@]}" 2>/dev/null || true)
trust=$(grep -lE "primTrustMe|trustMe" "${closure[@]}" 2>/dev/null || true)
sized=$(grep -lE "OPTIONS.*--sized-types" "${closure[@]}" 2>/dev/null || true)
post=$(grep -lE "^[[:space:]]*postulate" "${closure[@]}" 2>/dev/null || true)

status=0
# `report` gates GREEN/RED: a non-empty hit is a FAILURE. Used for the escape
# hatches that actually break totality/productivity.
report() { # $1 = label, $2 = file list
  if [ -n "$2" ]; then
    echo "  ✗ $1:"; printf '      %s\n' $2; status=1
  else
    echo "  ✓ $1: none"
  fi
}
# `report-info` is INFORMATIONAL only — it never fails the gate. D062: the
# meaning legitimately rests on declared axioms (`funext`, `bisimS-to-eq`) and
# external SigOp/arith contracts; `agda --safe` rejects ALL postulates, so it is
# the wrong gate. Discharging these is the stricter `denot-safe-strict` goal.
report-info() { # $1 = label, $2 = file list
  if [ -n "$2" ]; then
    echo "  • $1 (declared, not a TP gap):"; printf '      %s\n' $2
  else
    echo "  ✓ $1: none"
  fi
}
echo "TP escape hatches (must be empty):"
report "TERMINATING" "$term"
report "trustMe"     "$trust"
report "--sized-types" "$sized"
echo "postulates (foundational axioms allowed; not gated):"
report-info "postulate" "$post"

if [ $status -eq 0 ]; then
  echo "GREEN — denotational meaning closure is TP-clean (no escape hatches)."
else
  echo "RED — escape hatches remain (see above)."
fi
exit $status
