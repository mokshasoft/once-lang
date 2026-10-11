#!/usr/bin/env bash
# metatheory-gate.sh — the language's metatheory depends on the Spec ALONE (D304).
#
# A metatheorem is a claim about the Spec: its proof (`Once/Metatheory/**`) may
# import only the Spec, the semantic domain the Spec's meaning is built on, and
# other metatheory — never the compiler or its proofs (Compile, CCC, Adequacy,
# TypeCheck, Parser, …). The reverse direction is fine: a compiler proof may
# use a metatheorem. Allowed `Once.*` prefixes are listed below; library
# imports (Data, Relation, Function, Level, Agda) are always allowed.
#
# Usage (from formal/):  scripts/metatheory-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

allowed='^Once\.(Spec|Spec\..*|Type|Type\..*|Surface\..*|Denotation\..*|Target\.Arch|Postulates|Metatheory\..*)$'

bad=0; n=0
while IFS= read -r f; do
  n=$((n+1))
  while IFS= read -r m; do
    if [[ $m == Once.* && ! $m =~ $allowed ]]; then
      echo "metatheory-gate: $f imports $m (not Spec-side)"; bad=1
    fi
  done < <(grep -oP '^\s*(open\s+)?import\s+\K[\w.]+' "$f" | sort -u)
done < <(find Once/Metatheory -name '*.agda' | sort)

if (( bad )); then echo "metatheory-gate: FAIL"; exit 1; fi
echo "metatheory-gate: OK ($n modules under Once/Metatheory import only the Spec side)"
