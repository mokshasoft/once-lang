#!/usr/bin/env bash
# metatheory-gate.sh — the language's metatheory depends on the Spec ALONE (D304).
#
# A metatheorem is a claim about the Spec: its proof (`Once/Metatheory/**`) may
# import only the Spec, the semantic domain the Spec's meaning is built on, and
# other metatheory — never the compiler or its proofs (Compile, CCC, Adequacy,
# TypeCheck, Parser, …). The reverse direction is fine: a compiler proof may
# use a metatheorem. Allowed: the `Once.*` prefixes below, every module of the
# public Spec closure (`spec-closure.py`: e.g. TypeCheck.Judgment = Spec.Typing),
# and the named EXCEPTIONS below, each a dependency the Spec itself has. NOT
# "everything Once.Spec imports": that closure reaches the compiler (176
# modules incl. Once.Compile, D300; plan 0.114), which would make the gate
# vacuous. Library imports (Data, Relation, Function, Level, Agda) are free.
#
# Usage (from formal/):  scripts/metatheory-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

allowed='^Once\.(Spec|Spec\..*|Type|Type\..*|Surface\..*|Denotation\..*|Target\.Arch|Postulates|Metatheory|Metatheory\..*)$'
declare -A exception=(
  [Once.TypeCheck.Classify]="the typing judgment's premises (composeMid, classifyAppHead, NamedCtx): MERGE.md §1, plan 0.80/D134"
  [Once.CanonicalName]="the Spec's name type (canonical names in Resolution and the judgment)"
  [Once.Semantics.Functor]="the Spec's stream observation (Spec.Equivalence: SFunctor, ⟦_⟧SF) and μ/ν layers"
  [Once.Functor.Translate]="the Spec's ν value domain (⟦ ν F π ⟧ᵛ = νᵖ (translateF …)); validity proofs' irrelevance"
  [Once.Semantics.Machine]="the Spec's μ value domain (⟦ μ F ⟧ᵛ = Val.⟦μ⟧ F, sem-In, the layer coercions)"
  [Once.Word]="the machine-word carrier the Spec's ν value domain is built at (Carrier)"
)
declare -A spec=()
closure=$(cd .. && python3 formal/scripts/spec-closure.py)
while IFS= read -r f; do m=${f#formal/}; m=${m%.agda}; spec[${m//\//.}]=1; done <<< "$closure"
(( ${#spec[@]} > 20 )) || { echo "metatheory-gate: spec-closure.py gave ${#spec[@]} modules — refusing to run"; exit 1; }

bad=0; n=0
while IFS= read -r f; do
  n=$((n+1))
  while IFS= read -r m; do
    if [[ $m == Once.* && ! $m =~ $allowed && -z ${spec[$m]:-} && -z ${exception[$m]:-} ]]; then
      echo "metatheory-gate: $f imports $m (not Spec-side)"; bad=1
    fi
  done < <(grep -oP '^\s*(open\s+)?import\s+\K[\w.]+' "$f" | sort -u)
done < <({ echo Once/Metatheory.agda; find Once/Metatheory -name '*.agda'; } | sort)

if (( bad )); then echo "metatheory-gate: FAIL"; exit 1; fi
echo "metatheory-gate: OK ($n modules under Once/Metatheory import only the Spec side)"
