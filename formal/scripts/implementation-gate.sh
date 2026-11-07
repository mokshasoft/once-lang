#!/usr/bin/env bash
# implementation-gate.sh: the implementation Spec is statements only, and assumed
# by nothing (plan 0.138 §5, plan 0.123 B.0.9).
#
# `Once.Implementation` states the claims that constrain the compiler but not the
# meaning (`NoLeak`; next, plan 0.138's layout claim). Each is a `Set`-valued
# definition, stated before it is proved; its proof lives elsewhere and becomes a
# field of `CertifiedBuild`. The gate checks:
#   1. the module (and any `Once/Implementation/**`) has no `postulate`;
#   2. nothing imports it but `Once.Certified` (which names each claim) and the
#      module's own submodules, so no proof assumes an unproved claim;
#   3. `Once.Certified` does import it, so every claim is visible at the apex.
# "Statements only" beyond (1) is by review: the gate cannot tell a statement
# from a lemma.
#
# Usage (from formal/):  scripts/implementation-gate.sh
set -euo pipefail
cd "$(dirname "$0")/.."

bad=0
mods=$( { echo Once/Implementation.agda; if [ -d Once/Implementation ]; then find Once/Implementation -name '*.agda'; fi; } | sort )

while IFS= read -r f; do
  if sed 's/--.*//' "$f" | grep -qE '(^|[[:space:]])postulate([[:space:]]|$)'; then
    echo "implementation-gate: $f has a postulate (statements only)"; bad=1
  fi
done <<< "$mods"

while IFS= read -r f; do
  case $f in
    Once/Certified.agda|Once/Implementation.agda|Once/Implementation/*) ;;
    *) echo "implementation-gate: $f imports the implementation Spec (only Once.Certified may)"; bad=1 ;;
  esac
done < <(grep -rlE '^\s*(open\s+)?import\s+Once\.Implementation(\.|\s|$)' --include='*.agda' Once | sort)

grep -qE '^\s*(open\s+)?import\s+Once\.Implementation(\s|$)' Once/Certified.agda \
  || { echo "implementation-gate: Once.Certified does not import Once.Implementation"; bad=1; }

if (( bad )); then echo "implementation-gate: FAIL"; exit 1; fi
echo "implementation-gate: OK ($(wc -l <<< "$mods") module(s), statements only, named by Once.Certified alone)"
