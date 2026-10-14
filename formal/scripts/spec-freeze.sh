#!/usr/bin/env bash
# spec-freeze.sh — the Spec changes only with the user's approval.
#
# `scripts/spec.sha256` lists a SHA-256 for every file of the Spec: `Once/Spec.agda`
# and everything under `Once/Spec/` (Spec/Metatheory.agda included: the
# metatheorem STATEMENTS are Spec; their proofs under `Once/Metatheory/` are not).
#   --gate     fail if the working tree differs from the list (edited, added
#              or deleted file)
#   --approve  rewrite the list from the working tree. Run it ONLY after the
#              user approved the Spec change (ideally the user runs
#              `! make spec-approve` themselves). A plan or design text is not
#              approval.
#
# Usage (from formal/):  scripts/spec-freeze.sh --gate | --approve
set -euo pipefail
cd "$(dirname "$0")/.."
list=scripts/spec.sha256

current() { find Once/Spec.agda Once/Spec -type f -name '*.agda' | LC_ALL=C sort | xargs sha256sum; }

case "${1:-}" in
  --approve) current > "$list"; echo "spec-freeze: approved $(wc -l < "$list") Spec files";;
  --gate)
    if ! diff <(cat "$list") <(current) > /dev/null; then
      echo "spec-freeze: the Spec differs from the approved hashes ($list):"
      join -a1 -a2 -j2 -e MISSING -o 0,1.1,2.1 <(LC_ALL=C sort -k2 "$list") <(current | LC_ALL=C sort -k2) \
        | awk '$2 != $3 { s = ($2 == "MISSING") ? "added" : ($3 == "MISSING") ? "deleted" : "changed"; print "  " s ": " $1 }'
      echo "spec-freeze: a Spec change needs the user's approval, then \`make spec-approve\`."
      exit 1
    fi;;
  *) echo "usage: $0 --gate | --approve" >&2; exit 2;;
esac
