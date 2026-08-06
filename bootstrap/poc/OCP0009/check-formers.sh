#!/usr/bin/env bash
# ============================================================================
# check-formers.sh — the SN-LAYER TRIPWIRE.
#
# WHY THIS EXISTS.  Agda's coverage checker checks FUNCTIONS, not DATATYPES.
# `data SNe` with no row for a term former is a perfectly well-formed
# definition, and nothing in NbEPDirDBLR is obliged to produce an
# `SNe (ordtr …)` — so LR type-checks GREEN with the former missing from the
# entire SN layer, and the omission only surfaces four modules downstream as
# an unprovable `fund` case in the 1m36s module.  That happened with `ordtr`
# (2026-08-05 → 06).
#
# WHAT IT CHECKS.  Every constructor of `RTm` must appear in at least one of
# the four SN-layer datatypes in NbEPDirDBLR:  SNe, SN, SNRed, Ne.
#
# That "at least one" is deliberate and is the whole point: no former belongs
# in all four (`var` is neutral, never a redex; `lam` is an introduction,
# never neutral), so a per-datatype requirement would be wrong.  But a former
# in NONE of them has no SN semantics at all, which is always a bug.
#
# WHAT IT DOES NOT CHECK.  That the rows are RIGHT — only that they exist.
# A former with an `SNe` row but no `SNRed` rows for its root rules still
# type-checks here.  This is a tripwire, not a proof.
#
# Usage:  ./check-formers.sh          # from bootstrap/poc/OCP0009
# Exit:   0 = every former is homed; 1 = at least one is orphaned.
# ============================================================================
set -uo pipefail

cd "$(dirname "$0")"

PI=NbEPDirDBPi.agda
LR=NbEPDirDBLR.agda

for f in "$PI" "$LR"; do
  [ -r "$f" ] || { echo "!! cannot read $f" >&2; exit 2; }
done

# --- the formers: constructor names in `data RTm where` up to the next
# --- top-level (column-0) declaration.
formers=$(awk '
  /^data RTm where/ { inblock = 1; next }
  inblock && /^[^ \t]/ { inblock = 0 }
  inblock && /^  *[^ \t-]/ {
    line = $0
    sub(/^[ \t]+/, "", line)
    if (line ~ /^[^ \t]+[ \t]*:/) { sub(/[ \t]*:.*$/, "", line); print line }
  }
' "$PI")

[ -n "$formers" ] || { echo "!! parsed zero RTm constructors from $PI" >&2; exit 2; }

# --- the SN layer: the bodies of the four datatypes, comments stripped, so a
# --- former merely NAMED in a comment does not count as homed.
snlayer=$(awk '
  /^data (SNe|SN|SNRed|Ne) / && /where/ { inblock = 1; print; next }
  inblock && /^[^ \t]/ { inblock = 0 }
  inblock { print }
' "$LR" | sed 's/--.*$//')

[ -n "$snlayer" ] || { echo "!! parsed zero SN-layer rows from $LR" >&2; exit 2; }

orphans=0
total=0
echo "== SN-layer tripwire: RTm formers vs SNe/SN/SNRed/Ne in $LR =="
for c in $formers; do
  total=$((total + 1))
  homes=""
  for d in SNe SN SNRed Ne; do
    body=$(printf '%s\n' "$snlayer" | awk -v d="$d" '
      $0 ~ ("^data " d " ") { inb = 1; next }
      inb && /^data /        { inb = 0 }
      inb { print }
    ')
    # word-boundary match: `ordtr` must not be matched by `ordtrX`, and the
    # constructor must appear as an applied/standalone token.
    if printf '%s\n' "$body" | grep -qE "(^|[^A-Za-z0-9_'ᵃ-ᵿ⌜⌝?-])${c//\\/\\\\}([^A-Za-z0-9_'ᵃ-ᵿ⌜⌝?-]|$)"; then
      homes="$homes $d"
    fi
  done
  if [ -z "$homes" ]; then
    printf '  ORPHAN  %-8s — in NO SN-layer datatype\n' "$c"
    orphans=$((orphans + 1))
  else
    printf '  ok      %-8s —%s\n' "$c" "$homes"
  fi
done

echo "== $total formers, $orphans orphaned =="
if [ "$orphans" -ne 0 ]; then
  cat >&2 <<'EOF'

!! FAIL: a term former has no SN semantics.
!! Agda will NOT catch this — `data SNe` needs no coverage.  Add the missing
!! rows to NbEPDirDBLR (`SNe` for the neutral case, `SNRed` for each root
!! rule plus one xi per scrutinee, `Ne` for the untyped-neutral peer, `SN`
!! only if the former is an INTRODUCTION), then re-run.
EOF
  exit 1
fi
