#!/usr/bin/env bash
#
# run-ast-dumps.sh — dump the AST and trust base reachable from the apex proof
# for two refs, into two clearly-marked JSON files.
#
# Uses Agda's --write-ast=QNAME / --ast-file=PATH flags.
#
# Each ref is type-checked in its own staging tree under $WORK, extracted with
# `git archive` from the *committed* ref, so a dirty working tree never leaks
# into a dump, and so this run cannot invalidate formal/_build for your own
# Agda. Staging trees keep their _build across runs: a run that dies partway
# (OOM, Ctrl-C, reboot) resumes from the interfaces already written.
#
#   ./run-ast-dumps.sh              # master and the current branch
#   ./run-ast-dumps.sh master       # one ref
#   HEAP=3G ./run-ast-dumps.sh      # tighter heap cap on a smaller machine
#
# Used by MERGE.md §4b (the reachability gate) and plan 0.92/D277 (apex-live scope).
#
# REQUIRES the Agda fork that adds --write-ast/--ast-file (and the dead-import /
# re-export tools): https://github.com/mokshasoft/agda , branch `dead-code-2.8.0`.
#
#   git clone -b dead-code-2.8.0 https://github.com/mokshasoft/agda ~/Repo/OpenSource/agda
#   cd ~/Repo/OpenSource/agda && nix develop --command cabal build exe:agda
#
# The newest agda binary under $AGDA_TREE (default: that clone's dist-newstyle) is
# used; set $AGDA to name one explicitly. The fork does not reuse interfaces
# written by the stock Agda, nor can it write into the read-only nix store, so the
# standard library is checked from a WRITABLE copy ($STDLIB), which this script
# creates from the nix store on first use.

set -uo pipefail

REPO="${REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
OUT_DIR="${OUT_DIR:-$REPO}"
WORK="${WORK:-$HOME/.cache/once-ast-runs}"
# Pick the most recently built agda under dist-newstyle rather than naming one
# path. The tree holds several (ghc versions, noopt vs optimised), and a stale
# one silently produces a dump in the old format -- which is hard to notice,
# since it still produces *a* dump.
AGDA_TREE="${AGDA_TREE:-$HOME/Repo/OpenSource/agda/dist-newstyle}"
if [ -z "${AGDA:-}" ]; then
  AGDA="$(find "$AGDA_TREE" -type f -perm -u+x -name agda -path '*/x/agda/*' \
            -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)"
fi
STDLIB="${STDLIB:-$HOME/.cache/once-astdump/stdlib/standard-library.agda-lib}"

# Agda's own output contains non-ASCII (Setw, arrows), and it encodes stdout
# using the locale. Under a non-UTF-8 locale it dies with "commitBuffer:
# invalid argument" partway through printing -- including while printing
# --help. So every invocation here gets a UTF-8 locale, not just the run.
LOCALE="${LOCALE:-en_US.utf8}"

ENTRY="${ENTRY:-Once.Certified.once-certified}"
ENTRY_MODULE="${ENTRY_MODULE:-Once/Certified.agda}"
ENTRY_SLUG="${ENTRY_SLUG:-once-certified}"

# Cap Agda's heap so a runaway module raises a clean heap-overflow instead of
# inviting the kernel OOM killer to take the whole session down -- that is what
# happened on the first attempt at this run.
#
# COMPACT switches the old generation to a compacting collector once live data
# passes N% of the cap. This matters more than the cap itself: the default
# copying collector needs roughly twice the live set during a collection, so a
# module with 2.6G live wants ~5.3G of headroom and blows a 5G cap even though
# it is nowhere near 5G of actual data. Compacting sooner (a lower N) trades
# speed for a markedly lower peak.
#
# Known offender: Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim reproducibly
# reaches ~2.64G residency and exhausts a 5G/-c40 heap. For that one:
#
#     HEAP=6G COMPACT=-c20 ./run-ast-dumps.sh master
#
HEAP="${HEAP:-5G}"
COMPACT="${COMPACT:--c40}"
ALLOC="${ALLOC:-16m}"
RTS_OPTS=(-M"$HEAP" "$COMPACT" -A"$ALLOC" -s)
# RTS_EXTRA is appended verbatim, for anything not covered above.
read -r -a _rts_extra <<< "${RTS_EXTRA:-}"
[ ${#_rts_extra[@]} -gt 0 ] && RTS_OPTS+=("${_rts_extra[@]}")

# Refs to dump. Order matters only for readability of the log.
REFS=("${@:-master $(git -C "$REPO" rev-parse --abbrev-ref HEAD)}")
read -r -a REFS <<< "${REFS[*]}"

say()  { printf '%s  %s\n' "$(date +%H:%M:%S)" "$*"; }
die()  { printf 'error: %s\n' "$*" >&2; exit 1; }
rule() { printf '%s\n' "------------------------------------------------------------"; }

# ---------------------------------------------------------------- preflight --

[ -n "${AGDA:-}" ] || die "no agda binary found under $AGDA_TREE (override with \$AGDA)"
[ -x "$AGDA" ]     || die "no agda binary at $AGDA (override with \$AGDA)"
if [ ! -f "$STDLIB" ]; then
  NIX_STDLIB="$(find /nix/store -maxdepth 2 -name standard-library.agda-lib 2>/dev/null | head -1)"
  [ -n "$NIX_STDLIB" ] || die "no standard-library.agda-lib at $STDLIB and none in /nix/store (override with \$STDLIB)"
  mkdir -p "$(dirname "$(dirname "$STDLIB")")"
  cp -r "$(dirname "$NIX_STDLIB")" "$(dirname "$STDLIB")" && chmod -R u+w "$(dirname "$STDLIB")" \
    || die "could not copy the standard library to $(dirname "$STDLIB")"
fi
[ -f "$STDLIB" ]   || die "no standard-library.agda-lib at $STDLIB (override with \$STDLIB)"
[ -d "$REPO/.git" ]|| die "$REPO is not a git repository (override with \$REPO)"
command -v python3 >/dev/null || die "python3 is required for post-processing"

# Captured rather than piped: agda may still exit non-zero (a locale it cannot
# encode, a broken pipe), and under `pipefail` that would mask a grep that did
# match -- reporting a missing flag when the flag is there.
agda_help="$(LC_ALL="$LOCALE" "$AGDA" --help 2>&1 || true)"
case $agda_help in
  *--write-ast*) ;;
  *) die "$AGDA has no --write-ast flag; build the branch that adds it" ;;
esac

mkdir -p "$WORK" "$OUT_DIR"

say "agda:    $(LC_ALL="$LOCALE" "$AGDA" --version 2>&1 | head -1)"
say "binary:  $AGDA"
say "built:   $(date -r "$AGDA" '+%Y-%m-%d %H:%M')"
say "repo:    $REPO"
say "work:    $WORK"
say "out:     $OUT_DIR"
say "entry:   $ENTRY"
say "rts:     ${RTS_OPTS[*]}"

# ------------------------------------------------------------------ staging --

# Extract $ref's formal/ into $dir, but only if $dir does not already hold
# exactly that content -- reusing a matching tree keeps its cached interfaces,
# which is the difference between minutes and hours.
stage_ref() {
  local ref="$1" dir="$2" tmp
  tmp="$(mktemp -d)"

  git -C "$REPO" ls-tree -r "$ref" formal/ \
    | awk '$2=="blob"{print $3"  "substr($4,8)}' | sort > "$tmp/expected"

  if [ -d "$dir" ]; then
    ( cd "$dir" \
      && find . -type f -not -path './.git/*' -not -path './_build/*' -printf '%P\n' | sort > "$tmp/names" \
      && sed 's|^|./|' "$tmp/names" | git hash-object --stdin-paths 2>/dev/null \
         | paste -d'\0' - <(sed 's|^|  |' "$tmp/names") | sort > "$tmp/actual" ) || true
    if [ -s "$tmp/actual" ] && cmp -s "$tmp/expected" "$tmp/actual"; then
      say "  staging reused ($(find "$dir" -name '*.agdai' | wc -l) interfaces cached)"
      rm -rf "$tmp"; return 0
    fi
    say "  staging is stale -- re-extracting (cached interfaces discarded)"
    rm -rf "$dir"
  fi

  mkdir -p "$dir"
  git -C "$REPO" archive "$ref" formal | tar -x --strip-components=1 -C "$dir" \
    || die "git archive $ref failed"
  # An empty repo here bounds Agda's upward search for a project root.
  git -C "$dir" init -q 2>/dev/null
  say "  staged $(find "$dir" -name '*.agda' | wc -l) agda files"
  rm -rf "$tmp"
}

# ------------------------------------------------------------------ running --

# Type-check and dump. Agda writes one .agdai per module as it goes, so an
# interrupted attempt still makes progress; retry as long as each attempt
# advances, and give up once two consecutive attempts add nothing (that means a
# real error, not a resource kill).
run_ref() {
  local dir="$1" raw="$2" log="$3" libs="$4"
  local REF_LABEL="${5:-<ref>}"
  local attempt=0 stalled=0 rc before after

  while :; do
    attempt=$((attempt + 1))
    before=$(find "$dir" -name '*.agdai' | wc -l)
    say "  attempt $attempt (interfaces: $before)"

    ( cd "$dir" && unset AGDA_DIR && LC_ALL="$LOCALE" \
      "$AGDA" +RTS "${RTS_OPTS[@]}" -RTS \
        --library-file="$libs" --transliterate -vwarning:1 \
        --write-ast="$ENTRY" --ast-file="$raw" \
        "$ENTRY_MODULE" ) >> "$log" 2>&1
    rc=$?

    after=$(find "$dir" -name '*.agdai' | wc -l)
    [ $rc -eq 0 ] && { say "  agda finished cleanly ($after interfaces)"; return 0; }

    # A heap exhaustion names its victim: the last module Agda announced before
    # dying. Surfacing it beats making the reader dig through the log, and it is
    # the module whose name goes in the retry command.
    local culprit="" why="rc=$rc"
    if tail -40 "$log" | grep -q "Heap exhausted"; then
      culprit=$(grep -a "Checking" "$log" | tail -1 | sed 's/^ *Checking //;s/ *(.*//')
      why="heap exhausted on ${culprit:-unknown}"
    fi

    if [ "$after" -gt "$before" ]; then
      stalled=0
      say "  interrupted at $after interfaces ($why) -- resuming"
    else
      stalled=$((stalled + 1))
      say "  no progress ($why), stall $stalled/2"
      if [ $stalled -ge 2 ]; then
        if [ -n "$culprit" ]; then
          say "  giving up: $culprit does not fit in $HEAP with $COMPACT."
          say "  retry that ref alone with more headroom, e.g.:"
          say "    HEAP=6G COMPACT=-c20 $0 $REF_LABEL"
        else
          say "  giving up; last lines of $log:"
          tail -20 "$log" | sed 's/^/    /'
        fi
        return 1
      fi
    fi
  done
}

# ------------------------------------------------------------ postprocessing --

# Rewrite staging paths back to repo-relative and stamp provenance into the
# file, so a dump stays self-identifying even if it is renamed or moved.
finish_ref() {
  python3 - "$1" "$2" "$3" "$4" "$5" "$6" <<'PY'
import json, os, sys
raw, stage, out, ref, sha, entry = sys.argv[1:7]
d = json.load(open(raw))
stage = os.path.normpath(stage) + os.sep

# Agda reports paths relative to the project root, which here is the staging
# tree -- and the staging tree *is* formal/, extracted with --strip-components.
# So a relative path just needs the prefix put back. Absolute paths are handled
# too, for dumps made by an older Agda that emitted them.
def fix(p):
    if not p:
        return p
    if p.startswith(stage):
        return 'formal/' + p[len(stage):]
    if os.path.isabs(p):
        return p
    return 'formal/' + p

def fix_range(r):
    if not r or ':' not in r:
        return r
    path, _, pos = r.partition(':')
    return fix(path) + ':' + pos

for key in ('reachable', 'trustBase'):
    for e in d.get(key, []):
        if e.get('source'):
            e['source'] = fix(e['source'])
        if e.get('range'):
            e['range'] = fix_range(e['range'])

d['provenance'] = {'repo': 'once-lang', 'ref': ref, 'commit': sha,
                   'entryPoint': entry, 'paths': 'repo-relative'}
json.dump(d, open(out, 'w'), ensure_ascii=False, indent=1)

c = d.get('counts', {})
a = d.get('assumptions', {})
print(f"  wrote {out}  ({os.path.getsize(out):,} bytes)")
print(f"  definitions: inProject={c.get('inProject')} outside={c.get('outside')} "
      f"generated={c.get('generated')} (of {c.get('reachable')} reachable)")
# Counted per site: one pragma over a mutual block is one assumption, however
# many definitions inherit it.
print(f"  assumptions: obligations={a.get('obligations')} "
      f"assertions={a.get('assertions')}")
PY
}

# --------------------------------------------------------------------- main --

declare -a SUMMARY=()
status=0

for ref in "${REFS[@]}"; do
  rule
  sha="$(git -C "$REPO" rev-parse --short "$ref" 2>/dev/null)" \
    || die "cannot resolve ref '$ref' in $REPO"
  slug="${ref//\//-}"
  dir="$WORK/$slug"
  raw="$WORK/$slug.raw.json"
  libs="$WORK/$slug.libs.txt"
  log="$WORK/$slug.log"
  out="$OUT_DIR/ast-$ENTRY_SLUG-$slug-$sha.json"

  say "ref $ref ($sha)"
  stage_ref "$ref" "$dir"

  printf '%s\n%s\n' "$STDLIB" "$dir/Once.agda-lib" > "$libs"
  : > "$log"

  if run_ref "$dir" "$raw" "$log" "$libs" "$ref" && [ -f "$raw" ]; then
    finish_ref "$raw" "$dir" "$out" "$ref" "$sha" "$ENTRY"
    SUMMARY+=("ok    $ref ($sha) -> $(basename "$out")")
  else
    SUMMARY+=("FAIL  $ref ($sha) -- see $log")
    status=1
  fi
done

rule
say "summary"
printf '  %s\n' "${SUMMARY[@]}"
exit $status
