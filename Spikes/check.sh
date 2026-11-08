#!/usr/bin/env bash
# Type-check spike modules (Spikes/README.md), each in its own Agda process under
# formal/scripts/agda-safe.sh's cgroup cap, like every other Agda run here.
#
#   Spikes/check.sh LinCore/NbEPLinCore.agda [more.agda ...]
#   Spikes/check.sh                 # every .agda under Spikes/, in path order
#
# The spikes import nothing outside Spikes/ but the standard library (no
# formal/), found in the nix store as formal/Makefile finds it.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SAFE="$HERE/../formal/scripts/agda-safe.sh"
cd "$HERE"
unset AGDA_DIR   # as formal/Makefile: a stale nix AGDA_DIR only warns
STD_LIB=$(find /nix/store -maxdepth 2 -name standard-library.agda-lib 2>/dev/null | head -1)
[ -n "$STD_LIB" ] || { echo "check.sh: standard-library not found in the nix store" >&2; exit 2; }
if [ $# -eq 0 ]; then
  mapfile -t mods < <(find . -name '*.agda' -not -path './_build/*' -printf '%P\n' | LC_ALL=C sort)
else
  mods=("$@")
fi
status=0
for m in "${mods[@]}"; do
  start=$(date +%s)
  if "$SAFE" --exec agda --library-file=<(echo "$STD_LIB"; echo "$HERE/spikes.agda-lib") "$m" > "$HERE/.last-check.log" 2>&1; then
    echo "ok    $m ($(( $(date +%s) - start )) s)"
  else
    echo "FAIL  $m"; grep -v '^ *Checking' "$HERE/.last-check.log" | head -40; status=1
  fi
done
exit $status
