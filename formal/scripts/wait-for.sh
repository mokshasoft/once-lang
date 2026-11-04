#!/usr/bin/env bash
# wait-for.sh PATTERN|PID...  — block until the given processes have exited.
#
# Resolves PATTERN to PIDs ONCE (pgrep -f), excluding this script and all its
# ancestors (whose command lines contain PATTERN too — the self-match bug that
# made `until ! pgrep -f X` loops wait forever). Then waits on those PIDs only.
# Fails loudly if nothing matches, so a typo can't masquerade as "done".
set -u
[ $# -ge 1 ] || { echo "usage: wait-for.sh PATTERN | PID..." >&2; exit 2; }

ancestors() { local p=$$; while [ "$p" -gt 1 ]; do echo "$p"; p=$(ps -o ppid= -p "$p" | tr -d ' '); done; }

if [[ "$*" =~ ^[0-9\ ]+$ ]]; then
  pids="$*"
else
  skip=$(ancestors)
  pids=""
  for p in $(pgrep -f -- "$1"); do
    grep -qxF "$p" <<<"$skip" && continue                       # us or an ancestor
    [ "$(ps -o ppid= -p "$p" 2>/dev/null | tr -d ' ')" = "$$" ] && continue  # our own subshells
    kill -0 "$p" 2>/dev/null && pids="$pids $p"
  done
fi
[ -n "${pids// }" ] || { echo "wait-for: no process matches '$*'" >&2; exit 1; }

for p in $pids; do
  echo "waiting on $p: $(ps -o args= -p "$p" 2>/dev/null | cut -c1-150)"
done
for p in $pids; do tail --pid="$p" -f /dev/null; done
echo "all exited at $(date)"
