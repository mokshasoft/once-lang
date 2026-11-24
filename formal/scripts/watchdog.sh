#!/usr/bin/env bash
# watchdog.sh SECS CMD… : run CMD (its stdout and stderr merged and passed through) and kill it if it
# prints no new line for SECS seconds. Long tools print a line as each unit of work starts (Agda
# "Checking M", GHC "[i of n] Compiling M", a test runner one line per test), so a silence of SECS
# means one unit ran over its cap, and the last line printed names it. The cap is per unit, so it
# does not grow with the number of modules or tests.
#
# On a kill: prints "WATCHDOG: … stuck after: <last line>" and exits 124 (as timeout(1)).
# Otherwise: exits with CMD's status, after one line naming the slowest unit
# ("watchdog: slowest unit Ns after: <line>") so units near their cap show up before they cross it.
# WATCHDOG_QUIET=1 drops that last line.
set -u
secs="${1:?usage: watchdog.sh SECS CMD…}"; shift
[ $# -gt 0 ] || { echo "usage: watchdog.sh SECS CMD…" >&2; exit 2; }

fifo="$(mktemp -u)"; mkfifo "$fifo" || exit 2
# Its own process group (a background job of a non-interactive shell is no group leader, so setsid
# execs in place and $! is the group's id): a kill reaches CMD's whole subtree.
setsid "$@" > "$fifo" 2>&1 < /dev/null &
pid=$!
exec 3< "$fifo"; rm -f "$fifo"

last="(no output yet)"; t_last=$SECONDS; max=0; max_line="$last"
while :; do
  line=""
  if IFS= read -r -t "$secs" line <&3; then
    printf '%s\n' "$line"
    gap=$((SECONDS - t_last)); [ "$gap" -gt "$max" ] && { max=$gap; max_line="$last"; }
    last="$line"; t_last=$SECONDS
  elif [ $? -gt 128 ]; then
    [ -n "$line" ] && printf '%s' "$line"
    echo "WATCHDOG: no output for ${secs}s, killed; stuck after: $last" >&2
    kill -TERM -- "-$pid" 2>/dev/null; sleep 3; kill -KILL -- "-$pid" 2>/dev/null
    wait "$pid" 2>/dev/null
    exit 124
  else
    [ -n "$line" ] && printf '%s\n' "$line"   # a last line without its newline
    break
  fi
done
wait "$pid"; rc=$?
gap=$((SECONDS - t_last)); [ "$gap" -gt "$max" ] && { max=$gap; max_line="$last"; }
[ -n "${WATCHDOG_QUIET:-}" ] || echo "watchdog: slowest unit ${max}s after: $max_line" >&2
exit "$rc"
