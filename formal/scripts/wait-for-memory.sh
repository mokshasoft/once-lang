#!/usr/bin/env bash
# wait-for-memory.sh: block until the machine has room for a heavy agda run,
# then exit 0 (or run CMD… if given, under the same conditions).
#
# Why: on this 7.5 GiB box an apex check (`make certified`) next to another
# agda (another checkout, another session) OOMs or gets killed for low system
# memory. The right response is never "stop and wait for a human": poll until
# the machine is clear, then go. Run it in the background so the caller is
# woken when it returns.
#
# "Clear" means both:
#   * MemAvailable ≥ WAIT_MEM_MIN_MB (default 4500), and
#   * no other agda process is running (any checkout, any user session).
#
# Usage:
#   formal/scripts/wait-for-memory.sh                      # just wait
#   formal/scripts/wait-for-memory.sh make certified       # wait, then run
#
# Environment overrides:
#   WAIT_MEM_MIN_MB=4500   available memory required, in MiB
#   WAIT_INTERVAL=300      seconds between checks (5 min)
#   WAIT_MAX_HOURS=24      give up (exit 3) after this long

set -u

MIN_MB="${WAIT_MEM_MIN_MB:-4500}"
INTERVAL="${WAIT_INTERVAL:-300}"
MAX_S=$(( ${WAIT_MAX_HOURS:-24} * 3600 ))

avail_mb() { awk '/^MemAvailable:/ { print int($2 / 1024) }' /proc/meminfo; }
other_agda() { pgrep -x agda | tr '\n' ' '; }

start=$(date +%s)
while :; do
  a=$(avail_mb); o=$(other_agda)
  if [ "$a" -ge "$MIN_MB" ] && [ -z "$o" ]; then
    echo "wait-for-memory: clear ($a MiB available, no other agda) at $(date +%T)"
    break
  fi
  if [ $(( $(date +%s) - start )) -ge "$MAX_S" ]; then
    echo "wait-for-memory: gave up after ${WAIT_MAX_HOURS:-24}h ($a MiB, agda pids: ${o:-none})"
    exit 3
  fi
  echo "wait-for-memory: busy at $(date +%T): $a MiB available (need $MIN_MB), agda pids: ${o:-none}; next check in ${INTERVAL}s"
  sleep "$INTERVAL"
done

[ $# -gt 0 ] && exec "$@"
exit 0
