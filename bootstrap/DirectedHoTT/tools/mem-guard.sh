#!/usr/bin/env bash
# Run a long agda job (a sweep, a check) so that it yields the machine to
# other sessions automatically.
#
# Usage (from bootstrap/):
#   DirectedHoTT/tools/mem-guard.sh LOG -- CMD [ARGS...]
#
# The box is shared (7.5 GiB, other Claude sessions run agda too) and two
# agda checks at once OOM-kill each other.  The guard:
#
#   * STARTS (or restarts) CMD only when no foreign agda is running and
#     MemAvailable ≥ START_MB, both holding for SETTLE seconds;
#   * STOPS CMD (its whole process group, TERM then KILL) as soon as a
#     foreign agda appears, or the memory the rest of the machine leaves us
#     (MemAvailable + our own RSS) drops below STOP_MB, i.e. some other
#     process has started taking memory;
#   * exits with CMD's exit code once CMD finishes without being stopped.
#
# Restarting from scratch is cheap for the sweep: finished interfaces are
# reused, only the module in flight is lost.  CMD's output and the guard's
# events ("mem-guard: …") are both appended to LOG.
#
# "Foreign" = an agda process outside CMD's process group.  Kills go to
# that process group only, never machine-wide.
#
# Tunables (env): START_MB (4500), STOP_MB (3000), SETTLE (60), POLL (5).
set -u
set -m   # job control: each run of CMD gets its own process group, pgid = its pid
[ "$#" -ge 3 ] && [ "$2" = "--" ] || { echo "usage: $0 LOG -- CMD [ARGS...]" >&2; exit 2; }
LOG="$1"; shift 2
START_MB="${START_MB:-4500}"
STOP_MB="${STOP_MB:-3000}"
SETTLE="${SETTLE:-60}"
POLL="${POLL:-5}"
AGDA_RE="${AGDA_RE:-^/nix/store/[^ ]*-Agda-[^ ]*/bin/agda }"   # overridable for testing

say() { echo "mem-guard: $(date '+%F %T') $*" >> "$LOG"; }
avail_mb() { awk '/^MemAvailable:/ { print int($2 / 1024) }' /proc/meminfo; }

# agda PIDs not in process group $1 (empty $1: all of them)
foreign_agda() {
  local p g
  for p in $(pgrep -f "$AGDA_RE"); do
    g=$(ps -o pgid= -p "$p" 2>/dev/null | tr -d ' ') || continue
    [ -n "$g" ] && [ "$g" != "${1:-}" ] && echo "$p"
  done
}

# resident memory of process group $1, in MB
group_rss_mb() {
  ps -eo pgid=,rss= | awk -v g="$1" '$1 == g { s += $2 } END { print int(s / 1024) }'
}

child=
stop_child() {
  [ -n "$child" ] || return 0
  kill -TERM -- "-$child" 2>/dev/null
  for _ in $(seq 20); do kill -0 -- "-$child" 2>/dev/null || break; sleep 1; done
  kill -KILL -- "-$child" 2>/dev/null
  wait "$child" 2>/dev/null
  child=
}
trap 'say "guard terminated"; stop_child; exit 130' INT TERM

run=0
while :; do
  # wait for a clear machine, held for SETTLE seconds
  clear_since=
  while :; do
    f=$(foreign_agda ""); a=$(avail_mb)
    if [ -z "$f" ] && [ "$a" -ge "$START_MB" ]; then
      now=$(date +%s); clear_since=${clear_since:-$now}
      [ $((now - clear_since)) -ge "$SETTLE" ] && break
    else
      clear_since=
    fi
    sleep "$POLL"
  done

  run=$((run + 1))
  say "start #$run (MemAvailable ${a} MB): $*"
  "$@" >> "$LOG" 2>&1 &
  child=$!

  reason=
  while kill -0 "$child" 2>/dev/null; do
    sleep "$POLL"
    kill -0 "$child" 2>/dev/null || break
    f=$(foreign_agda "$child")
    if [ -n "$f" ]; then reason="foreign agda (pid $(echo $f | tr '\n' ' '))"; break; fi
    a=$(avail_mb); r=$(group_rss_mb "$child")
    if [ $((a + r)) -lt "$STOP_MB" ]; then
      reason="others need memory (MemAvailable ${a} MB + ours ${r} MB < ${STOP_MB} MB)"; break
    fi
  done

  if [ -n "$reason" ]; then
    say "stop #$run: $reason"
    stop_child
    continue
  fi
  wait "$child"; rc=$?; child=
  say "done #$run: rc=$rc"
  exit "$rc"
done
