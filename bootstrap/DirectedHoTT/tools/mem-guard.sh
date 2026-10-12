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
#   * STARTS (or restarts) CMD when MemAvailable ≥ START_MB has held for
#     SETTLE seconds — also while a foreign agda runs, against the lower
#     SHARE_START_MB (the RESERVE_MB stop below is what protects the other
#     check, so the start bar only has to promise some useful work): idle
#     memory is used, not waited out;
#   * STOPS CMD (its whole process group, TERM then KILL) when
#       - SHARING (a foreign agda is running): MemAvailable < RESERVE_MB.
#         We are the guest: whoever is growing, ours yields, so the other
#         session's check never meets an OOM because of us (both run at
#         oom_score_adj 1000, so the kernel would kill the bigger one);
#       - ALONE: the memory the rest of the machine leaves us (MemAvailable
#         + our own RSS) drops below STOP_MB, i.e. some other process has
#         started taking memory (our own growth is check.sh's cgroup's job);
#   * exits with CMD's exit code once CMD finishes without being stopped.
#
# After a stop while sharing, a restart beside a foreign agda waits twice
# as long as the last one (SETTLE, 2·SETTLE, … up to 600 s): the other
# check is evidently big, and re-running into it again costs both of us.
# Alone, the wait is SETTLE again.
#
# SHARE=0 restores the old policy: never run beside a foreign agda.
#
# Restarting from scratch is cheap for the sweep: finished interfaces are
# reused, only the module in flight is lost.  CMD's output and the guard's
# events ("mem-guard: …") are both appended to LOG.
#
# "Foreign" = an agda process outside CMD's process group.  Kills go to
# that process group only, never machine-wide.
#
# Tunables (env): START_MB (4500), SHARE_START_MB (3000), STOP_MB (3000),
# RESERVE_MB (1500),
# SETTLE (60), POLL (3), SHARE (1).
set -u
set -m   # job control: each run of CMD gets its own process group, pgid = its pid
[ "$#" -ge 3 ] && [ "$2" = "--" ] || { echo "usage: $0 LOG -- CMD [ARGS...]" >&2; exit 2; }
LOG="$1"; shift 2
START_MB="${START_MB:-4500}"
STOP_MB="${STOP_MB:-3000}"
RESERVE_MB="${RESERVE_MB:-1500}"
SHARE_START_MB="${SHARE_START_MB:-3000}"
SHARE="${SHARE:-1}"
SETTLE="${SETTLE:-60}"
POLL="${POLL:-3}"
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
backoff="$SETTLE"   # settle time beside a foreign agda
while :; do
  # wait for enough free memory (and, with SHARE=0, no foreign agda),
  # held for SETTLE seconds
  clear_since=
  while :; do
    f=$(foreign_agda ""); a=$(avail_mb)
    if [ -z "$f" ]; then backoff="$SETTLE"; need="$SETTLE"; bar="$START_MB"
    else need="$backoff"; bar="$SHARE_START_MB"; fi
    if { [ "$SHARE" = 1 ] || [ -z "$f" ]; } && [ "$a" -ge "$bar" ]; then
      now=$(date +%s); clear_since=${clear_since:-$now}
      [ $((now - clear_since)) -ge "$need" ] && break
    else
      clear_since=
    fi
    sleep "$POLL"
  done

  run=$((run + 1))
  f=$(foreign_agda "")
  say "start #$run (MemAvailable ${a} MB${f:+, sharing with agda $(echo $f | tr '\n' ' ')}): $*"
  "$@" >> "$LOG" 2>&1 &
  child=$!

  reason=
  while kill -0 "$child" 2>/dev/null; do
    sleep "$POLL"
    kill -0 "$child" 2>/dev/null || break
    f=$(foreign_agda "$child"); a=$(avail_mb)
    if [ -n "$f" ]; then
      if [ "$SHARE" != 1 ]; then reason="foreign agda (pid $(echo $f | tr '\n' ' '))"; break; fi
      if [ "$a" -lt "$RESERVE_MB" ]; then
        reason="sharing with agda $(echo $f | tr '\n' ' ')and MemAvailable ${a} MB < ${RESERVE_MB} MB"
        backoff=$((backoff * 2)); [ "$backoff" -le 600 ] || backoff=600; break
      fi
      continue
    fi
    r=$(group_rss_mb "$child")
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
