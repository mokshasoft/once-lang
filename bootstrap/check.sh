#!/usr/bin/env bash
# Typecheck a bootstrap module with the `Once` and `standard-library`
# dependencies registered (bootstrap.agda-lib now depends on both).
#
# Usage (path is relative to bootstrap/):
#   bootstrap/check.sh normalizer/Theory/Eval/Instance.agda
#
# Mirrors the --library-file pattern used by formal/Makefile. Modules that
# do not import Once still build fine; the dependency just makes Once
# available to those that do.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
SELF="$HERE/$(basename "$0")"

#-----------------------------------------------------------------------------
# OOM protection (mirrors formal/scripts/agda-safe.sh)
#-----------------------------------------------------------------------------
# A heavy bootstrap type-check can exhaust RAM and trip the kernel OOM
# killer, which scans ALL processes by oom_score and sometimes picks the
# claude-code harness instead of agda. To prevent that, re-exec this whole
# script inside a transient systemd-user cgroup scope with a hard
# MemoryMax/MemorySwapMax cap: when the cap is hit, only processes IN THAT
# cgroup are eligible for OOM-kill, so agda can only ever kill its own
# subtree — never claude, which lives outside the cgroup.
#
# CAP RATIONALE: 5.5G RAM is the right ceiling for this 7.5 GiB box — it
# leaves GHC's garbage collector the headroom it needs (a hard cap BELOW
# the live-heap-times-GC-overhead just makes agda thrash and balloon, which
# is worse). The cgroup's PRIMARY job is not to avoid the OOM event but to
# steer WHO dies: with oom_score_adj=1000 on the agda subtree, even a
# *global* OOM (e.g. when another session is also using memory) kills agda,
# never the claude harness. So under memory contention you may still see a
# kernel OOM of agda (and possibly an OS popup) — that is acceptable; the
# invariant we guarantee is "claude survives, and the failed check is
# loudly reported" (see the post-run signal check below), NOT "no OOM ever".
#
# The sentinel AGDA_SAFE_ACTIVE breaks the re-exec recursion. Opt out with
# AGDA_SAFE_DISABLE=1 (e.g. CI with its own memory controls); force the
# ulimit fallback with AGDA_SAFE_NO_CGROUP=1. Caps are overridable via
# AGDA_SAFE_MEM_MAX (default 5500M) and AGDA_SAFE_SWAP_MAX (default 2G).
if [ -z "${AGDA_SAFE_ACTIVE:-}" ] && [ -z "${AGDA_SAFE_DISABLE:-}" ]; then
  if [ -z "${AGDA_SAFE_NO_CGROUP:-}" ] \
     && command -v systemd-run >/dev/null 2>&1 \
     && [ -e /sys/fs/cgroup/cgroup.controllers ] \
     && systemctl --user show-environment >/dev/null 2>&1; then
    export AGDA_SAFE_ACTIVE=1
    exec systemd-run --user --scope --quiet \
      -p MemoryMax="${AGDA_SAFE_MEM_MAX:-5500M}" \
      -p MemorySwapMax="${AGDA_SAFE_SWAP_MAX:-2G}" \
      -- bash -c '
        if [ -w /proc/self/oom_score_adj ]; then
          echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
        fi
        exec bash "$@"
      ' bash "$SELF" "$@"
  else
    # Legacy fallback: ulimit only. Caps per-process address space but does
    # NOT structurally protect claude under system-wide memory pressure.
    echo "WARNING: cgroup-based isolation unavailable; using ulimit fallback." >&2
    echo "         claude may still be OOM-killed under heavy memory pressure." >&2
    export AGDA_SAFE_ACTIVE=1
    if [ -w /proc/self/oom_score_adj ]; then
      echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
    fi
    ulimit -v "${AGDA_SAFE_LIMIT_KB:-5500000}" 2>/dev/null || true
  fi
fi

STDLIB="$(find /nix/store -maxdepth 2 -name standard-library.agda-lib 2>/dev/null | head -1)"
[ -z "$STDLIB" ] && { echo "error: standard-library.agda-lib not found in /nix/store" >&2; exit 1; }
LIBF="$(mktemp)"
printf '%s\n' "$STDLIB" "$ROOT/formal/Once.agda-lib" "$ROOT/bootstrap/bootstrap.agda-lib" > "$LIBF"
cd "$HERE"
unset AGDA_DIR
# Run agda WITHOUT `set -e` aborting us, so we always reach the kill check.
rc=0
agda --library-file="$LIBF" "$@" || rc=$?
rm -f "$LIBF"

# OOM / kill detection. A process killed by a signal exits with 128+signo,
# so rc > 128 means agda was terminated (137=SIGKILL/OOM-killer,
# 143=SIGTERM/scope teardown on cgroup OOM) — the type-check did NOT
# complete and produced NO interface. Shout about it on stderr so the
# failure is unmissable however the caller pipes/tails the output, and
# re-map to a stable 137 ("OOM/killed") regardless of which signal landed.
if [ "$rc" -gt 128 ]; then
  sig=$((rc - 128))
  echo "" >&2
  echo "############################################################" >&2
  echo "## check.sh: agda was KILLED by signal $sig (exit code $rc)." >&2
  echo "## This is almost certainly an OUT-OF-MEMORY kill (cgroup cap" >&2
  echo "## ${AGDA_SAFE_MEM_MAX:-5500M} RAM / ${AGDA_SAFE_SWAP_MAX:-2G} swap, or a global OOM under contention)." >&2
  echo "## The type-check did NOT complete — no interface was written." >&2
  echo "############################################################" >&2
  exit 137
fi
exit $rc
