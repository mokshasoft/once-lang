#!/usr/bin/env bash
# agda-safe.sh: run `make agda MODULE=…` (or any make target) inside a
# systemd-user transient scope with a hard cgroup memory cap, so the
# kernel OOM killer can only target the agda subtree — never claude.
#
# Why the previous ulimit-based approach failed:
#   `ulimit -v` caps virtual address space per-process, but does NOT
#   prevent system-wide memory pressure. When this 7.5 GiB box already
#   has swap heavily used, agda's growth pushes the global watermark
#   below the kernel's threshold, and the OOM killer scans ALL
#   processes — picking by oom_score, not by who triggered the
#   pressure. Even with oom_score_adj=1000 on the agda subtree, the
#   killer sometimes still picks the claude harness (or its parent
#   shell) when scores tie or when fork() bombs the accounting.
#
#   A cgroup v2 memory.max limit is enforced LOCALLY: when exceeded,
#   only processes IN THAT CGROUP are eligible for OOM-kill. Claude is
#   outside the cgroup, so it's structurally protected. Verified on
#   this machine: a 64 MiB scope OOM'd the child with SIGKILL while
#   the parent shell continued running.
#
# Strategy:
#   1. systemd-run --user --scope        — transient cgroup, cleaned
#      up automatically when make exits.
#   2. -p MemoryMax=<cap>                — hard RAM cap (default 5.5G).
#   3. -p MemorySwapMax=<cap>            — bounded swap (default 2G);
#      prevents agda from joining the global swap-thrash that triggers
#      kernel OOM in the first place.
#   4. echo 1000 > oom_score_adj         — belt-and-braces inside the
#      scope, so the cgroup OOM-killer prefers agda over the wrapper.
#   5. Fallback to legacy ulimit path if systemd-run is missing.
#
# Usage:
#   formal/scripts/agda-safe.sh MODULE=Once/CCC/Machine/IR/PairWF2.agda
#   formal/scripts/agda-safe.sh malonzo MODULE=Once/CCC/Machine/IR/SimpleWF.agda
#
# Environment overrides:
#   AGDA_SAFE_MEM_MAX=4G       (default 5500M)
#   AGDA_SAFE_SWAP_MAX=1G      (default 2G)
#   AGDA_SAFE_NO_CGROUP=1      force ulimit fallback
#
# Output goes to stdout; caller redirects. Exit code mirrors make's,
# or 137 when the cgroup OOM-killer hit agda.

set -u

MEM_MAX="${AGDA_SAFE_MEM_MAX:-5500M}"
SWAP_MAX="${AGDA_SAFE_SWAP_MAX:-2G}"

cd "$(dirname "$0")/.." || exit 2

# If no target given, default to `agda`.
case "${1:-}" in
  ""|MODULE=*) set -- agda "$@" ;;
esac

cgroup_available() {
  [ -z "${AGDA_SAFE_NO_CGROUP:-}" ] \
    && command -v systemd-run >/dev/null 2>&1 \
    && [ -e /sys/fs/cgroup/cgroup.controllers ] \
    && systemctl --user show-environment >/dev/null 2>&1
}

# Set sentinel so the Makefile's `agda` / `malonzo` recipes skip their
# self-wrap when they re-invoke make inside this scope.
export AGDA_SAFE_ACTIVE=1

if cgroup_available; then
  # Run inside a transient user scope. The inner bash sets the agda
  # subtree's oom_score_adj so the kernel prefers it even when the
  # cgroup OOM-killer is comparing siblings.
  exec systemd-run --user --scope --quiet \
    -p MemoryMax="$MEM_MAX" \
    -p MemorySwapMax="$SWAP_MAX" \
    -- bash -c '
      if [ -w /proc/self/oom_score_adj ]; then
        echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
      fi
      export AGDA_SAFE_ACTIVE=1
      exec make "$@"
    ' bash "$@"
fi

# --- Legacy fallback: ulimit only -----------------------------------
echo "WARNING: cgroup-based isolation unavailable; using ulimit fallback." >&2
echo "         claude may still be OOM-killed under heavy memory pressure." >&2

LIMIT_KB="${AGDA_SAFE_LIMIT_KB:-5500000}"
if [ -w /proc/self/oom_score_adj ]; then
  echo 1000 > /proc/self/oom_score_adj 2>/dev/null || true
fi
ulimit -v "$LIMIT_KB" 2>/dev/null || true
exec make "$@"
