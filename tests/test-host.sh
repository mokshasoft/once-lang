# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
#
# Which Host the exit tests run under (plan 0.140 §3.6), sourced by the
# run-exit-tests scripts after they set ARCH and LINUX_RUN (how a Linux
# executable of that arch runs: nothing native, `qemu-i386`, `qemu-riscv64`).
#
#   ONCE_TEST_HOST=linux (default)  the Linux Host, run as a process.
#   ONCE_TEST_HOST=bare             the bare-metal Host of the arch's QEMU
#                                   machine: Bare/Virt on riscv64, Bare/PC on
#                                   x86_32 and x86_64, booted by qemu-system
#                                   with the UART on stdout.
#
# It sets:
#   HOST_FLAGS  the `once build` flags that pick the Host;
#   RUN         the command prefix that runs an image (under a wall-clock cap);
#   END_TABLE   the Host's end table, as `tests/check-trace.py` names it;
#   HOST_LABEL  for the summary line.
# and `host_skip FILE`, which prints why FILE cannot run under this Host (a
# program importing an Interpretation of the Linux Host runs only there).
ONCE_TEST_HOST="${ONCE_TEST_HOST:-linux}"
case "$ONCE_TEST_HOST" in
  linux)
    HOST_FLAGS=()
    RUN=(timeout 10 "${LINUX_RUN[@]}")
    END_TABLE=linux
    HOST_LABEL=Linux
    ;;
  bare)
    QEMU_COMMON=(-display none -serial stdio -monitor none -no-reboot)
    case "$ARCH" in
      riscv64)
        HOST_FLAGS=(--host Bare/Virt)
        RUN=(timeout 10 qemu-system-riscv64 -machine virt -bios none "${QEMU_COMMON[@]}" -kernel)
        END_TABLE=virt
        HOST_LABEL=Bare/Virt ;;
      x86_64|x86_32)
        qemu=qemu-system-x86_64; [ "$ARCH" = x86_32 ] && qemu=qemu-system-i386
        HOST_FLAGS=(--host Bare/PC)
        RUN=(timeout 10 "$qemu" "${QEMU_COMMON[@]}" -device isa-debug-exit,iobase=0xf4,iosize=0x04 -kernel)
        END_TABLE=pc
        HOST_LABEL=Bare/PC ;;
      *) echo "no bare-metal Host for $ARCH"; exit 2 ;;
    esac
    command -v "${RUN[2]}" >/dev/null || { echo "missing ${RUN[2]}"; exit 2; }
    ;;
  *) echo "ONCE_TEST_HOST must be linux or bare, not $ONCE_TEST_HOST"; exit 2 ;;
esac

host_skip() {
  [ "$ONCE_TEST_HOST" = linux ] && return 1
  local m
  m="$(grep -oE '^import +I\.Linux\.[A-Za-z0-9_.]+' "$1" | awk '{print $2}' | head -1)"
  [ -n "$m" ] && { echo "needs the Linux Host: imports $m"; return 0; }
  return 1
}
