#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""Check a run's observable against a test's expectation (plan 0.140 §3.5).

    check-trace.py HOST WORD_BYTES TRACE_FILE STATUS EXPECTED_TRACE [EXPECTED_END]

The observable is the trace and the end. The trace is what `I.Test.Emit`
writes: one machine word per event (WORD_BYTES: 8, or 4 on x86-32),
little-endian. The end is a kind and carries no value: `returned`, `exhausted`
or `halted`, read from STATUS by HOST's end table, which is its exit device's:

    HOST    returned  exhausted  halted
    linux   0         134        2       (the shell's status; 134 = SIGABRT)
    virt    0         1          2       (Bare/Virt: the SiFive test finisher)
    pc      1         3          5       (Bare/PC: isa-debug-exit, (v << 1) | 1)

EXPECTED_END defaults to `returned`. Any other status is no end of the Spec
(a timeout, or a defect of the trusted base) and fails.

EXPECTED_TRACE is a list like `[1, -3, 0.5]`. An `Int` is compared as its
two's-complement word; a `Float` (a literal with `.`, `e`, `nan` or `inf`) as
the literal rounded once to the target's Float (binary64, or binary32 on
x86-32, D113), a NaN as THE NaN `I.Test.Emit` writes.

Exit status 0 when the observable is the expected one; otherwise 1, with what
differs on stdout.
"""
import re
import struct
import sys

ENDS = {
    "linux": {0: "returned", 134: "exhausted", 2: "halted"},
    "virt": {0: "returned", 1: "exhausted", 2: "halted"},
    "pc": {1: "returned", 3: "exhausted", 5: "halted"},
}


def word(item, nbytes):
    item = item.strip()
    if re.fullmatch(r"-?[0-9]+", item):
        return (int(item) % (1 << (8 * nbytes))).to_bytes(nbytes, "little")
    f = float(item)
    if f != f:
        return (b"\x00\x00\xc0\x7f" if nbytes == 4
                else b"\x00\x00\x00\x00\x00\x00\xf8\x7f")
    return struct.pack("<f" if nbytes == 4 else "<d", f)


def main():
    host, nbytes, path, status, expected = (sys.argv[1], int(sys.argv[2]), sys.argv[3],
                                            int(sys.argv[4]), sys.argv[5])
    want_end = sys.argv[6] if len(sys.argv) > 6 else "returned"
    body = expected.strip()
    if not (body.startswith("[") and body.endswith("]")):
        print(f"bad expected trace {expected!r}")
        return 1
    items = [i for i in body[1:-1].split(",") if i.strip()]
    want = b"".join(word(i, nbytes) for i in items)
    got = open(path, "rb").read()
    errors = []
    end = ENDS[host].get(status, f"no end (status {status})")
    if end != want_end:
        errors.append(f"expected end {want_end}, got {end}")
    if got != want:
        words = [int.from_bytes(got[k:k + nbytes], "little", signed=True)
                 for k in range(0, len(got) - len(got) % nbytes, nbytes)]
        tail = f" and {len(got) % nbytes} stray bytes" if len(got) % nbytes else ""
        errors.append(f"expected trace {expected}, got words {words}{tail}")
    for e in errors:
        print(e)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
