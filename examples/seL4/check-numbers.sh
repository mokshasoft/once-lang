#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
#
# Check the seL4 numbers written in the Strata against the pinned kernel.
#
#   check-numbers.sh KERNEL_SRC KERNEL_BUILD ARCH FILE...
#
# KERNEL_SRC is the kernel's source; KERNEL_BUILD the kernel package (its
# `autoconf/`, `gen_config/`, `gen_headers/`); ARCH is x86_64 (riscv64 to
# come). Each FILE keeps its seL4 numbers in one block:
#
#   assembly:   # seL4 numbers               Once:   -- seL4 numbers
#               .equ NAME, VALUE [# = EXPR]          NAME = VALUE [-- = EXPR]
#               # end seL4 numbers                   -- end seL4 numbers
#
# Each entry is checked: VALUE must equal the C expression EXPR, or NAME
# itself when no EXPR is given, as the kernel's and libsel4's headers
# define it (syscall and invocation numbers, object types, struct
# offsets, ...). A name the headers do not know fails the compile. EXPR
# may also use MSG_INFO(label, capsUnwrapped, extraCaps, length) (the
# kernel's message info constructor) and RIGHTS_BIT(capAllowRead) (the
# rights word the kernel reads as that right alone).
set -euo pipefail

if [ "$#" -lt 4 ]; then
    echo "usage: $0 KERNEL_SRC KERNEL_BUILD ARCH FILE..." >&2
    exit 2
fi
SRC=$1; BUILD=$2; ARCH=$3; shift 3

case "$ARCH" in
    x86_64) ARCH_INC=x86; PLAT=pc99 ;;
    *) echo "check-numbers: no header set for $ARCH" >&2; exit 2 ;;
esac

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# One `CHECK(file, name, value, expr)` per entry
for f in "$@"; do
    awk -v file="$f" '
        /^(#|--) seL4 numbers$/      { inside = 1; seen = 1; next }
        /^(#|--) end seL4 numbers$/  { inside = 0; next }
        inside && /^\.equ / {
            line = $0; expr = ""
            if (match(line, /# = .*/)) { expr = substr(line, RSTART + 4); line = substr(line, 1, RSTART - 1) }
            sub(/^\.equ[ \t]+/, "", line)
            name = line; sub(/[ \t]*,.*/, "", name)
            value = line; sub(/^[^,]*,[ \t]*/, "", value); sub(/[ \t]+$/, "", value)
            if (expr == "") expr = name
            printf "    CHECK(\"%s\", \"%s\", %s, %s);\n", file, name, value, expr
            next
        }
        inside && /^[A-Za-z_][A-Za-z_0-9]* = / {
            line = $0; expr = ""
            if (match(line, /-- = .*/)) { expr = substr(line, RSTART + 5); line = substr(line, 1, RSTART - 1) }
            name = line; sub(/[ \t]*=.*/, "", name)
            value = line; sub(/^[^=]*=[ \t]*/, "", value); sub(/[ \t]+$/, "", value)
            if (expr == "") expr = name
            printf "    CHECK(\"%s\", \"%s\", %s, %s);\n", file, name, value, expr
            next
        }
        inside && /^[A-Za-z_][A-Za-z_0-9]* :/ { next }      # a Once type signature
        inside && /[^ \t]/ && !/^(#|--)/ {
            printf "check-numbers: %s: not an entry: %s\n", file, $0 > "/dev/stderr"; exit 1
        }
        END { if (!seen) { printf "check-numbers: %s has no seL4 numbers block\n", file > "/dev/stderr"; exit 1 } }
    ' "$f" >> "$WORK/checks.inc"
done

cat > "$WORK/probe.c" <<'EOF'
#include <autoconf.h>
#include <stddef.h>
#include <stdio.h>
#include <sel4/simple_types.h>
#include <sel4/sel4_arch/simple_types.h>
#include <sel4/macros.h>
#include <sel4/constants.h>
/* The kernel's generated bitfields: seL4_MessageInfo_t, seL4_CapRights_t */
#include <sel4/shared_types_gen.h>
/* libsel4's other names for words these headers use */
typedef seL4_Word seL4_NodeId;
typedef seL4_Word seL4_Domain;
typedef unsigned long word_t;
#define UNUSED __attribute__((unused))
#include <sel4/shared_types.h>
#include <sel4/bootinfo_types.h>
#include <sel4/objecttype.h>
#include <sel4/sel4_arch/objecttype.h>
#include <sel4/arch/objecttype.h>
#include <sel4/sel4_arch/types.h>
#include <sel4/sel4_arch/constants.h>
#include <sel4/errors.h>
#include <api/invocation.h>
#include <arch/api/sel4_invocation.h>
#include <arch/api/syscall.h>

/* The rights word with only the bit the kernel's getter reads */
static long rights_bit(uint64_t (*get)(seL4_CapRights_t)) {
    for (int k = 0; k < 64; k++) {
        seL4_CapRights_t r = {{1ull << k}};
        if (get(r)) return 1L << k;
    }
    return -1;
}
#define RIGHTS_BIT(field) rights_bit(seL4_CapRights_get_##field)
/* Message info layout, from the kernel's constructor */
#define MSG_INFO(label, caps_unwrapped, extra_caps, length) \
    ((long)seL4_MessageInfo_new(label, caps_unwrapped, extra_caps, length).words[0])

static int failures, checks;
#define CHECK(file, name, value, expr) do { \
        long v = (long)(value), e = (long)(expr); checks++; \
        if (v != e) { failures++; \
            printf("%s: %s is %ld, the kernel says %ld (%s)\n", file, name, v, e, #expr); } \
    } while (0)

int main(void) {
#include "checks.inc"
    printf("check-numbers: %d checked, %d wrong\n", checks, failures);
    return failures != 0;
}
EOF

# The kernel's own include/ (config.h, util.h for the generated bitfields)
# comes after the C library's, which it would otherwise shadow
cc -I"$BUILD/autoconf" -I"$BUILD/gen_config" -I"$BUILD/gen_headers" -I"$BUILD/generated" \
   -I"$SRC/libsel4/include" -I"$SRC/libsel4/arch_include/$ARCH_INC" \
   -I"$SRC/libsel4/sel4_arch_include/$ARCH" -I"$SRC/libsel4/mode_include/64" \
   -I"$SRC/libsel4/sel4_plat_include/$PLAT" -idirafter "$SRC/include" \
   "$WORK/probe.c" -o "$WORK/probe"
"$WORK/probe"
