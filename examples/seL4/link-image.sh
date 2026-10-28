#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
#
# Build an seL4 image of several Once programs (plan 0.127 B.1).
#
#   link-image.sh ONCE STRATA OUT ROOT.once [PROGRAM.once ...]
#
# ROOT is program 0, the root task (the kernel starts it at the Host's
# entry). Each further PROGRAM is program 1, 2, 3, in order: it is built
# alone, and its `_start` (its only global symbol) is renamed
# `once_program_<n>`, which the seL4 Host's program table names.
# Interpretation objects are linked once each. x86_64 only for now.
set -euo pipefail

if [ "$#" -lt 4 ]; then
    echo "usage: $0 ONCE STRATA OUT ROOT.once [PROGRAM.once ...]" >&2
    exit 2
fi
ONCE=$1; STRATA=$2; OUT=$3; shift 3

ARCH=x86_64
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

n=0
objects=()
for src in "$@"; do
    "$ONCE" build --save-temps --target "$ARCH" --host SeL4 --strata "$STRATA" \
        "$src" -o "$WORK/p$n" > /dev/null
    if [ "$n" -gt 0 ]; then
        objcopy --redefine-sym "_start=once_program_$n" "$WORK/p$n.o"
    fi
    objects+=("$WORK/p$n.o")
    n=$((n + 1))
done

# One object per Interpretation module (`p<n>.<module path>.o`)
for obj in "$WORK"/p*.Interpretations.*.o; do
    module=${obj#"$WORK"/p*.}
    [ -e "$WORK/impl.$module" ] || cp "$obj" "$WORK/impl.$module"
done
shopt -s nullglob
impls=("$WORK"/impl.*)

ld "${objects[@]}" "${impls[@]}" "$WORK/p0.Host.SeL4.o" \
    "$STRATA/Hosts/SeL4/Host.$ARCH.ld" -o "$OUT"
