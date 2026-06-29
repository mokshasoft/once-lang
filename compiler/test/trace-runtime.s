# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson and contributors
#
# Runtime for TraceSpec's OBSERVABLE effect-trace tests.
#
# A trace program declares the SigOps LOCALLY:
#     signature emit : Eff Int Unit
#     signature exit : Eff Int Unit
# so the verified codegen calls them by their own (unqualified) symbol —
# `Once.Target.Symbol.once-symbol-own name` = "once_" ++ <len> ++ name. Hence
# the symbols below are just the signature names, `once_4emit` / `once_4exit`;
# there is no module-path mangling to track (that only arises for imported
# strata interpretations). TraceSpec assembles this file and links it with the
# program object the compiler produces.
#
# Once SysV convention: the SigOp's Int argument arrives in %rdi.
#   emit : Eff Int Unit  -- write the argument's low byte to stdout (fd 1), so
#                           the emitted sequence is observable; return Unit (0).
#   exit : Eff Int Unit  -- exit_group(status = arg); does not return.

.text

.align 16
.global once_4emit
.type once_4emit, @function
once_4emit:
    movb    %dil, -1(%rsp)      # stash the argument's low byte (red zone)
    leaq    -1(%rsp), %rsi      # rsi = buffer
    movq    $1, %rdi            # rdi = fd (stdout)
    movq    $1, %rdx            # rdx = count (1 byte)
    movq    $1, %rax            # rax = SYS_write
    syscall
    xorq    %rax, %rax          # return Unit (0)
    ret
.size once_4emit, .-once_4emit

.align 16
.global once_4exit
.type once_4exit, @function
once_4exit:
    movq    $231, %rax          # rax = SYS_exit_group (status already in rdi)
    syscall
.size once_4exit, .-once_4exit
