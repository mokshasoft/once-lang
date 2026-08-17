-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.RegRoles
--
-- x86-32's answer to `FlatCore.RegRoles` — THE THIRD INSTANCE, and the one
-- that could not be written until plan 0.66 (D108).
--
-- Plan 0.65's G1c measured that this record was UNFILLABLE here: eight GPRs,
-- nine roles counting the frame pointer, `Input2` and `Scratch` both `edx`, and
-- no free register to move to — `ebp` is the live frame anchor every i386
-- epilogue restores `%esp` from, so reassigning it is a SIGSEGV, not a fix.
-- D108 resolved it by deleting the role rather than finding a register:
-- `Input2` had no producer on any arch. Seven roles remain, and x86-32 has
-- exactly seven registers to spare.
--
-- Every assignment below is read off `AbstractToX86-32`, the same way the other
-- two were read off their emitters — NOT off its comments, which called `%edi`
-- "Input2" while `count-*` is what writes it (corrected by D108):
--
--     mov eax, ecx               Output := Input1     → eax, ecx
--     mov eax, esi ; add esi, n  alloc-heap           → esi is the frontier
--     mov ebx, ecx               save-closure-reg     → ebx
--     mov edi, 0 / add edi, 1    count-zero/-inc      → edi
--     mov edx, 1 / cmp edx, 0    scratch-one/branch   → edx
--     sub esp, n                 alloc-stack          → esp
--
-- Seven roles, seven distinct registers — INJECTIVE, with `ebp` reserved (it
-- is not a role: it is the frame ceremony `Once/Target/X86-32.agda` emits in
-- the TEXT, outside the abstract trace entirely).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-32.RegRoles where

open import Once.CCC.Target.X86-32.Syntax using (Reg; eax; ebx; ecx; edx; esi; edi; esp)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-scratch; role-count)

x86-32-reg-of : Role → Reg
x86-32-reg-of role-sp      = esp
x86-32-reg-of role-clos    = ebx
x86-32-reg-of role-heap    = esi
x86-32-reg-of role-out     = eax
x86-32-reg-of role-in1     = ecx
x86-32-reg-of role-scratch = edx
x86-32-reg-of role-count   = edi

x86-32-roles : RegRoles Reg
x86-32-roles = record { reg-of = x86-32-reg-of }

open RegRoles x86-32-roles public
