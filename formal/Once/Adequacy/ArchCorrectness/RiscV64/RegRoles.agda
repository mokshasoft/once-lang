-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.RegRoles
--
-- riscv64's answer to `FlatCore.RegRoles` — THE SECOND INSTANCE, and the
-- point of writing it now rather than at G2 (plan 0.65, 2026-08-12).
--
-- A core with one instance is not known to be generic; it is only known to
-- typecheck. Every assignment below is read off `AbstractToRiscV`, the same
-- way x86-64's was read off `AbstractToX86`:
--
--     mv a0 t0                   Output := Input1     → a0, t0
--     mv a0 s2 ; addi s2 s2 n    alloc-heap           → s2 is the frontier
--     mv s1 t0                   save-closure-reg     → s1
--     li s4 0 / addi s4 s4 1     count-zero/-inc      → s4
--     li s3 1 / beq s3 zero      scratch-one/branch   → s3
--     addi sp sp -n              alloc-stack          → sp
--
-- Seven roles, seven distinct registers — INJECTIVE. (It was eight until plan
-- 0.66 retired `Input2`/`a1`, the role x86-32 had no free register for.)
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.RiscV64.RegRoles where

open import Once.CCC.Target.RiscV64.Syntax using (Reg; sp; a0; t0; s1; s2; s3; s4)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-scratch; role-count)

riscv64-reg-of : Role → Reg
riscv64-reg-of role-sp      = sp
riscv64-reg-of role-clos    = s1
riscv64-reg-of role-heap    = s2
riscv64-reg-of role-out     = a0
riscv64-reg-of role-in1     = t0
riscv64-reg-of role-scratch = s3
riscv64-reg-of role-count   = s4

riscv64-roles : RegRoles Reg
riscv64-roles = record { reg-of = riscv64-reg-of }

open RegRoles riscv64-roles public
