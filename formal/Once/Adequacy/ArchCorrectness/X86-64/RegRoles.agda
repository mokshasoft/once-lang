-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.RegRoles
--
-- x86-64's answer to `FlatCore.RegRoles` (Plan 0.65 G1c). Eight roles, eight
-- registers, injectively — the assignment `AbstractToX86.compile-abstract`
-- already makes, written down once where the correspondence can name it.
--
-- The long-lived roles sit in callee-saved registers (rbx/r14/r12/r15) and the
-- transient ones in the SysV argument/return registers (rax/rdi/rsi), which is
-- why a closure call can cross an arith block without spilling them.
--
-- Because this is a CONCRETE record, every projection reduces: `out-reg` IS
-- `rax` definitionally, so introducing the role names changes nothing the
-- typechecker does. That is what makes G1c step 1 a pure rename.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64.RegRoles where

open import Once.CCC.Target.X86-64.Syntax using (Reg; rax; rbx; rsi; rdi; rsp; r12; r14; r15)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-in2; role-scratch; role-count)

x86-64-reg-of : Role → Reg
x86-64-reg-of role-sp      = rsp
x86-64-reg-of role-clos    = r12
x86-64-reg-of role-heap    = r15
x86-64-reg-of role-out     = rax
x86-64-reg-of role-in1     = rdi
x86-64-reg-of role-in2     = rsi
x86-64-reg-of role-scratch = rbx
x86-64-reg-of role-count   = r14

x86-64-roles : RegRoles Reg
x86-64-roles = record { reg-of = x86-64-reg-of }

open RegRoles x86-64-roles public
