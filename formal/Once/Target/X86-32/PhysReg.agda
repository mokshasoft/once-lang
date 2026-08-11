-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.X86-32.PhysReg
--
-- The SINGLE ia32 physical-register declaration, shared by the CCC and
-- arith backends (Plan 0.55).
--
-- ia32 is the register-POOR case: CCC's codegen live-uses ALL 8 GPRs, so
-- there are ZERO CCC-free registers. The arith block therefore CANNOT be
-- disjoint — it BORROWS CCC's registers and preserves them by save/restore
-- (push/pop in the block prologue/epilogue). The `owner` partition records
-- this honestly: the arith block's working registers are `ccc`-owned
-- (`arith-borrows` in the arith Emit is `owner (arith-reg x) ≡ ccc`), which
-- is the marker that PreservesCCC here is a restore-correctness property,
-- NOT the definitional disjointness used on x86-64 / riscv64.
--
-- Partition (from the 0.55 audit):
--   * io   — ecx (Input1 / arith block input), eax (Output / arith result).
--   * ccc  — ebx edx esi edi ebp esp (all live in CCC; arith borrows edx edi
--            ebx esi and push/pops them).
------------------------------------------------------------------------

module Once.Target.X86-32.PhysReg where

open import Data.String using (String)

data Reg : Set where
  eax ebx ecx edx esi edi ebp esp : Reg

showReg : Reg → String
showReg eax = "%eax"
showReg ebx = "%ebx"
showReg ecx = "%ecx"
showReg edx = "%edx"
showReg esi = "%esi"
showReg edi = "%edi"
showReg ebp = "%ebp"
showReg esp = "%esp"

open import Once.Target.RegConvention public
  using (RegClass; io; ccc; arith; free; RegConvention)

owner : Reg → RegClass
owner ecx = io
owner eax = io
owner ebx = ccc
owner edx = ccc
owner esi = ccc
owner edi = ccc
owner ebp = ccc
owner esp = ccc

------------------------------------------------------------------------
-- Arith register budget (Plan 0.56): EMPTY on ia32 — no CCC-free
-- registers, so k = 0 ⇒ the save/restore fallback (0.55's arith-borrows).
------------------------------------------------------------------------

open import Data.List using (List; [])
import Data.List.Relation.Unary.All as All

arith-budget : List Reg
arith-budget = []

-- k = 0: the arith block borrows CCC registers + save/restores (0.55's
-- arith-borrows); the budget is empty, so `budget-owned` is trivially `[]`.
convention : RegConvention
convention = record
  { Reg = Reg ; showReg = showReg ; owner = owner ; arith-budget = arith-budget
  ; budget-owned = All.[] }
