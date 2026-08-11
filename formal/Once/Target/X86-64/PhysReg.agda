-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.X86-64.PhysReg
--
-- The SINGLE x86-64 physical-register declaration, shared by the CCC
-- backend and the arith backend (Plan 0.55). Both machines "acquire"
-- their registers from this one type, and the `owner` partition makes
-- CCC/arith register disjointness DEFINITIONAL (a `refl`) rather than an
-- informal comment papered over by `x86-flat-from-obs`.
--
-- Partition (from the 0.55 concrete-register audit of CCC's codegen):
--   * io   — rdi (Input1 / arith block input), rax (Output / arith result):
--            the calling-convention registers the arith block reads/writes
--            on purpose.
--   * ccc  — registers CCC keeps live across a SigOp call: rcx rbx rbp rsi
--            rsp, plus r12 (closure ptr) and r15 (heap-top ptr).
--   * arith— the arith block's private working registers (r8 r9 r10 r11):
--            chosen to be BOTH caller-saved (a `call` already clobbers them,
--            so the frameless block owes no callee-save) AND in the set CCC
--            never emits (so disjointness with `ccc` is definitional).
--   * free — rdx r13 r14 (emitted by neither today).
------------------------------------------------------------------------

module Once.Target.X86-64.PhysReg where

open import Data.String using (String)

------------------------------------------------------------------------
-- The 16 general-purpose registers
------------------------------------------------------------------------

data Reg : Set where
  rax : Reg    -- Return value / accumulator
  rbx : Reg    -- Callee-saved (base)
  rcx : Reg    -- Fourth argument (Windows) / counter
  rdx : Reg    -- Third argument
  rsi : Reg    -- Second argument (source index)
  rdi : Reg    -- First argument (destination index)
  rbp : Reg    -- Frame pointer (callee-saved)
  rsp : Reg    -- Stack pointer
  r8  : Reg    -- Fifth argument
  r9  : Reg    -- Sixth argument
  r10 : Reg    -- Temporary
  r11 : Reg    -- Temporary
  r12 : Reg    -- Callee-saved (environment pointer for closures)
  r13 : Reg    -- Callee-saved
  r14 : Reg    -- Callee-saved
  r15 : Reg    -- Callee-saved

showReg : Reg → String
showReg rax = "%rax"
showReg rbx = "%rbx"
showReg rcx = "%rcx"
showReg rdx = "%rdx"
showReg rsi = "%rsi"
showReg rdi = "%rdi"
showReg rbp = "%rbp"
showReg rsp = "%rsp"
showReg r8  = "%r8"
showReg r9  = "%r9"
showReg r10 = "%r10"
showReg r11 = "%r11"
showReg r12 = "%r12"
showReg r13 = "%r13"
showReg r14 = "%r14"
showReg r15 = "%r15"

------------------------------------------------------------------------
-- Ownership partition — makes CCC/arith disjointness definitional
------------------------------------------------------------------------

open import Once.Target.RegConvention public
  using (RegClass; io; ccc; arith; free; RegConvention)

owner : Reg → RegClass
owner rdi = io
owner rax = io
owner rcx = ccc
owner rbx = ccc
owner rbp = ccc
owner rsi = ccc
owner rsp = ccc
owner r12 = ccc
owner r15 = ccc
owner r8  = arith
owner r9  = arith
owner r10 = arith
owner r11 = arith
owner rdx = free
owner r13 = free
owner r14 = free

------------------------------------------------------------------------
-- Arith register budget (Plan 0.56): the arith-owned registers in
-- priority order. `k = length arith-budget` scales the arith compiler.
------------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (refl)

arith-budget : List Reg
arith-budget = r8 ∷ r9 ∷ r10 ∷ r11 ∷ []

-- This arch's register convention (Plan 0.55/0.56). `budget-owned` proves
-- every budget register is arith-owned, so an invalid budget won't typecheck.
convention : RegConvention
convention = record
  { Reg = Reg ; showReg = showReg ; owner = owner ; arith-budget = arith-budget
  ; budget-owned = refl All.∷ refl All.∷ refl All.∷ refl All.∷ All.[] }
