-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
--
-- THE ROLE MAP (Plan 0.65 G1c, 2026-08-11).
--
-- The abstract machine has a fixed set of registers — Output, Input1,
-- Scratch, Count — plus three the flat machine owns: the stack pointer, the
-- closure pointer and the heap frontier. `FlatCorrespondence` named x86-64's
-- physical registers for these **799 times**, and every one of those mentions
-- is a ROLE, not an x86 fact. This record is that observation, made a type.
--
-- WHY A RECORD OF NAMED ROLES rather than `Reg` + `sp-reg`. A `sp-reg`-only
-- parameterisation was the original guess; measuring showed it would leave 587
-- concrete register mentions behind, i.e. most of the module. The roles are
-- what the correspondence's fields are ABOUT — `rax-eq` is the claim that the
-- Output register agrees — so naming them is what lets the statements survive
-- a change of arch.
--
-- INDEXED BY A `Role` ENUM, not eight independent fields — and that is step 2
-- talking. Once the post-state is abstract, "a write to Output leaves Input1
-- alone" stops being free (it used to be `writeReg`/`readReg` reduction on two
-- distinct constructors) and has to be stated. Stated over eight fields it is
-- 28 inequalities; stated over a `Role` enum it is `ρ' ≢ ρ`, ONE premise, and
-- the arch discharges it by an eight-way case split where the constructors
-- make every case `refl` or absurd. The eight names below are DERIVED, so the
-- 120 sites G1c step 1 renamed did not have to move again.
--
-- THE CAVEAT G1c MEASURED IS NOW CLOSED (plan 0.66, 2026-08-17). x86-32 could
-- not fill this record injectively: eight GPRs, nine roles counting the frame
-- pointer, `Input2` and `Scratch` both `edx`. There was no LOCAL fix — `ebp` is
-- the live frame anchor, so reassigning it is a SIGSEGV, not a fix. The fix was
-- to delete the role: `Input2` had no producer on any arch, so it is RETIRED
-- (see `SMCore.AbstractReg`), and x86-32's seven realised roles fit its seven
-- available registers exactly.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.FlatCore.RegRoles where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

data Role : Set where
  -- the flat machine's own three
  role-sp      : Role   -- stack pointer: IS the current frame's base (plan 0.61)
  role-clos    : Role   -- closure pointer, mirroring the flat `fclosure` (D097)
  role-heap    : Role   -- heap frontier, the bump allocator's top
  -- the abstract machine's registers
  role-out     : Role
  role-in1     : Role
  role-scratch : Role
  role-count   : Role   -- the cata tally (plan 0.54 D item 4)

record RegRoles (Reg : Set) : Set where
  field
    reg-of : Role → Reg

  sp-reg      = reg-of role-sp
  clos-reg    = reg-of role-clos
  heap-reg    = reg-of role-heap
  out-reg     = reg-of role-out
  in1-reg     = reg-of role-in1
  scratch-reg = reg-of role-scratch
  count-reg   = reg-of role-count
