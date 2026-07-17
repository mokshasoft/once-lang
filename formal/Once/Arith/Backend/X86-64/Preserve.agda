-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Preserve  (Plan 0.54 Phase B / Option 2)
--
-- The concrete-machine foundation for arith CCC-preservation: writing a
-- NON-`ccc` register leaves every `ccc`-owned register unchanged, over the
-- REAL x86-64 register file (`Once.CCC.Target.X86-64.Semantics.RegFile`,
-- which reuses the shared `Once.Target.X86-64.PhysReg.Reg`).
--
-- This is the atomic step behind "the arith subroutine preserves CCC state":
-- combined with `Confine.confined` (every arith write is non-`ccc`), a whole
-- arith block preserves the 7 CCC registers. `AgreeCCC` enumerates them, so
-- the proof splits only on the WRITTEN register (16 clauses: 9 non-`ccc` →
-- refls, 7 `ccc` → absurd), not the 16×16 read×write matrix.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Preserve where

open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_)

open import Once.CCC.Target.X86-64.Semantics using (RegFile; readReg; writeReg)
open import Once.Target.X86-64.PhysReg
  using (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         owner; ccc)

------------------------------------------------------------------------
-- Agreement on the 7 CCC-owned registers (rcx rbx rbp rsi rsp r12 r15).
------------------------------------------------------------------------

AgreeCCC : RegFile → RegFile → Set
AgreeCCC rf rf' =
    (readReg rf rcx ≡ readReg rf' rcx)
  × (readReg rf rbx ≡ readReg rf' rbx)
  × (readReg rf rbp ≡ readReg rf' rbp)
  × (readReg rf rsi ≡ readReg rf' rsi)
  × (readReg rf rsp ≡ readReg rf' rsp)
  × (readReg rf r12 ≡ readReg rf' r12)
  × (readReg rf r15 ≡ readReg rf' r15)

agree-refl-ccc : ∀ rf → AgreeCCC rf rf
agree-refl-ccc rf = refl , refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- Writing a non-CCC register preserves all CCC registers.
--   * non-`ccc` write (rdi rax r8 r9 r10 r11 rdx r13 r14): distinct record
--     fields ⇒ each CCC read is `refl`.
--   * `ccc` write (rcx rbx rbp rsi rsp r12 r15): `owner w ≡ ccc` contradicts
--     the hypothesis.
------------------------------------------------------------------------

write-nonccc-agrees : ∀ rf w v → owner w ≢ ccc → AgreeCCC rf (writeReg rf w v)
write-nonccc-agrees rf rax v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf rdi v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf rdx v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r8  v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r9  v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r10 v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r11 v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r13 v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf r14 v _   = refl , refl , refl , refl , refl , refl , refl
write-nonccc-agrees rf rcx v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rbx v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rbp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rsi v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rsp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf r12 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf r15 v neq = ⊥-elim (neq refl)
