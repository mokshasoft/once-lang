-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Preserve  (Plan 0.54 Phase B / Option 2)
--
-- x86-64 register CCC-preservation. This module holds ONLY the per-arch BASE —
-- the enumerated `AgreeCCC` over the 7 CCC registers (rcx rbx rbp rsi rsp r12
-- r15) and its three lemmas — over the real x86-64 `RegFile`. The whole
-- downstream framework (`PreservesCCC-rf`/`runFns`/`step-of`/…) is the
-- arch-generic `Once.Arith.Backend.PreserveCore`, re-exported here.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Preserve where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; _≢_)

open import Once.Arith.Backend.X86-64.Confine using (writes; confined; NotCCC)
open import Once.CCC.Target.X86-64.Semantics using (RegFile; readReg; writeReg; Word)
open import Once.Target.X86-64.PhysReg
  using (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         owner; ccc)

------------------------------------------------------------------------
-- BASE: agreement on the 7 CCC-owned registers (a RECORD so `AgreeCCC-trans`
-- can infer its indices; the 3 lemmas below feed `PreserveCore`).
------------------------------------------------------------------------

record AgreeCCC (rf rf' : RegFile) : Set where
  constructor mkAgree
  field
    a-rcx : readReg rf rcx ≡ readReg rf' rcx
    a-rbx : readReg rf rbx ≡ readReg rf' rbx
    a-rbp : readReg rf rbp ≡ readReg rf' rbp
    a-rsi : readReg rf rsi ≡ readReg rf' rsi
    a-rsp : readReg rf rsp ≡ readReg rf' rsp
    a-r12 : readReg rf r12 ≡ readReg rf' r12
    a-r15 : readReg rf r15 ≡ readReg rf' r15
open AgreeCCC public

agree-refl-ccc : ∀ rf → AgreeCCC rf rf
agree-refl-ccc rf = mkAgree refl refl refl refl refl refl refl

-- Writing a non-CCC register (rdi rax r8-r11 rdx r13 r14) preserves all CCC
-- registers (distinct record fields ⇒ refl); a CCC write contradicts NotCCC.
write-nonccc-agrees : ∀ rf w v → NotCCC w → AgreeCCC rf (writeReg rf w v)
write-nonccc-agrees rf rax v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf rdi v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf rdx v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r8  v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r9  v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r10 v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r11 v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r13 v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf r14 v _   = mkAgree refl refl refl refl refl refl refl
write-nonccc-agrees rf rcx v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rbx v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rbp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rsi v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf rsp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf r12 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf r15 v neq = ⊥-elim (neq refl)

AgreeCCC-trans : ∀ {a b c} → AgreeCCC a b → AgreeCCC b c → AgreeCCC a c
AgreeCCC-trans (mkAgree p1 p2 p3 p4 p5 p6 p7) (mkAgree q1 q2 q3 q4 q5 q6 q7) =
  mkAgree (trans p1 q1) (trans p2 q2) (trans p3 q3) (trans p4 q4) (trans p5 q5) (trans p6 q6) (trans p7 q7)

------------------------------------------------------------------------
-- FRAMEWORK: the arch-generic lift / lowering / step-of, instantiated here.
------------------------------------------------------------------------

open import Once.Arith.Backend.PreserveCore
  writeReg NotCCC AgreeCCC agree-refl-ccc AgreeCCC-trans write-nonccc-agrees writes confined
  public
