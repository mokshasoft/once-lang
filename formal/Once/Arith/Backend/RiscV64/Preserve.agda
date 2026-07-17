-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Preserve  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 register CCC-preservation: the per-arch BASE only (enumerated
-- `AgreeCCC` over the 16 CCC registers incl. hardwired `zero`, + its 3 lemmas),
-- over the real riscv64 `RegFile`. The framework is the arch-generic
-- `Once.Arith.Backend.PreserveCore`, re-exported.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Preserve where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; _≢_)

open import Once.Arith.Backend.RiscV64.Confine using (writes; confined; NotCCC)
open import Once.CCC.Target.RiscV64.Semantics using (RegFile; readReg; writeReg; Word)
open import Once.Target.RiscV64.PhysReg using (Reg; t0; a0; a3; a4; a5; zero; ra; sp; fp; a1; a2; a6; a7; s1; s2; s3; s4; t1; t2; t3; t4; owner; ccc)

record AgreeCCC (rf rf' : RegFile) : Set where
  constructor mkAgree
  field
    a-zero : readReg rf zero ≡ readReg rf' zero
    a-ra : readReg rf ra ≡ readReg rf' ra
    a-sp : readReg rf sp ≡ readReg rf' sp
    a-fp : readReg rf fp ≡ readReg rf' fp
    a-a1 : readReg rf a1 ≡ readReg rf' a1
    a-a2 : readReg rf a2 ≡ readReg rf' a2
    a-a6 : readReg rf a6 ≡ readReg rf' a6
    a-a7 : readReg rf a7 ≡ readReg rf' a7
    a-s1 : readReg rf s1 ≡ readReg rf' s1
    a-s2 : readReg rf s2 ≡ readReg rf' s2
    a-s3 : readReg rf s3 ≡ readReg rf' s3
    a-s4 : readReg rf s4 ≡ readReg rf' s4
    a-t1 : readReg rf t1 ≡ readReg rf' t1
    a-t2 : readReg rf t2 ≡ readReg rf' t2
    a-t3 : readReg rf t3 ≡ readReg rf' t3
    a-t4 : readReg rf t4 ≡ readReg rf' t4
open AgreeCCC public

agree-refl-ccc : ∀ rf → AgreeCCC rf rf
agree-refl-ccc rf = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

write-nonccc-agrees : ∀ rf w v → NotCCC w → AgreeCCC rf (writeReg rf w v)
write-nonccc-agrees rf t0 v _   = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
write-nonccc-agrees rf a0 v _   = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
write-nonccc-agrees rf a3 v _   = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
write-nonccc-agrees rf a4 v _   = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
write-nonccc-agrees rf a5 v _   = mkAgree refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
write-nonccc-agrees rf zero v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf ra v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf sp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf fp v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf a1 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf a2 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf a6 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf a7 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf s1 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf s2 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf s3 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf s4 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf t1 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf t2 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf t3 v neq = ⊥-elim (neq refl)
write-nonccc-agrees rf t4 v neq = ⊥-elim (neq refl)

AgreeCCC-trans : ∀ {a b c} → AgreeCCC a b → AgreeCCC b c → AgreeCCC a c
AgreeCCC-trans (mkAgree p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15) (mkAgree q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15) =
  mkAgree (trans p0 q0) (trans p1 q1) (trans p2 q2) (trans p3 q3) (trans p4 q4) (trans p5 q5) (trans p6 q6) (trans p7 q7) (trans p8 q8) (trans p9 q9) (trans p10 q10) (trans p11 q11) (trans p12 q12) (trans p13 q13) (trans p14 q14) (trans p15 q15)

open import Once.Arith.Backend.PreserveCore
  writeReg NotCCC AgreeCCC agree-refl-ccc AgreeCCC-trans write-nonccc-agrees writes confined
  public
