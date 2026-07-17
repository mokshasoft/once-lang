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

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; _≢_)
open import Relation.Nullary using (¬_)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Arith.Backend.X86-64.Confine using (writes; confined)
open import Once.CCC.Target.X86-64.Semantics using (RegFile; readReg; writeReg; Word)
open import Once.Target.X86-64.PhysReg
  using (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;
         owner; ccc)

------------------------------------------------------------------------
-- Agreement on the 7 CCC-owned registers (rcx rbx rbp rsi rsp r12 r15).
------------------------------------------------------------------------

-- A RECORD (not a ×-synonym) so its indices are inferrable at `AgreeCCC-trans`
-- call sites (defined functions aren't injective for unification).
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

------------------------------------------------------------------------
-- Writing a non-CCC register preserves all CCC registers.
--   * non-`ccc` write (rdi rax r8 r9 r10 r11 rdx r13 r14): distinct record
--     fields ⇒ each CCC read is `refl`.
--   * `ccc` write (rcx rbx rbp rsi rsp r12 r15): `owner w ≡ ccc` contradicts
--     the hypothesis.
------------------------------------------------------------------------

write-nonccc-agrees : ∀ rf w v → owner w ≢ ccc → AgreeCCC rf (writeReg rf w v)
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

------------------------------------------------------------------------
-- The LIFT: `AgreeCCC` is transitive, so CCC-preservation composes.
-- A block is a list of per-instruction register-file steps; if every step
-- only writes non-`ccc` registers, the whole block preserves the 7 CCC
-- registers. Abstract over the step semantics (the lowering fills them in).
------------------------------------------------------------------------

AgreeCCC-trans : ∀ {a b c} → AgreeCCC a b → AgreeCCC b c → AgreeCCC a c
AgreeCCC-trans (mkAgree p1 p2 p3 p4 p5 p6 p7) (mkAgree q1 q2 q3 q4 q5 q6 q7) =
  mkAgree (trans p1 q1) (trans p2 q2) (trans p3 q3) (trans p4 q4) (trans p5 q5) (trans p6 q6) (trans p7 q7)

-- A register-file step "preserves CCC" if it agrees on all 7 CCC registers.
PreservesCCC-rf : (RegFile → RegFile) → Set
PreservesCCC-rf f = ∀ rf → AgreeCCC rf (f rf)

-- A single write to a non-`ccc` register (value may depend on the state).
preserves-write-nonccc : ∀ {w} (val : RegFile → Word) → owner w ≢ ccc →
                         PreservesCCC-rf (λ rf → writeReg rf w (val rf))
preserves-write-nonccc {w} val neq rf = write-nonccc-agrees rf w (val rf) neq

-- Run a block of register-file steps in order.
runFns : List (RegFile → RegFile) → RegFile → RegFile
runFns []       rf = rf
runFns (f ∷ fs) rf = runFns fs (f rf)

-- Block-level CCC-preservation: every step preserving CCC ⇒ the block does.
preserves-runFns : ∀ fs → All PreservesCCC-rf fs → PreservesCCC-rf (runFns fs)
preserves-runFns []       _          rf = agree-refl-ccc rf
preserves-runFns (f ∷ fs) (pf ∷ pfs) rf =
  AgreeCCC-trans (pf rf) (preserves-runFns fs pfs (f rf))

------------------------------------------------------------------------
-- Lowering (register-effect model): an instruction's concrete effect on the
-- register file is a sequence of writes to its footprint registers. For
-- CCC-preservation the WRITTEN VALUES are irrelevant (value correctness is
-- Phase A `block-correct`); only the footprint's CCC-disjointness matters.
------------------------------------------------------------------------

-- Write a list of (register, value) pairs in order.
write-regs : List (Reg × Word) → RegFile → RegFile
write-regs []             rf = rf
write-regs ((w , v) ∷ ps) rf = write-regs ps (writeReg rf w v)

-- If every written register is non-`ccc`, the whole write-sequence preserves
-- the CCC registers. This is the bridge `Confine.confined` plugs into: a step
-- writing exactly `writes i` (any values) preserves CCC because `confined i`
-- proves `writes i` is CCC-disjoint.
write-regs-preserves : ∀ ps → All (λ p → owner (proj₁ p) ≢ ccc) ps →
                       PreservesCCC-rf (write-regs ps)
write-regs-preserves []             _          rf = agree-refl-ccc rf
write-regs-preserves ((w , v) ∷ ps) (nc ∷ ncs) rf =
  AgreeCCC-trans (write-nonccc-agrees rf w v nc) (write-regs-preserves ps ncs (writeReg rf w v))

------------------------------------------------------------------------
-- CAPSTONE: `Confine.confined` ⇒ the arith instruction's register step
-- preserves CCC. `step-of i val` is instruction i writing its footprint
-- `writes i` with values from `val` (the concrete instruction semantics —
-- irrelevant to preservation). Whole blocks then compose via `preserves-runFns`.
------------------------------------------------------------------------

step-of : XInstr → (Reg → Word) → RegFile → RegFile
step-of i val = write-regs (map (λ r → (r , val r)) (writes i))

step-of-preserves : ∀ i val → PreservesCCC-rf (step-of i val)
step-of-preserves i val = write-regs-preserves _ (map⁺ (confined i))
