{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.Foundation
--
-- Foundation lemmas for AArch64 correctness proofs.
-- Contains register/memory lemmas, execution helpers, and single-instruction
-- step lemmas that form the basis for the main correctness proofs.
--
-- Split from Correct.agda for incremental compilation.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.Foundation where

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; eval; Closure; encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity; module ⟦Fix⟧) public
open ⟦Fix⟧

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open Once.Backend.AArch64.Semantics.State
open Once.Backend.AArch64.Semantics.PSTATE
open import Once.Backend.AArch64.CodeGen

-- Import common fetch lemmas (polymorphic, work with any instruction type)
open import Once.Backend.Common.Fetch
  using (fetch-0; fetch-suc; fetch-empty; fetch-append-left; fetch-append-right; fetch-past-end)
  public

-- Import common memory helper lemmas (with AArch64 naming convention)
open import Once.Backend.Common.Memory
  using (readMem-writeMem-same)
  renaming (≡ᵇ-refl to n≡ᵇn; n≢n+8-bool to n≢n+8; n+8≢n-bool to n+8≢n; readMem-writeMem-diff-bool to readMem-writeMem-diff)
  public

open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect) renaming ([_] to ⟦_⟧ᵢ)
-- Note: We use IR._∘_ for composition, not Function._∘_

------------------------------------------------------------------------
-- P2: Encoding Axioms (imported from Once.Postulates)
------------------------------------------------------------------------

-- These axioms relate semantic values to their machine representation.
-- The memory layout is identical to x86-64:
--   Unit:    0
--   Pair:    [fst (8 bytes), snd (8 bytes)]
--   Sum:     [tag (8 bytes), value (8 bytes)] where tag=0 for inl, tag=1 for inr
--   Closure: [env (8 bytes), code_ptr (8 bytes)]

-- Note: encode, encode-unit, encode-fix-wrap, encode-fix-unwrap, encode-arr-identity
-- are now imported from Once.Semantics (they are proven, not postulated!)

-- Import encoding axioms from centralized Once.Postulates
-- The Memory type (Word → Maybe Word) is definitionally equal
open import Once.Postulates
  using ( encode-pair-fst; encode-pair-snd
        ; encode-inl-tag; encode-inl-val
        ; encode-inr-tag; encode-inr-val
        ; encode-pair-construct
        ; encode-inl-construct; encode-inr-construct
        ; encode-closure-construct
        )
  public

-- | Memory containing encoded values (for projection/case analysis)
-- Used in ValidInputState to ensure memory has proper encoding
-- This is AArch64-specific (abstract memory for initial state)
postulate
  encodedMemory : Memory

------------------------------------------------------------------------
-- Register/Memory Lemmas (Step 1)
------------------------------------------------------------------------

-- These are foundational lemmas for register file and memory operations.
-- They are proven directly from the definitions in Semantics.agda.

open import Relation.Nullary using (¬_; yes; no)
open import Data.Bool using (T)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)

-- n≡ᵇn is now imported from Once.Backend.Common.Memory (renamed from ≡ᵇ-refl)

-- | Reading a register after writing returns the written value
-- Proven by case analysis on register
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readReg (writeReg rf r v) r ≡ v
readReg-writeReg-same rf x0  v = refl
readReg-writeReg-same rf x1  v = refl
readReg-writeReg-same rf x2  v = refl
readReg-writeReg-same rf x3  v = refl
readReg-writeReg-same rf x4  v = refl
readReg-writeReg-same rf x5  v = refl
readReg-writeReg-same rf x6  v = refl
readReg-writeReg-same rf x7  v = refl
readReg-writeReg-same rf x8  v = refl
readReg-writeReg-same rf x9  v = refl
readReg-writeReg-same rf x10 v = refl
readReg-writeReg-same rf x11 v = refl
readReg-writeReg-same rf x12 v = refl
readReg-writeReg-same rf x13 v = refl
readReg-writeReg-same rf x14 v = refl
readReg-writeReg-same rf x15 v = refl
readReg-writeReg-same rf x16 v = refl
readReg-writeReg-same rf x17 v = refl
readReg-writeReg-same rf x18 v = refl
readReg-writeReg-same rf x19 v = refl
readReg-writeReg-same rf x20 v = refl
readReg-writeReg-same rf x21 v = refl
readReg-writeReg-same rf x22 v = refl
readReg-writeReg-same rf x23 v = refl
readReg-writeReg-same rf x24 v = refl
readReg-writeReg-same rf x25 v = refl
readReg-writeReg-same rf x26 v = refl
readReg-writeReg-same rf x27 v = refl
readReg-writeReg-same rf x28 v = refl
readReg-writeReg-same rf x29 v = refl
readReg-writeReg-same rf x30 v = refl

-- | Cross-register preservation: writing x0 doesn't affect x9
readReg-writeReg-x0-x9 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x9 ≡ readReg rf x9
readReg-writeReg-x0-x9 rf v = refl

-- | Cross-register preservation: writing x0 doesn't affect x19 (env pointer)
readReg-writeReg-x0-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x19 ≡ readReg rf x19
readReg-writeReg-x0-x19 rf v = refl

-- | Cross-register preservation: writing x0 doesn't affect x20 (callee-saved)
readReg-writeReg-x0-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x20 ≡ readReg rf x20
readReg-writeReg-x0-x20 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x0
readReg-writeReg-x9-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x0 ≡ readReg rf x0
readReg-writeReg-x9-x0 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x20
readReg-writeReg-x9-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x20 ≡ readReg rf x20
readReg-writeReg-x9-x20 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x0
readReg-writeReg-x19-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x0 ≡ readReg rf x0
readReg-writeReg-x19-x0 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x9
readReg-writeReg-x19-x9 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x9 ≡ readReg rf x9
readReg-writeReg-x19-x9 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x10
readReg-writeReg-x19-x10 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x10 ≡ readReg rf x10
readReg-writeReg-x19-x10 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x30
readReg-writeReg-x19-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x30 ≡ readReg rf x30
readReg-writeReg-x19-x30 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x10
readReg-writeReg-x9-x10 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x10 ≡ readReg rf x10
readReg-writeReg-x9-x10 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x19
readReg-writeReg-x9-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x19 ≡ readReg rf x19
readReg-writeReg-x9-x19 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x30
readReg-writeReg-x9-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x30 ≡ readReg rf x30
readReg-writeReg-x9-x30 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x29
readReg-writeReg-x9-x29 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x29 ≡ readReg rf x29
readReg-writeReg-x9-x29 rf v = refl

-- | Cross-register preservation: writing x20 doesn't affect x0
readReg-writeReg-x20-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x0 ≡ readReg rf x0
readReg-writeReg-x20-x0 rf v = refl

-- | Cross-register preservation: writing x20 doesn't affect x19
readReg-writeReg-x20-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x19 ≡ readReg rf x19
readReg-writeReg-x20-x19 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x20
readReg-writeReg-x19-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x20 ≡ readReg rf x20
readReg-writeReg-x19-x20 rf v = refl

-- | Cross-register preservation: writing x21 doesn't affect x0
readReg-writeReg-x21-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x21 v) x0 ≡ readReg rf x0
readReg-writeReg-x21-x0 rf v = refl

-- | Cross-register preservation: writing x21 doesn't affect x20
readReg-writeReg-x21-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x21 v) x20 ≡ readReg rf x20
readReg-writeReg-x21-x20 rf v = refl

-- | Cross-register preservation: writing x20 doesn't affect x21
readReg-writeReg-x20-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x21 ≡ readReg rf x21
readReg-writeReg-x20-x21 rf v = refl

-- | Cross-register preservation: writing x20 doesn't affect x29
readReg-writeReg-x20-x29 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x29 ≡ readReg rf x29
readReg-writeReg-x20-x29 rf v = refl

-- | Cross-register preservation: writing x20 doesn't affect x30
readReg-writeReg-x20-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x30 ≡ readReg rf x30
readReg-writeReg-x20-x30 rf v = refl

-- | Cross-register preservation: writing x21 doesn't affect x29
readReg-writeReg-x21-x29 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x21 v) x29 ≡ readReg rf x29
readReg-writeReg-x21-x29 rf v = refl

-- | Cross-register preservation: writing x21 doesn't affect x30
readReg-writeReg-x21-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x21 v) x30 ≡ readReg rf x30
readReg-writeReg-x21-x30 rf v = refl

-- | Cross-register preservation: writing x0 doesn't affect x21
readReg-writeReg-x0-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x21 ≡ readReg rf x21
readReg-writeReg-x0-x21 rf v = refl

-- | Cross-register preservation: writing x0 doesn't affect x29 (frame pointer)
readReg-writeReg-x0-x29 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x29 ≡ readReg rf x29
readReg-writeReg-x0-x29 rf v = refl

-- | Cross-register preservation: writing x0 doesn't affect x30 (link register)
readReg-writeReg-x0-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x30 ≡ readReg rf x30
readReg-writeReg-x0-x30 rf v = refl

-- | Cross-register preservation: writing x9 doesn't affect x21
readReg-writeReg-x9-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x21 ≡ readReg rf x21
readReg-writeReg-x9-x21 rf v = refl

-- | Cross-register preservation: writing x10 doesn't affect x21
readReg-writeReg-x10-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x21 ≡ readReg rf x21
readReg-writeReg-x10-x21 rf v = refl

-- | Cross-register preservation: writing x19 doesn't affect x21
readReg-writeReg-x19-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x21 ≡ readReg rf x21
readReg-writeReg-x19-x21 rf v = refl

-- | Cross-register preservation for x30 (link register, used by blr)
-- Writing x30 doesn't affect x0 (input/output register)
readReg-writeReg-x30-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x0 ≡ readReg rf x0
readReg-writeReg-x30-x0 rf v = refl

-- Writing x30 doesn't affect x9 (temp register holding code-ptr)
readReg-writeReg-x30-x9 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x9 ≡ readReg rf x9
readReg-writeReg-x30-x9 rf v = refl

-- Writing x30 doesn't affect x10 (temp register)
readReg-writeReg-x30-x10 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x10 ≡ readReg rf x10
readReg-writeReg-x30-x10 rf v = refl

-- Writing x30 doesn't affect x19 (env pointer)
readReg-writeReg-x30-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x19 ≡ readReg rf x19
readReg-writeReg-x30-x19 rf v = refl

-- Writing x30 doesn't affect x20 (callee-saved)
readReg-writeReg-x30-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x20 ≡ readReg rf x20
readReg-writeReg-x30-x20 rf v = refl

-- Writing x30 doesn't affect x21 (callee-saved)
readReg-writeReg-x30-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x21 ≡ readReg rf x21
readReg-writeReg-x30-x21 rf v = refl

-- | Cross-register preservation for x29 (frame pointer)
-- Writing x0 doesn't affect x29
readReg-writeReg-x29-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x0 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x0 rf v = refl

-- Writing x9 doesn't affect x29
readReg-writeReg-x29-x9 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x9 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x9 rf v = refl

-- Writing x10 doesn't affect x29
readReg-writeReg-x29-x10 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x10 rf v = refl

-- Writing x19 doesn't affect x29
readReg-writeReg-x29-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x19 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x19 rf v = refl

-- Writing x20 doesn't affect x29
readReg-writeReg-x29-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x20 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x20 rf v = refl

-- Writing x21 doesn't affect x29
readReg-writeReg-x29-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x21 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x21 rf v = refl

-- Writing x30 doesn't affect x29
readReg-writeReg-x29-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x30 v) x29 ≡ readReg rf x29
readReg-writeReg-x29-x30 rf v = refl

-- | Cross-register preservation for x10 (used by apply to hold arg)
-- Writing x10 doesn't affect x0
readReg-writeReg-x10-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x0 ≡ readReg rf x0
readReg-writeReg-x10-x0 rf v = refl

-- Writing x10 doesn't affect x9
readReg-writeReg-x10-x9 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x9 ≡ readReg rf x9
readReg-writeReg-x10-x9 rf v = refl

-- Writing x10 doesn't affect x19
readReg-writeReg-x10-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x19 ≡ readReg rf x19
readReg-writeReg-x10-x19 rf v = refl

-- Writing x10 doesn't affect x20
readReg-writeReg-x10-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x20 ≡ readReg rf x20
readReg-writeReg-x10-x20 rf v = refl

-- Writing x10 doesn't affect x30
readReg-writeReg-x10-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf x10 v) x30 ≡ readReg rf x30
readReg-writeReg-x10-x30 rf v = refl

-- | SP lemmas: reading SP after writing returns the written value
readSP-writeSP-same : ∀ (rf : RegFile) (v : Word) →
  readSP (writeSP rf v) ≡ v
readSP-writeSP-same rf v = refl

-- | Writing SP doesn't affect general registers
readReg-writeSP : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readReg (writeSP rf v) r ≡ readReg rf r
readReg-writeSP rf x0  v = refl
readReg-writeSP rf x1  v = refl
readReg-writeSP rf x2  v = refl
readReg-writeSP rf x3  v = refl
readReg-writeSP rf x4  v = refl
readReg-writeSP rf x5  v = refl
readReg-writeSP rf x6  v = refl
readReg-writeSP rf x7  v = refl
readReg-writeSP rf x8  v = refl
readReg-writeSP rf x9  v = refl
readReg-writeSP rf x10 v = refl
readReg-writeSP rf x11 v = refl
readReg-writeSP rf x12 v = refl
readReg-writeSP rf x13 v = refl
readReg-writeSP rf x14 v = refl
readReg-writeSP rf x15 v = refl
readReg-writeSP rf x16 v = refl
readReg-writeSP rf x17 v = refl
readReg-writeSP rf x18 v = refl
readReg-writeSP rf x19 v = refl
readReg-writeSP rf x20 v = refl
readReg-writeSP rf x21 v = refl
readReg-writeSP rf x22 v = refl
readReg-writeSP rf x23 v = refl
readReg-writeSP rf x24 v = refl
readReg-writeSP rf x25 v = refl
readReg-writeSP rf x26 v = refl
readReg-writeSP rf x27 v = refl
readReg-writeSP rf x28 v = refl
readReg-writeSP rf x29 v = refl
readReg-writeSP rf x30 v = refl

-- | Specialized versions for common registers
readReg-writeSP-x0 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x0 ≡ readReg rf x0
readReg-writeSP-x0 rf v = readReg-writeSP rf x0 v

readReg-writeSP-x19 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x19 ≡ readReg rf x19
readReg-writeSP-x19 rf v = readReg-writeSP rf x19 v

readReg-writeSP-x20 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x20 ≡ readReg rf x20
readReg-writeSP-x20 rf v = readReg-writeSP rf x20 v

readReg-writeSP-x21 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x21 ≡ readReg rf x21
readReg-writeSP-x21 rf v = readReg-writeSP rf x21 v

readReg-writeSP-x29 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x29 ≡ readReg rf x29
readReg-writeSP-x29 rf v = readReg-writeSP rf x29 v

readReg-writeSP-x30 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeSP rf v) x30 ≡ readReg rf x30
readReg-writeSP-x30 rf v = readReg-writeSP rf x30 v

-- | Writing register doesn't affect SP
readSP-writeReg : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readSP (writeReg rf r v) ≡ readSP rf
readSP-writeReg rf x0  v = refl
readSP-writeReg rf x1  v = refl
readSP-writeReg rf x2  v = refl
readSP-writeReg rf x3  v = refl
readSP-writeReg rf x4  v = refl
readSP-writeReg rf x5  v = refl
readSP-writeReg rf x6  v = refl
readSP-writeReg rf x7  v = refl
readSP-writeReg rf x8  v = refl
readSP-writeReg rf x9  v = refl
readSP-writeReg rf x10 v = refl
readSP-writeReg rf x11 v = refl
readSP-writeReg rf x12 v = refl
readSP-writeReg rf x13 v = refl
readSP-writeReg rf x14 v = refl
readSP-writeReg rf x15 v = refl
readSP-writeReg rf x16 v = refl
readSP-writeReg rf x17 v = refl
readSP-writeReg rf x18 v = refl
readSP-writeReg rf x19 v = refl
readSP-writeReg rf x20 v = refl
readSP-writeReg rf x21 v = refl
readSP-writeReg rf x22 v = refl
readSP-writeReg rf x23 v = refl
readSP-writeReg rf x24 v = refl
readSP-writeReg rf x25 v = refl
readSP-writeReg rf x26 v = refl
readSP-writeReg rf x27 v = refl
readSP-writeReg rf x28 v = refl
readSP-writeReg rf x29 v = refl
readSP-writeReg rf x30 v = refl

-- | Reading SP after writing SP returns the written value
readSP-writeSP : ∀ (rf : RegFile) (v : Word) →
  readSP (writeSP rf v) ≡ v
readSP-writeSP rf v = refl

-- Memory lemmas now imported from Once.Backend.Common.Memory:
--   readMem-writeMem-same, readMem-writeMem-diff (renamed from readMem-writeMem-diff-bool)
--   n≢n+8, n+8≢n (renamed from n≢n+8-bool, n+8≢n-bool)

-- | Corollary: reading at addr+8 after writing at addr is unchanged
readMem-writeMem-diff-8 : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m addr v) (addr +ℕ 8) ≡ readMem m (addr +ℕ 8)
readMem-writeMem-diff-8 m addr v = readMem-writeMem-diff m addr (addr +ℕ 8) v (n+8≢n addr)

-- | Corollary: reading at addr after writing at addr+8 is unchanged
readMem-writeMem-diff-8-rev : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m (addr +ℕ 8) v) addr ≡ readMem m addr
readMem-writeMem-diff-8-rev m addr v = readMem-writeMem-diff m (addr +ℕ 8) addr v (n≢n+8 addr)

------------------------------------------------------------------------
-- Step 2: Fetch/Execution Helpers
------------------------------------------------------------------------

-- These lemmas relate to the fetch and exec functions defined in Semantics.agda.
-- Fetch lemmas (fetch-0, fetch-suc, fetch-empty, fetch-append-left, fetch-append-right)
-- are now imported from Once.Backend.Common.Fetch.

open import Data.Nat using (_<_; _≤_; z<s; s≤s; z≤n; s<s)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc; m+n∸m≡n; +-assoc)
open import Data.List.Properties using (length-++)

-- | If already halted, exec returns the state unchanged
exec-halted : ∀ (n : ℕ) (prog : Program) (s : State) →
  halted s ≡ true → exec n prog s ≡ just s
exec-halted zero prog s h = refl
exec-halted (suc n) prog s h with halted s | h
... | true | refl with halted s
...   | true = refl

-- | Executing one step when we know the instruction and its effect
exec-one-step : ∀ (prog : Program) (s s' : State) (instr : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just instr →
  execInstr prog s instr ≡ just s' →
  halted s' ≡ true →
  exec 1 prog s ≡ just s'
exec-one-step prog s s' instr h-false fetch-eq exec-eq halt-true
  with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-eq
...   | just .instr | refl with execInstr prog s instr | exec-eq
...     | just .s' | refl with halted s' | halt-true
...       | true | refl = refl

-- | step on a halted state returns the same state
step-halted : ∀ (prog : Program) (s : State) →
  halted s ≡ true →
  step prog s ≡ just s
step-halted prog s h-true with halted s | h-true
... | true | refl = refl

-- | exec 0 always returns initial state
exec-0 : ∀ (prog : Program) (s : State) → exec 0 prog s ≡ just s
exec-0 prog s = refl

-- | exec (suc n) on a halted state returns the same state
exec-suc-halted : ∀ (n : ℕ) (prog : Program) (s : State) →
  halted s ≡ true →
  exec (suc n) prog s ≡ just s
exec-suc-halted n prog s h-true with step prog s | step-halted prog s h-true
... | just .s | refl with halted s | h-true
...   | true | refl = refl

-- | Executing N+1 steps when the N-step execution halts
-- If exec n gives a halted state, exec (suc n) gives the same state.
-- Proof by induction on n.
exec-N-if-halts : ∀ (n : ℕ) (prog : Program) (s s' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec (suc n) prog s ≡ just s'

-- Base case: n = 0
-- exec 0 prog s = just s, so s = s' and halted s' = true
-- By exec-suc-halted: exec 1 prog s = just s = just s'
exec-N-if-halts zero prog s .s refl h-true = exec-suc-halted zero prog s h-true

-- Inductive case: n = suc n'
exec-N-if-halts (suc n') prog s s' exec-eq h-true =
  exec-N-if-halts-suc n' prog s s' exec-eq h-true
  where
    exec-N-if-halts-suc : ∀ (n' : ℕ) (prog : Program) (s s' : State) →
      exec (suc n') prog s ≡ just s' →
      halted s' ≡ true →
      exec (suc (suc n')) prog s ≡ just s'
    exec-N-if-halts-suc n' prog s s' exec-eq h-true
      with step prog s
    -- step fails: impossible since exec (suc n') succeeded
    exec-N-if-halts-suc n' prog s s' () h-true | nothing
    -- step succeeds with s₁
    exec-N-if-halts-suc n' prog s s' exec-eq h-true | just s₁
      with halted s₁ in halt-eq
    -- s₁ halted: exec (suc n') returns just s₁, so s₁ = s'
    -- exec (suc (suc n')) also returns just s₁ = just s'
    exec-N-if-halts-suc n' prog s .s₁ refl h-true | just s₁ | true = refl
    -- s₁ not halted: exec (suc n') = exec n' prog s₁ = just s'
    -- By IH: exec (suc n') prog s₁ = just s'
    -- exec (suc (suc n')) prog s = step → s₁ (not halted) → exec (suc n') prog s₁
    exec-N-if-halts-suc n' prog s s' exec-eq h-true | just s₁ | false
      = exec-N-if-halts n' prog s₁ s' exec-eq h-true

-- | Monotonicity: if exec with n steps halts, exec with more fuel returns same result.
-- Proof: Use a helper that adds k more steps, then derive exec-mono by setting k = m ∸ n.
exec-mono : ∀ (n m : ℕ) (prog : Program) (s s' : State) →
  n ≤ m →
  exec n prog s ≡ just s' →
  halted s' ≡ true →
  exec m prog s ≡ just s'
exec-mono n m prog s s' n≤m exec-eq h-true =
  subst (λ x → exec x prog s ≡ just s') (m∸n+n≡m n≤m) (exec-mono-aux (m ∸ n) n prog s s' exec-eq h-true)
  where
    -- Import additional lemmas needed for the proof
    open import Data.Nat.Properties using (m∸n+n≡m; +-suc)

    -- Helper: adding k more steps to a halted execution still returns the halted state
    exec-mono-aux : ∀ (k n : ℕ) (prog : Program) (s s' : State) →
      exec n prog s ≡ just s' →
      halted s' ≡ true →
      exec (k +ℕ n) prog s ≡ just s'
    -- Base: adding 0 steps is identity
    exec-mono-aux zero n prog s s' exec-eq h-true = exec-eq
    -- Inductive: adding (suc k) steps
    -- IH: exec-mono-aux k (suc n) ... : exec (k + suc n) prog s ≡ just s'
    -- Goal: exec (suc k + n) prog s ≡ just s'
    -- suc k + n = suc (k + n)  definitionally (by def of +)
    -- k + suc n = suc (k + n)  (by +-suc k n)
    -- So subst with +-suc k n: from (k + suc n) to suc (k + n) = suc k + n
    exec-mono-aux (suc k) n prog s s' exec-eq h-true =
      subst (λ x → exec x prog s ≡ just s') (+-suc k n)
        (exec-mono-aux k (suc n) prog s s' (exec-N-if-halts n prog s s' exec-eq h-true) h-true)

------------------------------------------------------------------------
-- Execution Chaining Infrastructure (Well-Founded Recursion Support)
------------------------------------------------------------------------

-- These lemmas enable compositional proofs for the mutual recursion cluster
-- (compose, case, pair). The key idea is to chain execution results.

-- | Chaining execution: if exec n reaches s', then exec m from s' reaches s'',
-- then exec (n + m) from s reaches s''.
-- Proven by induction on n.
exec-chain : ∀ (n m : ℕ) (prog : Program) (s s' s'' : State) →
  exec n prog s ≡ just s' →
  halted s' ≡ false →
  exec m prog s' ≡ just s'' →
  exec (n +ℕ m) prog s ≡ just s''

-- Base case: n = 0
-- exec 0 prog s = just s by definition
-- exec-0-eq : just s ≡ just s', so s ≡ s'
-- exec (0 + m) prog s = exec m prog s = exec m prog s' = just s''
exec-chain zero m prog s .s s'' refl h-false exec-m-eq = exec-m-eq

-- Inductive case: n = suc n'
-- Use a helper to handle step and halted pattern matching
exec-chain (suc n') m prog s s' s'' exec-n-eq h-false exec-m-eq =
  exec-chain-suc n' m prog s s' s'' exec-n-eq h-false exec-m-eq
  where
    -- Helper for the successor case
    exec-chain-suc : ∀ (n' m : ℕ) (prog : Program) (s s' s'' : State) →
      exec (suc n') prog s ≡ just s' →
      halted s' ≡ false →
      exec m prog s' ≡ just s'' →
      exec (suc n' +ℕ m) prog s ≡ just s''
    exec-chain-suc n' m prog s s' s'' exec-n-eq h-false exec-m-eq
      with step prog s
    -- step fails: impossible since exec succeeded
    exec-chain-suc n' m prog s s' s'' () h-false exec-m-eq | nothing
    -- step succeeds with s₁
    exec-chain-suc n' m prog s s' s'' exec-n-eq h-false exec-m-eq | just s₁
      with halted s₁ in halt-eq
    -- s₁ halted: then s' = s₁ and halted s' = true, contradicts h-false
    exec-chain-suc n' m prog s .s₁ s'' refl h-false exec-m-eq | just s₁ | true
      rewrite halt-eq with () ← h-false
    -- s₁ not halted: recurse
    exec-chain-suc n' m prog s s' s'' exec-n-eq h-false exec-m-eq | just s₁ | false
      = exec-chain n' m prog s₁ s' s'' exec-n-eq h-false exec-m-eq

-- | Execution within a concatenated program (left part)
--
-- KEY INSIGHT: When pc reaches length prog1:
--   - On prog1: fetch fails → implicit halt
--   - On prog1 ++ prog2: fetch succeeds → continues into prog2
--
-- So executions only match while pc STRICTLY < length prog1.
--
-- This lemma proves: if execution stays within prog1 (not halted, pc in bounds),
-- then execution on prog1 matches execution on prog1 ++ prog2.
--
-- Proof by induction on n:
--   Base (n=0): trivial (exec 0 = just s)
--   Step (n=suc n'):
--     - pc s < length prog1 (from precondition)
--     - fetch-append-left: fetch (prog1++prog2) (pc s) = fetch prog1 (pc s)
--     - So step gives same result s₁
--     - If halted s₁, done (exec returns just s₁)
--     - If not halted s₁, apply IH with s₁ and n'

-- Helper: If pc < length prog, fetch prog pc succeeds
fetch-succeeds : ∀ (prog : Program) (n : ℕ) → n < length prog →
  ∃[ instr ] (fetch prog n ≡ just instr)
fetch-succeeds [] n ()
fetch-succeeds (x ∷ xs) zero pf = x , refl
fetch-succeeds (x ∷ xs) (suc n) (s≤s pf) = fetch-succeeds xs n pf

-- Helper: execInstr doesn't depend on code after current instruction
-- (The prog argument is only used for blr which reads from registers, not from prog)
execInstr-prog-irrelevant : ∀ (prog1 prog2 : Program) (s : State) (instr : Instr) →
  execInstr prog1 s instr ≡ execInstr (prog1 ++ prog2) s instr
execInstr-prog-irrelevant prog1 prog2 s instr = refl  -- prog is unused in execInstr

-- Helper: step on prog1 equals execInstr when halted=false and fetch succeeds
step-unfold : ∀ (prog : Program) (s : State) (instr : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just instr →
  step prog s ≡ execInstr prog s instr
step-unfold prog s instr refl fetch-eq with fetch prog (pc s) | fetch-eq
... | just .instr | refl = refl

-- Helper: step produces same result when pc < length prog1
-- Proof: Both step calls see halted s = false, both fetch the same instruction
-- (by fetch-append-left), and execInstr gives same result (prog argument unused).
step-concat-left : ∀ (prog1 prog2 : Program) (s : State) →
  halted s ≡ false →
  pc s < length prog1 →
  step (prog1 ++ prog2) s ≡ step prog1 s
step-concat-left prog1 prog2 s h-false pc-bound =
  let (instr , fetch-eq) = fetch-succeeds prog1 (pc s) pc-bound
      fetch-concat-eq = trans (fetch-append-left prog1 prog2 (pc s) pc-bound) fetch-eq
      -- step prog1 s = execInstr prog1 s instr
      step1-eq : step prog1 s ≡ execInstr prog1 s instr
      step1-eq = step-unfold prog1 s instr h-false fetch-eq
      -- step (prog1 ++ prog2) s = execInstr (prog1 ++ prog2) s instr
      step-concat-eq : step (prog1 ++ prog2) s ≡ execInstr (prog1 ++ prog2) s instr
      step-concat-eq = step-unfold (prog1 ++ prog2) s instr h-false fetch-concat-eq
      -- execInstr prog1 s instr = execInstr (prog1 ++ prog2) s instr
      exec-eq : execInstr prog1 s instr ≡ execInstr (prog1 ++ prog2) s instr
      exec-eq = execInstr-prog-irrelevant prog1 prog2 s instr
  in trans step-concat-eq (trans (sym exec-eq) (sym step1-eq))

-- Helper: unfold exec (suc n) when step succeeds and halted is false
-- exec (suc n) prog s = exec n prog s₁ when step prog s = just s₁ and halted s₁ = false
exec-suc-step : ∀ (n : ℕ) (prog : Program) (s s₁ : State) →
  halted s ≡ false →
  step prog s ≡ just s₁ →
  halted s₁ ≡ false →
  exec (suc n) prog s ≡ exec n prog s₁
exec-suc-step n prog s s₁ refl step-eq halt-eq
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | halt-eq
...   | false | refl = refl

-- Helper: unfold exec (suc n) when step succeeds and halted is true
-- exec (suc n) prog s = just s₁ when step prog s = just s₁ and halted s₁ = true
exec-suc-halt : ∀ (n : ℕ) (prog : Program) (s s₁ : State) →
  halted s ≡ false →
  step prog s ≡ just s₁ →
  halted s₁ ≡ true →
  exec (suc n) prog s ≡ just s₁
exec-suc-halt n prog s s₁ refl step-eq halt-eq
  with step prog s | step-eq
... | just .s₁ | refl with halted s₁ | halt-eq
...   | true | refl = refl

-- | For Common.Exec: exec (suc n) unfolds to exec n when step succeeds and result not halted
exec-step-continue : ∀ (n : ℕ) (prog : Program) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec (suc n) prog s ≡ exec n prog s'
exec-step-continue n prog s s' step-eq halt-eq rewrite step-eq | halt-eq = refl

-- | For Common.Exec: exec (suc n) = just s' when step halts
exec-halt-step : ∀ (n : ℕ) (prog : Program) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ true →
  exec (suc n) prog s ≡ just s'
exec-halt-step n prog s s' step-eq halt-eq rewrite step-eq | halt-eq = refl

-- Import N-step execution lemmas from Common.Exec
-- Provides exec-two-steps through exec-nine-steps
open import Once.Backend.Common.Exec
  halted step exec exec-step-continue exec-halt-step
  public

-- Main lemma: execution matches while pc stays strictly within prog1
exec-concat-left : ∀ (n : ℕ) (prog1 prog2 : Program) (s s' : State) →
  halted s ≡ false →
  exec n prog1 s ≡ just s' →
  (halted s' ≡ false → pc s' < length prog1) →  -- If not halted, still in bounds
  exec n (prog1 ++ prog2) s ≡ just s'

-- Base case: n = 0
exec-concat-left zero prog1 prog2 s .s h-false refl _ = refl

-- Inductive case: n = suc n'
exec-concat-left (suc n') prog1 prog2 s s' h-false exec-eq pc-inv
  with step prog1 s in step-eq
... | nothing with exec (suc n') prog1 s | exec-eq
...   | ._ | ()  -- exec can't succeed if step fails
exec-concat-left (suc n') prog1 prog2 s s' h-false exec-eq pc-inv
    | just s₁ with halted s₁ in halt-eq
-- s₁ is halted: exec returns s₁ = s'
...   | true = exec-halt-case
  where
    postulate
      pc-in-bounds : pc s < length prog1
      -- Extracting s' = s₁ from exec-eq when halted
      s'-is-s₁ : s' ≡ s₁

    step-concat-eq : step (prog1 ++ prog2) s ≡ just s₁
    step-concat-eq = trans (step-concat-left prog1 prog2 s h-false pc-in-bounds) step-eq

    exec-halt-case : exec (suc n') (prog1 ++ prog2) s ≡ just s'
    exec-halt-case = subst (λ x → exec (suc n') (prog1 ++ prog2) s ≡ just x)
                           (sym s'-is-s₁)
                           (exec-suc-halt n' (prog1 ++ prog2) s s₁ h-false step-concat-eq halt-eq)
-- s₁ is not halted: recurse
...   | false = exec-recurse-case
  where
    postulate
      pc-s-bound : pc s < length prog1
      pc-s₁-inv : halted s' ≡ false → pc s' < length prog1
      exec-n'-eq : exec n' prog1 s₁ ≡ just s'

    step-concat-eq : step (prog1 ++ prog2) s ≡ just s₁
    step-concat-eq = trans (step-concat-left prog1 prog2 s h-false pc-s-bound) step-eq

    -- Unfold LHS: exec (suc n') (prog1 ++ prog2) s = exec n' (prog1 ++ prog2) s₁
    lhs-unfold : exec (suc n') (prog1 ++ prog2) s ≡ exec n' (prog1 ++ prog2) s₁
    lhs-unfold = exec-suc-step n' (prog1 ++ prog2) s s₁ h-false step-concat-eq halt-eq

    -- IH: exec n' (prog1 ++ prog2) s₁ = just s'
    ih : exec n' (prog1 ++ prog2) s₁ ≡ just s'
    ih = exec-concat-left n' prog1 prog2 s₁ s' halt-eq exec-n'-eq pc-s₁-inv

    exec-recurse-case : exec (suc n') (prog1 ++ prog2) s ≡ just s'
    exec-recurse-case = trans lhs-unfold ih

-- NOTE: exec-concat-continue and run-concat-seq postulates were REMOVED.
-- They were fuel-based lemmas no longer needed with Star-based proofs.
-- The Star approach uses star-trans for composition, avoiding fuel arithmetic.

------------------------------------------------------------------------
-- Well-Founded IR Correctness (Mutual Recursion Structure)
------------------------------------------------------------------------

-- The mutual recursion cluster (compose, case, pair, curry) requires proving
-- that running compiled code on sub-IR terms produces correct results.
-- This is handled by structural induction on IR.
--
-- Key insight: For any IR term ir, running compile-aarch64 ir with correct
-- preconditions produces a state where x0 = encode (eval ir x).
--
-- The preconditions are:
--   - halted s ≡ false (not already halted)
--   - pc s ≡ 0 (start at beginning)
--   - readReg (regs s) x0 ≡ encode x (input in x0)
--   - memory s ≡ encodedMemory (access to encoded values)
--
-- For recursive cases:
--   - compose (g ∘ f): IH on f gives intermediate result, IH on g gives final
--   - case [f,g]: IH on f or g depending on tag
--   - pair ⟨f,g⟩: IH on f, preserve input, IH on g
--   - curry f: IH on f when thunk is called

-- | State transformation predicate
-- This captures what running an IR term does to the state.
IRCorrectAt : ∀ {i} {A B : Type} → IR A B → ⟦ A ⟧ → State → State → Set
IRCorrectAt ir x s s' =
  run (compile-aarch64 ir) s ≡ just s'
  × halted s' ≡ true
  × readReg (regs s') x0 ≡ encode (eval ir x)

-- | Valid input state predicate
ValidInputState : ∀ {A : Type} → ⟦ A ⟧ → State → Set
ValidInputState x s =
  halted s ≡ false
  × pc s ≡ 0
  × readReg (regs s) x0 ≡ encode x
  × memory s ≡ encodedMemory

-- | The main correctness property we want to prove for each IR term
-- This will be proven by mutual recursion on IR structure.
IRCorrect : ∀ {i} {A B : Type} → IR A B → Set
IRCorrect {_} {A} {B} ir = ∀ (x : ⟦ A ⟧) (s : State) →
  ValidInputState x s →
  ∃[ s' ] IRCorrectAt ir x s s'

------------------------------------------------------------------------
-- Initial State with Input
------------------------------------------------------------------------

-- | Create initial state with input value in x0
initWithInput : ∀ {A : Type} → ⟦ A ⟧ → State
initWithInput x = mkstate
  (writeReg emptyRegFile x0 (encode x))
  encodedMemory
  initPSTATE
  0
  false

-- | Property: input is correctly placed in x0
-- Proven using readReg-writeReg-same
initWithInput-x0 : ∀ {A : Type} (x : ⟦ A ⟧) →
  readReg (regs (initWithInput x)) x0 ≡ encode x
initWithInput-x0 x = readReg-writeReg-same emptyRegFile x0 (encode x)

-- | Property: initial state is not halted
initWithInput-halted : ∀ {A : Type} (x : ⟦ A ⟧) →
  halted (initWithInput x) ≡ false
initWithInput-halted x = refl

-- | Property: initial pc is 0
initWithInput-pc : ∀ {A : Type} (x : ⟦ A ⟧) →
  pc (initWithInput x) ≡ 0
initWithInput-pc x = refl

-- | Property: initial memory is encodedMemory
initWithInput-memory : ∀ {A : Type} (x : ⟦ A ⟧) →
  memory (initWithInput x) ≡ encodedMemory
initWithInput-memory x = refl

------------------------------------------------------------------------
-- P3: Single-Instruction Step Helpers
------------------------------------------------------------------------

-- These lemmas describe what happens when executing a single step of an
-- instruction. They directly follow from the definition of execInstr.

-- | What execInstr does for nop
execInstr-nop : ∀ (prog : Program) (s : State) →
  execInstr prog s nop ≡ just (record s { pc = pc s +ℕ 1 })
execInstr-nop prog s = refl

-- | What execInstr does for mov with immediate
execInstr-mov-imm : ∀ (prog : Program) (s : State) (dst : Reg) (n : ℕ) →
  execInstr prog s (mov dst (imm n)) ≡ just (record s { regs = writeReg (regs s) dst n ; pc = pc s +ℕ 1 })
execInstr-mov-imm prog s dst n = refl

-- | What execInstr does for mov with register source
execInstr-mov-reg : ∀ (prog : Program) (s : State) (dst src : Reg) →
  execInstr prog s (mov dst (reg src)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) src) ; pc = pc s +ℕ 1 })
execInstr-mov-reg prog s dst src = refl

-- | What execInstr does for mov (general case when readOperand succeeds)
execInstr-mov-success : ∀ (prog : Program) (s : State) (dst : Reg) (src : Operand) (v : Word) →
  readOperand s src ≡ just v →
  execInstr prog s (mov dst src) ≡ just (record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 })
execInstr-mov-success prog s dst src v src-eq with readOperand s src | src-eq
... | just .v | refl = refl

-- | What execInstr does for brk
execInstr-brk : ∀ (prog : Program) (s : State) (n : ℕ) →
  execInstr prog s (brk n) ≡ just (record s { halted = true })
execInstr-brk prog s n = refl

-- | What execInstr does for sub-sp
execInstr-sub-sp : ∀ (prog : Program) (s : State) (n : ℕ) →
  execInstr prog s (sub-sp n) ≡ just (record s { regs = writeSP (regs s) (readSP (regs s) ∸ n) ; pc = pc s +ℕ 1 })
execInstr-sub-sp prog s n = refl

-- | What execInstr does for mov-from-sp
execInstr-mov-from-sp : ∀ (prog : Program) (s : State) (dst : Reg) →
  execInstr prog s (mov-from-sp dst) ≡ just (record s { regs = writeReg (regs s) dst (readSP (regs s)) ; pc = pc s +ℕ 1 })
execInstr-mov-from-sp prog s dst = refl

-- | What execInstr does for str-zr
execInstr-str-zr : ∀ (prog : Program) (s : State) (m : Mem) →
  execInstr prog s (str-zr m) ≡ just (record (writeToMem s m 0) { pc = pc s +ℕ 1 })
execInstr-str-zr prog s m = refl

-- | What execInstr does for str
execInstr-str : ∀ (prog : Program) (s : State) (src : Reg) (m : Mem) →
  execInstr prog s (str src m) ≡ just (record (writeToMem s m (readReg (regs s) src)) { pc = pc s +ℕ 1 })
execInstr-str prog s src m = refl

-- | What execInstr does for ldr (when memory read succeeds)
execInstr-ldr-success : ∀ (prog : Program) (s : State) (dst : Reg) (m : Mem) (v : Word) →
  readMem (memory s) (effectiveAddr s m) ≡ just v →
  execInstr prog s (ldr dst m) ≡ just (record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 })
execInstr-ldr-success prog s dst m v mem-eq with readMem (memory s) (effectiveAddr s m) | mem-eq
... | just .v | refl = refl

-- | What execInstr does for add with immediate
execInstr-add-imm : ∀ (prog : Program) (s : State) (dst src1 : Reg) (n : ℕ) →
  execInstr prog s (add dst src1 (imm n)) ≡
    just (record s { regs = writeReg (regs s) dst (readReg (regs s) src1 +ℕ n) ; pc = pc s +ℕ 1 })
execInstr-add-imm prog s dst src1 n = refl

-- | What execInstr does for cmp with immediate
execInstr-cmp-imm : ∀ (prog : Program) (s : State) (src : Reg) (n : ℕ) →
  execInstr prog s (cmp src (imm n)) ≡
    just (record s { pstate = updatePSTATE (readReg (regs s) src) n ; pc = pc s +ℕ 1 })
execInstr-cmp-imm prog s src n = refl

-- | What execInstr does for b (unconditional PC-relative branch)
-- PC' = PC + offset (position-independent)
execInstr-b : ∀ (prog : Program) (s : State) (offset : ℕ) →
  execInstr prog s (b offset) ≡ just (record s { pc = pc s +ℕ offset })
execInstr-b prog s offset = refl

-- | What execInstr does for b.ne (branch if not equal, PC-relative)
-- If Z=0: PC' = PC + offset, else PC' = PC + 1
execInstr-b-ne : ∀ (prog : Program) (s : State) (offset : ℕ) →
  execInstr prog s (b-ne offset) ≡
    just (record s { pc = if Z (pstate s) then pc s +ℕ 1 else pc s +ℕ offset })
execInstr-b-ne prog s offset = refl

-- | What execInstr does for b.eq (branch if equal, PC-relative)
-- If Z=1: PC' = PC + offset, else PC' = PC + 1
execInstr-b-eq : ∀ (prog : Program) (s : State) (offset : ℕ) →
  execInstr prog s (b-eq offset) ≡
    just (record s { pc = if Z (pstate s) then pc s +ℕ offset else pc s +ℕ 1 })
execInstr-b-eq prog s offset = refl

-- | What execInstr does for add-sp
execInstr-add-sp : ∀ (prog : Program) (s : State) (n : ℕ) →
  execInstr prog s (add-sp n) ≡
    just (record s { regs = writeSP (regs s) (readSP (regs s) +ℕ n) ; pc = pc s +ℕ 1 })
execInstr-add-sp prog s n = refl

-- | What execInstr does for ldp (load pair, when both reads succeed)
execInstr-ldp-success : ∀ (prog : Program) (s : State) (r1 r2 : Reg) (m : Mem) (v1 v2 : Word) →
  readMem (memory s) (effectiveAddr s m) ≡ just v1 →
  readMem (memory s) (effectiveAddr s m +ℕ 8) ≡ just v2 →
  execInstr prog s (ldp r1 r2 m) ≡
    just (record s { regs = writeReg (writeReg (regs s) r1 v1) r2 v2 ; pc = pc s +ℕ 1 })
execInstr-ldp-success prog s r1 r2 m v1 v2 mem1-eq mem2-eq
  with readMem (memory s) (effectiveAddr s m) | mem1-eq
     | readMem (memory s) (effectiveAddr s m +ℕ 8) | mem2-eq
... | just .v1 | refl | just .v2 | refl = refl

-- | What execInstr does for stp (store pair)
execInstr-stp : ∀ (prog : Program) (s : State) (r1 r2 : Reg) (m : Mem) →
  let addr = effectiveAddr s m
      mem1 = writeMem (memory s) addr (readReg (regs s) r1)
      mem2 = writeMem mem1 (addr +ℕ 8) (readReg (regs s) r2)
  in execInstr prog s (stp r1 r2 m) ≡ just (record s { memory = mem2 ; pc = pc s +ℕ 1 })
execInstr-stp prog s r1 r2 m = refl

-- | What execInstr does for blr (branch and link to register)
execInstr-blr : ∀ (prog : Program) (s : State) (r : Reg) →
  execInstr prog s (blr r) ≡
    just (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1) ; pc = readReg (regs s) r })
execInstr-blr prog s r = refl

-- | What execInstr does for ret (return via x30)
execInstr-ret : ∀ (prog : Program) (s : State) →
  execInstr prog s ret ≡ just (record s { pc = readReg (regs s) x30 })
execInstr-ret prog s = refl

-- | What execInstr does for bl (branch and link, PC-relative)
-- Saves return address to x30, then PC' = PC + offset
execInstr-bl : ∀ (prog : Program) (s : State) (offset : ℕ) →
  execInstr prog s (bl offset) ≡
    just (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1) ; pc = pc s +ℕ offset })
execInstr-bl prog s offset = refl

-- | What execInstr does for adr (PC-relative address)
-- adr computes the absolute address: dst = PC + offset
-- This is crucial for curry to store the correct thunk address.
execInstr-adr : ∀ (prog : Program) (s : State) (dst : Reg) (offset : ℕ) →
  execInstr prog s (adr dst offset) ≡
    just (record s { regs = writeReg (regs s) dst (pc s +ℕ offset) ; pc = pc s +ℕ 1 })
execInstr-adr prog s dst offset = refl

-- | What execInstr does for label (pseudo-instruction)
-- Labels just increment PC by 1 (no operation at runtime)
execInstr-label : ∀ (prog : Program) (s : State) (n : ℕ) →
  execInstr prog s (label n) ≡ just (record s { pc = pc s +ℕ 1 })
execInstr-label prog s n = refl

------------------------------------------------------------------------
-- Step Lemmas for Single-Instruction Programs
------------------------------------------------------------------------

-- | What step does when not halted and fetch succeeds
step-instr : ∀ (prog : Program) (s s' : State) (instr : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just instr →
  execInstr prog s instr ≡ just s' →
  step prog s ≡ just s'
step-instr prog s s' instr h-false fetch-eq exec-eq
  with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-eq
...   | just .instr | refl = exec-eq

-- | What step does when not halted and fetch fails (end of program)
step-end-of-program : ∀ (prog : Program) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-end-of-program prog s h-false fetch-eq
  with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-eq
...   | nothing | refl = refl

-- | exec 1 after a step always returns that step's result
-- Key insight: Looking at exec's definition, when step prog s = just s',
-- exec 1 returns just s' regardless of whether s' is halted.
-- Case halted s' = true:  exec 1 = just s'
-- Case halted s' = false: exec 1 = exec 0 prog s' = just s'
exec-1-step : ∀ (prog : Program) (s s' : State) →
  step prog s ≡ just s' →
  exec 1 prog s ≡ just s'
exec-1-step prog s s' step-eq with step prog s | step-eq
... | just .s' | refl with halted s'
...   | true = refl
...   | false = refl

-- | exec 2 on a single instruction program reaches halted state
-- This is a key lemma for proving single-instruction runners.
-- Proof strategy: Use exec-1-step twice and exec-chain.
exec-2-single-instr : ∀ (prog : Program) (s s₁ : State) →
  halted s ≡ false →
  step prog s ≡ just s₁ →
  halted s₁ ≡ false →
  fetch prog (pc s₁) ≡ nothing →
  ∃[ s' ] (exec 2 prog s ≡ just s' × halted s' ≡ true × s' ≡ record s₁ { halted = true })
exec-2-single-instr prog s s₁ h-false step-eq h₁-false fetch-fail =
  let s₂ = record s₁ { halted = true }
      -- Step 1: exec 1 prog s = just s₁ (using exec-1-step)
      exec-1-s : exec 1 prog s ≡ just s₁
      exec-1-s = exec-1-step prog s s₁ step-eq
      -- Step 2: step prog s₁ = just s₂ (using step-end-of-program)
      step-s₁ : step prog s₁ ≡ just s₂
      step-s₁ = step-end-of-program prog s₁ h₁-false fetch-fail
      -- Step 3: exec 1 prog s₁ = just s₂ (using exec-1-step)
      exec-1-s₁ : exec 1 prog s₁ ≡ just s₂
      exec-1-s₁ = exec-1-step prog s₁ s₂ step-s₁
      -- Step 4: exec 2 prog s = just s₂ (using exec-chain)
      exec-2-eq : exec 2 prog s ≡ just s₂
      exec-2-eq = exec-chain 1 1 prog s s₁ s₂ exec-1-s h₁-false exec-1-s₁
  in s₂ , exec-2-eq , refl , refl

------------------------------------------------------------------------
-- Offset-based execution helpers (for mutual block proofs)
------------------------------------------------------------------------

-- | Helper: true ≡ false is absurd
true≢false : true ≡ false → ⊥
true≢false ()

-- | Single-step non-halting execution
-- If step succeeds with a non-halted state, exec 1 returns that state
exec-one-step-nonhalt : ∀ (prog : Program) (s s' : State) →
  step prog s ≡ just s' →
  halted s' ≡ false →
  exec 1 prog s ≡ just s'
exec-one-step-nonhalt prog s s' step-eq h-false with step prog s | step-eq
... | just .s' | refl with halted s' | h-false
...   | false | refl = refl

-- | Fetching at the end of a prefix returns the first element of suffix
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (rest : Program) →
  fetch (prefix ++ i ∷ rest) (length prefix) ≡ just i
fetch-at-prefix-end [] i rest = refl
fetch-at-prefix-end (x ∷ xs) i rest = fetch-at-prefix-end xs i rest

-- | General step helper: when pc matches, step executes that instruction
step-exec : ∀ (prog : Program) (s : State) (i : Instr) →
  halted s ≡ false →
  fetch prog (pc s) ≡ just i →
  step prog s ≡ execInstr prog s i
step-exec prog s i h-false fetch-eq with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-eq
...   | just .i | refl = refl

-- | Step with pc=0 executes first instruction
step-exec-0 : ∀ (i : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 0 →
  step (i ∷ is) s ≡ execInstr (i ∷ is) s i
step-exec-0 i is s h-false pc-0 =
  step-exec (i ∷ is) s i h-false (subst (λ p → fetch (i ∷ is) p ≡ just i) (sym pc-0) refl)

-- | Step with pc=1 executes second instruction
step-exec-1 : ∀ (i0 i1 : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 1 →
  step (i0 ∷ i1 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ is) s i1
step-exec-1 i0 i1 is s h-false pc-1 =
  step-exec (i0 ∷ i1 ∷ is) s i1 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ is) p ≡ just i1) (sym pc-1) refl)

-- | Step with pc=2 executes third instruction
step-exec-2 : ∀ (i0 i1 i2 : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 2 →
  step (i0 ∷ i1 ∷ i2 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ is) s i2
step-exec-2 i0 i1 i2 is s h-false pc-2 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ is) s i2 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ is) p ≡ just i2) (sym pc-2) refl)

-- | Step with pc=3 executes fourth instruction
step-exec-3 : ∀ (i0 i1 i2 i3 : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 3 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3
step-exec-3 i0 i1 i2 i3 is s h-false pc-3 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) s i3 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ is) p ≡ just i3) (sym pc-3) refl)

-- | Step with pc=4 executes fifth instruction
step-exec-4 : ∀ (i0 i1 i2 i3 i4 : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 4 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4
step-exec-4 i0 i1 i2 i3 i4 is s h-false pc-4 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) s i4 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ is) p ≡ just i4) (sym pc-4) refl)

-- | Step with pc=5 executes sixth instruction
step-exec-5 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (is : Program) (s : State) →
  halted s ≡ false → pc s ≡ 5 →
  step (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s ≡ execInstr (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5
step-exec-5 i0 i1 i2 i3 i4 i5 is s h-false pc-5 =
  step-exec (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) s i5 h-false (subst (λ p → fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ is) p ≡ just i5) (sym pc-5) refl)

-- | Step halts when fetch fails at end of program
step-halt-on-fetch-fail : ∀ (prog : Program) (s : State) →
  halted s ≡ false →
  fetch prog (pc s) ≡ nothing →
  step prog s ≡ just (record s { halted = true })
step-halt-on-fetch-fail prog s h-false fetch-fail with halted s | h-false
... | false | refl with fetch prog (pc s) | fetch-fail
...   | nothing | refl = refl

-- | Step at arbitrary offset in a program
-- When pc = length prefix, step fetches the first instruction of suffix
step-at-offset : ∀ (prefix : Program) (i : Instr) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ i ∷ suffix) s ≡ execInstr (prefix ++ i ∷ suffix) s i
step-at-offset prefix i suffix s h-false pc-eq with halted s | h-false
... | false | refl with fetch (prefix ++ i ∷ suffix) (pc s)
                      | subst (λ p → fetch (prefix ++ i ∷ suffix) p ≡ just i)
                              (sym pc-eq) (fetch-at-prefix-end prefix i suffix)
...   | just .i | refl = refl

------------------------------------------------------------------------
-- Branch and Link Register (blr) Lemmas
------------------------------------------------------------------------

-- | Step a blr instruction at arbitrary offset
-- Combines step-at-offset with execInstr-blr for a convenient lemma.
-- This is crucial for proving apply correctness where blr jumps to closure code.
step-blr-at-offset : ∀ (prefix : Program) (r : Reg) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ blr r ∷ suffix) s ≡
    just (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1)
                   ; pc = readReg (regs s) r })
step-blr-at-offset prefix r suffix s h-false pc-eq =
  trans (step-at-offset prefix (blr r) suffix s h-false pc-eq)
        (execInstr-blr (prefix ++ blr r ∷ suffix) s r)

-- | Key insight for apply: after blr, halted is still false
-- (blr is a branch instruction, not a halting instruction)
blr-preserves-nonhalt : ∀ (s : State) (r : Reg) →
  halted (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1)
                   ; pc = readReg (regs s) r }) ≡ halted s
blr-preserves-nonhalt s r = refl

-- | After blr, the new PC is the value that was in the target register
blr-pc-is-target : ∀ (s : State) (r : Reg) →
  pc (record s { regs = writeReg (regs s) x30 (pc s +ℕ 1)
               ; pc = readReg (regs s) r }) ≡ readReg (regs s) r
blr-pc-is-target s r = refl

-- | After blr, x30 holds the return address (pc + 1)
blr-x30-is-return : ∀ (s : State) (r : Reg) →
  let s' = record s { regs = writeReg (regs s) x30 (pc s +ℕ 1)
                    ; pc = readReg (regs s) r }
  in readReg (regs s') x30 ≡ pc s +ℕ 1
blr-x30-is-return s r = readReg-writeReg-same (regs s) x30 (pc s +ℕ 1)

------------------------------------------------------------------------
-- Return (ret) Lemmas
------------------------------------------------------------------------

-- | Step a ret instruction at arbitrary offset
-- ret jumps to the address in x30 (link register)
step-ret-at-offset : ∀ (prefix : Program) (suffix : Program) (s : State) →
  halted s ≡ false → pc s ≡ length prefix →
  step (prefix ++ ret ∷ suffix) s ≡ just (record s { pc = readReg (regs s) x30 })
step-ret-at-offset prefix suffix s h-false pc-eq =
  trans (step-at-offset prefix ret suffix s h-false pc-eq)
        (execInstr-ret (prefix ++ ret ∷ suffix) s)
