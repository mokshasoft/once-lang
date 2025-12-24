------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.StarBase
--
-- Star-based IR execution result types for AArch64.
-- Defines IRStarResult record for uniform proof composition.
--
-- Note: Actual run-*-star functions will be added once supporting
-- modules (RegisterLemmas, FetchStep, etc.) are extracted.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.StarBase where

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; eval)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (encode)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- IRStarResult: Result type for Star-based IR execution
------------------------------------------------------------------------

-- | Record type for Star-based IR execution result
-- Contains all properties needed for proof composition.
--
-- Key differences from x86 version:
-- - Uses x0 as result register (not rax)
-- - Uses x20, x21 as callee-saved context (not r14, r15)
-- - Uses x29 as frame pointer (not rbp)
-- - Uses SP functions (readSP) for stack pointer
record IRStarResult {A B : Type} (ir : IR A B) (prog : Program)
                    (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set where
  field
    -- Execution
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-x0         : readReg (regs s') x0 ≡ encode (eval ir x)

    -- Register preservation (callee-saved)
    ir-x20        : readReg (regs s') x20 ≡ readReg (regs s) x20
    ir-x21        : readReg (regs s') x21 ≡ readReg (regs s) x21
    ir-x29        : readReg (regs s') x29 ≡ readReg (regs s) x29
    ir-x30        : readReg (regs s') x30 ≡ readReg (regs s) x30

    -- Memory preservation
    -- Memory at x21 (pair context pointer)
    ir-mem-x21    : readMem (memory s') (readReg (regs s) x21)
                  ≡ readMem (memory s) (readReg (regs s) x21)
    -- Memory at x29 (frame pointer / return context)
    ir-mem-x29    : readMem (memory s') (readReg (regs s) x29)
                  ≡ readMem (memory s) (readReg (regs s) x29)
    -- Memory at x29+8 (return address storage)
    ir-mem-x29+8  : readMem (memory s') (readReg (regs s) x29 +ℕ 8)
                  ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Invariants
    ir-stack-inv  : StackInvariant s'
    ir-sp-bound   : readSP (regs s') > 16

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type for the recursive IR execution function
------------------------------------------------------------------------

-- | Type signature for the recursive IR execution function.
-- Recursive case handlers (compose, pair, case, curry, apply) take
-- an IRRunner as a parameter, allowing them to be defined outside
-- the mutual block. This dramatically reduces compilation time.
IRRunner : Set
IRRunner = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- Helper: combine two IRStarResults (for compose-style proofs)
------------------------------------------------------------------------

-- | Combine two Star proofs when PC and register conditions align
-- This is the key composition lemma for sequential IR execution
combine-star-results : ∀ {A B C : Type}
  (f : IR A B) (g : IR B C)
  (prog : Program) (s₀ s₁ s₂ : State)
  (x : ⟦ A ⟧) (offset : ℕ) →
  IRStarResult f prog s₀ s₁ x offset →
  -- Second result needs adjusted preconditions
  pc s₁ ≡ offset +ℕ compile-length f →
  readReg (regs s₁) x0 ≡ encode (eval f x) →
  IRStarResult g prog s₁ s₂ (eval f x) (offset +ℕ compile-length f) →
  -- Combined result
  Star prog s₀ s₂
combine-star-results f g prog s₀ s₁ s₂ x offset res-f pc-eq x0-eq res-g =
  star-trans (ir-star res-f) (ir-star res-g)
