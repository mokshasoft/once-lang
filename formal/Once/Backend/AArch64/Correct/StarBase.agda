{-# OPTIONS --sized-types #-}
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
open import Once.Backend.AArch64.Semantics using (Word)
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (encode)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single)

open import Size using (Size)
open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
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
record IRStarResult {i} {A B : Type} (ir : IR i A B) (prog : Program)
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
    -- SP preservation (stack grows down, so sp' ≤ sp)
    ir-sp         : readSP (regs s') ≤ readSP (regs s)

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
    ir-x29-inv    : X29Invariant s'
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
IRRunner = ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- Helper: combine two IRStarResults (for compose-style proofs)
------------------------------------------------------------------------

-- | Combine two Star proofs when PC and register conditions align
-- This is the key composition lemma for sequential IR execution
combine-star-results : ∀ {i} {A B C : Type}
  (f : IR i A B) (g : IR i B C)
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

------------------------------------------------------------------------
-- IRStarResultS: Stateful version with explicit address
------------------------------------------------------------------------

-- | Stateful IR execution result record
-- Like IRStarResult but with explicit address instead of encode.
-- This enables proofs that don't depend on encoding postulates.
--
-- Key difference: ir-x0-s returns the raw address, and validity
-- (PairAtS, InlAtS, InrAtS) is tracked separately at the call site.
record IRStarResultS {i} {A B : Type} (ir : IR i A B) (prog : Program)
                     (s s' : State) (addr-out : Word) (offset : ℕ) : Set where
  field
    -- Execution
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-x0-s       : readReg (regs s') x0 ≡ addr-out  -- Address, not encode!

    -- Register preservation (callee-saved)
    ir-x20        : readReg (regs s') x20 ≡ readReg (regs s) x20
    ir-x21        : readReg (regs s') x21 ≡ readReg (regs s) x21
    ir-x29        : readReg (regs s') x29 ≡ readReg (regs s) x29
    ir-x30        : readReg (regs s') x30 ≡ readReg (regs s) x30
    -- SP preservation (stack grows down, so sp' ≤ sp)
    ir-sp         : readSP (regs s') ≤ readSP (regs s)

    -- Memory preservation
    ir-mem-x21    : readMem (memory s') (readReg (regs s) x21)
                  ≡ readMem (memory s) (readReg (regs s) x21)
    ir-mem-x29    : readMem (memory s') (readReg (regs s) x29)
                  ≡ readMem (memory s) (readReg (regs s) x29)
    ir-mem-x29+8  : readMem (memory s') (readReg (regs s) x29 +ℕ 8)
                  ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)

    -- Invariants
    ir-stack-inv  : StackInvariant s'
    ir-x29-inv    : X29Invariant s'
    ir-sp-bound   : readSP (regs s') > 16

open IRStarResultS public

-- | Convert IRStarResult to IRStarResultS
-- This allows gradual migration to stateful proofs
convert-to-stateful : ∀ {i : Size} {A B : Type} (ir : IR i A B) (prog : Program)
                      (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) →
  IRStarResult ir prog s s' x offset →
  IRStarResultS ir prog s s' (encode (eval ir x)) offset
convert-to-stateful ir prog s s' x offset res = record
  { ir-star      = IRStarResult.ir-star res
  ; ir-halted    = IRStarResult.ir-halted res
  ; ir-pc        = IRStarResult.ir-pc res
  ; ir-x0-s      = IRStarResult.ir-x0 res
  ; ir-x20       = IRStarResult.ir-x20 res
  ; ir-x21       = IRStarResult.ir-x21 res
  ; ir-x29       = IRStarResult.ir-x29 res
  ; ir-x30       = IRStarResult.ir-x30 res
  ; ir-sp        = IRStarResult.ir-sp res
  ; ir-mem-x21   = IRStarResult.ir-mem-x21 res
  ; ir-mem-x29   = IRStarResult.ir-mem-x29 res
  ; ir-mem-x29+8 = IRStarResult.ir-mem-x29+8 res
  ; ir-stack-inv = IRStarResult.ir-stack-inv res
  ; ir-x29-inv   = IRStarResult.ir-x29-inv res
  ; ir-sp-bound  = IRStarResult.ir-sp-bound res
  }

------------------------------------------------------------------------
-- IRRunnerS: Stateful version of IRRunner
------------------------------------------------------------------------

-- | Type signature for stateful IR execution.
-- Returns explicit address instead of encode.
IRRunnerS : Set
IRRunnerS = ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-in →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 ir ++ suffix
  in ∃[ s' ] ∃[ addr-out ] IRStarResultS ir prog s s' addr-out (length prefix)
