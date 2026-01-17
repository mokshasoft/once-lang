------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Case
--
-- Case implementation as a parameterized module.
-- Takes a size-bounded recursive dispatcher as a module parameter.
-- Enables well-founded recursion on IR size via Acc pattern.
------------------------------------------------------------------------

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

-- Import types needed for module parameter signature
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots; StackCapacity; ir-stack-requirement)
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; [,]-f-smaller; [,]-g-smaller)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong₂)

-- Parameterized module: takes size bound and size-bounded dispatcher
module Once.Backend.X86.Correct.MutualIR.Case
  (bound : ℕ)
  (run-ir-star : ∀ {A B} (ir : IR A B) → ir-size ir < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement ir) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix))
  where

-- Imports needed for case execution
open import Data.Sum using (inj₁; inj₂)

------------------------------------------------------------------------
-- Case implementation using size-bounded dispatcher
-- Termination is proven via Acc pattern on ir-size in MutualIR.agda
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Case execution functions
--
-- POSTULATE ELIMINATION: These postulates can be eliminated by:
-- 1. Updating the proofs to match the new frame-based CaseInlSetupResult/CaseInrSetupResult
--    which have frame semantics (rsp/rbp modified, memory modified by push)
-- 2. Using stack-inv-preserved-r15-unchanged instead of stack-inv-preserved-mem-rsp
-- 3. Updating all hard-coded PC offsets (4→6 for inl setup, etc.)
-- 4. Threading saved-rbp through the proof chain
------------------------------------------------------------------------

-- | Validity-based case execution (inl branch)
-- Executes: frame setup (2), prefix (4), f, jmp, cleanup (2)
postulate
  run-case-star-direct-inl : ∀ {A B C} (f : IR A C) (g : IR B C) →
    ir-size f < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt {A + B} (inj₁ a) (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement [ f , g ]) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResultV [ f , g ] prog s s' (inj₁ a) (length prefix)

-- | Validity-based case execution (inr branch)
-- Executes: frame setup (2), prefix (3), jne taken to label, prefix-right (2), g, cleanup (2)
postulate
  run-case-star-direct-inr : ∀ {A B C} (f : IR A C) (g : IR B C) →
    ir-size g < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt {A + B} (inj₂ b) (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement [ f , g ]) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResultV [ f , g ] prog s s' (inj₂ b) (length prefix)

-- | Validity-based case execution dispatcher
-- Dispatches to branch implementations based on sum injection
run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A + B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s' ] IRStarResultV [ f , g ] prog s s' x (length prefix)
run-case-star-direct {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv
  with x
... | inj₁ a = run-case-star-direct-inl f g f<bound prefix suffix caller-sp a s h-false pc-eq input-valid stack-inv cap-in rbp-inv
... | inj₂ b = run-case-star-direct-inr f g g<bound prefix suffix caller-sp b s h-false pc-eq input-valid stack-inv cap-in rbp-inv

-- | Validity-based case execution
-- Takes ValidAt input, returns IRStarResultV
-- Delegates directly to validity-based branch implementations - no bridging!
-- Takes size proofs for sub-terms to enable well-founded recursion.
run-case-star-v : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A + B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s' ] IRStarResultV [ f , g ] prog s s' x (length prefix)
run-case-star-v {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  -- Delegate directly - run-case-star-direct now takes validity and returns IRStarResultV
  run-case-star-direct f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv

