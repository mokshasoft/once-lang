------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Dispatcher
--
-- Abstract dispatcher interface for breaking mutual recursion.
-- Each implementation module (Compose, Pair, Case) imports this
-- abstract interface and implements its functions independently.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR.Dispatcher where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ir-rbp-inv; rbp-inv-preserved-unchanged)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)

open import Once.Postulates using (encode)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Once.Backend.X86.Semantics.State public

------------------------------------------------------------------------
-- Helper functions for RbpInvariant preservation
------------------------------------------------------------------------

-- RbpInvariant is preserved through IR execution when rsp and rbp are unchanged
-- Uses ir-rbp-inv from IRStarResult and register preservation from transfer
rbp-inv-preserved-through-ir : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {A B} {ir : IR A B} {prog x offset} →
  IRStarResult ir prog s s1 x offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir s s1 s2 _ {ir = ir} r rsp2-eq rbp2-eq =
  -- s1 has RbpInvariant from ir-rbp-inv r
  -- s2 has same rsp and rbp as s1, so RbpInvariant is preserved
  rbp-inv-preserved-unchanged s1 s2 (ir-rbp-inv r) rsp2-eq rbp2-eq

------------------------------------------------------------------------
-- Abstract dispatcher signatures (to be implemented concretely later)
------------------------------------------------------------------------

postulate
  -- | Abstract dispatcher for non-stateful IR execution
  -- caller-sp: StackPointer representing the caller's stack frame (D041)
  run-ir-star-at-offset-abstract : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)
