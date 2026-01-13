------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Compose
--
-- Compose implementation using abstract dispatcher.
-- Part of the strategy to break large mutual blocks into smaller pieces.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR.Compose where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

-- Import abstract dispatcher and helpers
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (run-ir-star-at-offset-abstract; rbp-inv-preserved-through-ir)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound)

-- Import StackInvariant
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots)
-- Import StackPointer for D041
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)

-- Import Compose helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResult;
         compose-transfer-star; assemble-compose-result)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)
open import Once.Backend.X86.Correct.IR.Compose using (module TransferResult)

open import Once.Postulates using (encode)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

------------------------------------------------------------------------
-- Compose implementation with abstract dispatcher
-- NOTE: Uses TERMINATING pragma as structural recursion is guaranteed
-- by IR structure but hidden by abstract dispatcher
------------------------------------------------------------------------

{-# TERMINATING #-}
-- | Star-based compose execution
-- Uses extracted helpers from IR.Compose - only recursive calls remain here
-- caller-sp: StackPointer from the caller (D041)
run-compose-star-direct : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
  in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)
run-compose-star-direct {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
    s3 , assemble-compose-result f g prefix suffix x s s1 s2 s3 r1 tr r3 refl
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (RECURSIVE via abstract dispatcher)
      step-f : ∃[ s1 ] IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star-at-offset-abstract f prefix suffix-f caller-sp x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv

      s1 : State
      s1 = proj₁ step-f

      r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1 = proj₂ step-f

      -- Step 2: Execute transfer (extracted helper)
      tr : TransferResult f g prefix suffix x s s1
      tr = compose-transfer-star f g prefix suffix x s s1 r1

      s2 = TransferResult.s2 tr

      -- RbpInvariant preserved: rbp unchanged (ir-rbp), rsp may change but invariant maintained
      -- Register preservation from transfer
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResult.rsp-s1-to-s2 tr

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResult.rbp-s1-to-s2 tr

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-through-ir s s1 s2 rbp-inv r1 rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Step 3: Execute g (RECURSIVE via abstract dispatcher)
      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star-at-offset-abstract g prefix-g suffix caller-sp (eval f x) s2
                 (TransferResult.h2 tr) (TransferResult.pc2-g tr) (TransferResult.rdi2-enc tr)
                 (TransferResult.stack-inv-2 tr) (TransferResult.rsp-2>16 tr) rbp-inv-2

      s3 : State
      s3 = proj₁ step-g

      r3 : IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3 = proj₂ step-g
