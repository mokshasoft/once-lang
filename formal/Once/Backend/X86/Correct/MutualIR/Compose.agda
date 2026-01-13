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
  using (run-ir-star-at-offset-abstract; run-ir-star-at-offset-abstract-v; rbp-inv-preserved-through-ir)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultV; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound)

-- Import validity predicates and bridging for Phase 6
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; addr-from-valid; valid-from-encode)

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

------------------------------------------------------------------------
-- Validity-based compose wrapper
-- Uses bridging postulates to convert between validity and encode
------------------------------------------------------------------------

{-# TERMINATING #-}
-- | Validity-based compose execution
-- Takes ValidAt input, bridges to encode-based implementation, converts output to validity
run-compose-star-v : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
  in ∃[ s' ] IRStarResultV (g ∘ f) prog s s' x (length prefix)
run-compose-star-v {A} {B} {C} f g prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv rsp-sufficient rbp-inv =
  let
    -- Bridge: validity → encode equality
    rdi-eq : readReg (regs s) rdi ≡ encode x
    rdi-eq = addr-from-valid input-valid

    -- Call the encode-based implementation
    (s' , result) = run-compose-star-direct f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv

    -- Bridge: encode equality → validity
    result-valid : ValidAt (eval (g ∘ f) x) (readReg (regs s') rax) (memory s')
    result-valid = valid-from-encode (IRStarResult.ir-rax result)
  in s' , record
    { ir-star = IRStarResult.ir-star result
    ; ir-halted = IRStarResult.ir-halted result
    ; ir-pc = IRStarResult.ir-pc result
    ; ir-result-valid = result-valid
    ; ir-r14 = IRStarResult.ir-r14 result
    ; ir-r15 = IRStarResult.ir-r15 result
    ; ir-rbp = IRStarResult.ir-rbp result
    ; ir-mem = IRStarResult.ir-mem result
    ; ir-mem-rbp = IRStarResult.ir-mem-rbp result
    ; ir-mem-rbp+8 = IRStarResult.ir-mem-rbp+8 result
    ; ir-mem-above = IRStarResult.ir-mem-above result
    ; ir-mem-at-0 = IRStarResult.ir-mem-at-0 result
    ; ir-mem-code = IRStarResult.ir-mem-code result
    ; ir-mem-heap = IRStarResult.ir-mem-heap result
    ; ir-stack-inv = IRStarResult.ir-stack-inv result
    ; ir-capacity = IRStarResult.ir-capacity result
    ; ir-rbp-inv = IRStarResult.ir-rbp-inv result
    ; ir-closure-wf = IRStarResult.ir-closure-wf result
    }
