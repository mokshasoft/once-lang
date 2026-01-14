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

-- Import abstract dispatcher (validity-based only)
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (run-ir-star-at-offset-abstract-v)

-- Import StarBase for result types (validity-based only)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResultV; ir-result-valid; rbp-inv-preserved-unchanged)

-- Import validity predicates (no bridging postulates needed!)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-subst-addr-mem)

-- Import StackInvariant
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots)
-- Import StackPointer for D041
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)

-- Import Compose helpers (validity-based versions)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResultV;
         compose-transfer-star-v; assemble-compose-result-v)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)
open import Once.Backend.X86.Correct.IR.Compose using (module TransferResultV)

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
-- | Validity-based compose execution
-- Uses validity-based dispatcher and helpers - no encode bridging needed!
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
    s3 , result-v
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (RECURSIVE via validity-based dispatcher)
      step-f : ∃[ s1 ] IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star-at-offset-abstract-v f prefix suffix-f caller-sp x s h-false pc-eq input-valid stack-inv rsp-sufficient rbp-inv

      s1 : State
      s1 = proj₁ step-f

      r1-v : IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1-v = proj₂ step-f

      -- Step 2: Execute transfer (validity-based helper - no encode bridging!)
      tr : TransferResultV f g prefix suffix x s s1
      tr = compose-transfer-star-v f g prefix suffix x s s1 r1-v

      s2 = TransferResultV.s2 tr

      -- RbpInvariant preserved through IR execution
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResultV.rsp-s1-to-s2 tr

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResultV.rbp-s1-to-s2 tr

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-unchanged s1 s2 (IRStarResultV.ir-rbp-inv r1-v) rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via direct propagation
      -- The transfer moves rax→rdi and doesn't change memory
      -- So validity at rax in s1 becomes validity at rdi in s2
      input-valid-for-g : ValidAt (eval f x) (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-addr-mem
        (IRStarResultV.ir-result-valid r1-v)  -- ValidAt at rax in s1
        (TransferResultV.rdi2-raw tr)          -- rdi in s2 = rax in s1
        (TransferResultV.mem-s1-to-s2 tr)      -- memory unchanged

      -- Step 3: Execute g (RECURSIVE via validity-based dispatcher)
      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star-at-offset-abstract-v g prefix-g suffix caller-sp (eval f x) s2
                 (TransferResultV.h2 tr) (TransferResultV.pc2-g tr) input-valid-for-g
                 (TransferResultV.stack-inv-2 tr) (TransferResultV.rsp-2>16 tr) rbp-inv-2

      s3 : State
      s3 = proj₁ step-g

      r3-v : IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3-v = proj₂ step-g

      -- Assemble final result (validity-based - no encode bridging!)
      result-v : IRStarResultV (g ∘ f) prog s s3 x (length prefix)
      result-v = assemble-compose-result-v f g prefix suffix x s s1 s2 s3 r1-v tr r3-v refl
