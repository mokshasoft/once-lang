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

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultV; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound;
         ir-result-valid; ir-mem-rbp; ir-mem-rbp+8; ir-mem-above; ir-mem-at-0;
         ir-mem-code; ir-mem-heap; ir-capacity; ir-closure-wf;
         rbp-inv-preserved-unchanged)

-- Import validity predicates and bridging
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; addr-from-valid; valid-from-encode; valid-subst-addr-mem)

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
-- | Validity-based compose execution
-- Uses validity-based dispatcher for recursive calls
-- Note: Still bridges to encode for helper functions (compose-transfer-star, assemble-compose-result)
--       until those helpers are converted to validity
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

      -- Create IRStarResult from IRStarResultV for compose-transfer-star
      -- Note: ir-rax still needs bridging because compose-transfer-star computes rdi2-enc
      r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1 = record
        { ir-star = IRStarResultV.ir-star r1-v
        ; ir-halted = IRStarResultV.ir-halted r1-v
        ; ir-pc = IRStarResultV.ir-pc r1-v
        ; ir-rax = addr-from-valid (IRStarResultV.ir-result-valid r1-v)
        ; ir-r14 = IRStarResultV.ir-r14 r1-v
        ; ir-r15 = IRStarResultV.ir-r15 r1-v
        ; ir-rbp = IRStarResultV.ir-rbp r1-v
        ; ir-mem = IRStarResultV.ir-mem r1-v
        ; ir-mem-rbp = IRStarResultV.ir-mem-rbp r1-v
        ; ir-mem-rbp+8 = IRStarResultV.ir-mem-rbp+8 r1-v
        ; ir-stack-inv = IRStarResultV.ir-stack-inv r1-v
        ; ir-capacity = IRStarResultV.ir-capacity r1-v
        ; ir-rbp-inv = IRStarResultV.ir-rbp-inv r1-v
        ; ir-mem-above = IRStarResultV.ir-mem-above r1-v
        ; ir-mem-at-0 = IRStarResultV.ir-mem-at-0 r1-v
        ; ir-mem-code = IRStarResultV.ir-mem-code r1-v
        ; ir-mem-heap = IRStarResultV.ir-mem-heap r1-v
        ; ir-closure-wf = IRStarResultV.ir-closure-wf r1-v
        }

      -- Step 2: Execute transfer (still use encode-based helper for now)
      tr : TransferResult f g prefix suffix x s s1
      tr = compose-transfer-star f g prefix suffix x s s1 r1

      s2 = TransferResult.s2 tr

      -- RbpInvariant preserved through IR execution
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResult.rsp-s1-to-s2 tr

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResult.rbp-s1-to-s2 tr

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-unchanged s1 s2 (IRStarResultV.ir-rbp-inv r1-v) rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via direct propagation
      -- The transfer moves rax→rdi and doesn't change memory
      -- So validity at rax in s1 becomes validity at rdi in s2
      -- Using valid-subst-addr-mem instead of round-tripping through encode
      input-valid-for-g : ValidAt (eval f x) (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-addr-mem
        (IRStarResultV.ir-result-valid r1-v)  -- ValidAt at rax in s1
        (TransferResult.rdi2-raw tr)           -- rdi in s2 = rax in s1
        (TransferResult.mem-s1-to-s2 tr)       -- memory unchanged

      -- Step 3: Execute g (RECURSIVE via validity-based dispatcher)
      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star-at-offset-abstract-v g prefix-g suffix caller-sp (eval f x) s2
                 (TransferResult.h2 tr) (TransferResult.pc2-g tr) input-valid-for-g
                 (TransferResult.stack-inv-2 tr) (TransferResult.rsp-2>16 tr) rbp-inv-2

      s3 : State
      s3 = proj₁ step-g

      r3-v : IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3-v = proj₂ step-g

      -- Create IRStarResult from IRStarResultV for assemble-compose-result
      r3 : IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3 = record
        { ir-star = IRStarResultV.ir-star r3-v
        ; ir-halted = IRStarResultV.ir-halted r3-v
        ; ir-pc = IRStarResultV.ir-pc r3-v
        ; ir-rax = addr-from-valid (IRStarResultV.ir-result-valid r3-v)
        ; ir-r14 = IRStarResultV.ir-r14 r3-v
        ; ir-r15 = IRStarResultV.ir-r15 r3-v
        ; ir-rbp = IRStarResultV.ir-rbp r3-v
        ; ir-mem = IRStarResultV.ir-mem r3-v
        ; ir-mem-rbp = IRStarResultV.ir-mem-rbp r3-v
        ; ir-mem-rbp+8 = IRStarResultV.ir-mem-rbp+8 r3-v
        ; ir-stack-inv = IRStarResultV.ir-stack-inv r3-v
        ; ir-capacity = IRStarResultV.ir-capacity r3-v
        ; ir-rbp-inv = IRStarResultV.ir-rbp-inv r3-v
        ; ir-mem-above = IRStarResultV.ir-mem-above r3-v
        ; ir-mem-at-0 = IRStarResultV.ir-mem-at-0 r3-v
        ; ir-mem-code = IRStarResultV.ir-mem-code r3-v
        ; ir-mem-heap = IRStarResultV.ir-mem-heap r3-v
        ; ir-closure-wf = IRStarResultV.ir-closure-wf r3-v
        }

      -- Assemble encode-based result then convert to validity
      result : IRStarResult (g ∘ f) prog s s3 x (length prefix)
      result = assemble-compose-result f g prefix suffix x s s1 s2 s3 r1 tr r3 refl

      -- Convert to IRStarResultV
      result-v : IRStarResultV (g ∘ f) prog s s3 x (length prefix)
      result-v = record
        { ir-star = IRStarResult.ir-star result
        ; ir-halted = IRStarResult.ir-halted result
        ; ir-pc = IRStarResult.ir-pc result
        ; ir-result-valid = ir-result-valid r3-v  -- Use g's validity directly
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
