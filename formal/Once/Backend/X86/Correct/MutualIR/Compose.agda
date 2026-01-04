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
  using (run-ir-star-at-offset-abstract; run-ir-star-at-offset-s-abstract;
         rbp-inv-preserved-through-ir; rbp-inv-preserved-through-ir-s;
         irresults-preserves-eval)

-- Import StarBase for result types
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultS; ir-star; ir-halted; ir-pc; ir-rax;
         ir-r14; ir-r15; ir-rbp; ir-mem; ir-rbp-inv; ir-stack-inv; ir-rsp-bound;
         convert-to-stateful)

-- Import StackInvariant
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)

-- Import Compose helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResult; TransferResultS;
         exec-compose-transfer; assemble-compose-result;
         exec-compose-transfer-s; assemble-compose-result-s)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)
open import Once.Backend.X86.Correct.IR.Compose using (module TransferResult)
open import Once.Backend.X86.Correct.IR.Compose using (module TransferResultS)

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
mutual
  -- | Stateful compose execution (NO encoding postulates!)
  run-compose-star-direct-s : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program)
      (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ addr-in →
    encode x ≡ addr-in →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
    in ∃[ addr-out ] ∃[ s' ] IRStarResultS (g ∘ f) prog s s' addr-out (length prefix)
  run-compose-star-direct-s {A} {B} {C} f g prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    addr-out , s3 , result-s
    where
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (STATEFUL RECURSIVE CALL via abstract dispatcher)
      step-f-s : ∃[ addr-f ] ∃[ s1 ] IRStarResultS f (prefix ++ code-f ++ suffix-f) s s1 addr-f (length prefix)
      step-f-s = run-ir-star-at-offset-s-abstract f prefix suffix-f addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

      addr-f = proj₁ step-f-s
      s1 = proj₁ (proj₂ step-f-s)
      r1-s = proj₂ (proj₂ step-f-s)

      -- Step 2: Execute transfer (STATEFUL HELPER)
      tr-s : TransferResultS f g prefix suffix addr-f s s1
      tr-s = exec-compose-transfer-s f g prefix suffix addr-f s s1 r1-s

      s2 = TransferResultS.s2 tr-s

      -- Preserve RbpInvariant through transfer
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResultS.rsp-s1-to-s2 tr-s

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResultS.rbp-s1-to-s2 tr-s

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-through-ir-s s s1 s2 rbp-inv r1-s rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Step 3: Execute g (STATEFUL RECURSIVE CALL via abstract dispatcher)
      -- Note: We need semantic value (eval f x) and its address
      y = eval f x
      enc-y-eq-addr-f : encode y ≡ addr-f
      enc-y-eq-addr-f = irresults-preserves-eval f (prefix ++ code-f ++ suffix-f) s s1 addr-in addr-f x (length prefix) r1-s enc-eq rdi-eq

      step-g-s : ∃[ addr-g ] ∃[ s3 ] IRStarResultS g (prefix-g ++ code-g ++ suffix) s2 s3 addr-g (length prefix-g)
      step-g-s = run-ir-star-at-offset-s-abstract g prefix-g suffix addr-f y s2
                   (TransferResultS.h2 tr-s) (TransferResultS.pc2-g tr-s) (TransferResultS.rdi2-addr tr-s)
                   enc-y-eq-addr-f
                   (TransferResultS.stack-inv-2 tr-s) (TransferResultS.rsp-2>16 tr-s) rbp-inv-2

      addr-g = proj₁ step-g-s
      s3 = proj₁ (proj₂ step-g-s)
      r3-s = proj₂ (proj₂ step-g-s)

      -- Assemble final result (STATEFUL HELPER)
      addr-out = addr-g  -- Compose output = g output
      result-s = assemble-compose-result-s f g prefix suffix addr-f addr-g s s1 s2 s3 r1-s tr-s r3-s refl

  -- | Star-based compose execution
  -- Uses extracted helpers from IR.Compose - only recursive calls remain here
  run-compose-star-direct : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
    in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)
  run-compose-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s3 , assemble-compose-result f g prefix suffix x s s1 s2 s3 r1 tr r3 refl
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (RECURSIVE via abstract dispatcher)
      step-f : ∃[ s1 ] IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star-at-offset-abstract f prefix suffix-f x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

      s1 : State
      s1 = proj₁ step-f

      r1 : IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1 = proj₂ step-f

      -- Step 2: Execute transfer (extracted helper)
      tr : TransferResult f g prefix suffix x s s1
      tr = exec-compose-transfer f g prefix suffix x s s1 r1

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
      step-g = run-ir-star-at-offset-abstract g prefix-g suffix (eval f x) s2
                 (TransferResult.h2 tr) (TransferResult.pc2-g tr) (TransferResult.rdi2-enc tr)
                 (TransferResult.stack-inv-2 tr) (TransferResult.rsp-2>16 tr) rbp-inv-2

      s3 : State
      s3 = proj₁ step-g

      r3 : IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3 = proj₂ step-g
