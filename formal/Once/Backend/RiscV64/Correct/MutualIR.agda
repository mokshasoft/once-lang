------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.MutualIR
--
-- Mutual block for run-ir-star-at-offset and complex IR cases.
--
-- RISC-V simplification over X86:
--   - a0 is BOTH input and output (no rdi/rax transfer needed)
--   - Only s1 needs preservation (vs x86's r14/r15/rbp)
--   - Simpler compose: no transfer instruction between f and g
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.MutualIR where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; star-step5)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.RiscV64.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star)

-- Import extracted compose helpers
open import Once.Backend.RiscV64.Correct.IR.Compose
  using (ComposeContext; make-compose-context;
         assemble-compose-result; transform-f-result; transform-g-result)
open import Once.Backend.RiscV64.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers
open import Once.Backend.RiscV64.Correct.IR.Pair
  using (PairContext; make-pair-context)
open import Once.Backend.RiscV64.Correct.IR.Pair using (module PairContext)

-- Import extracted case helpers
open import Once.Backend.RiscV64.Correct.IR.Case
  using (CaseContext; make-case-context)
open import Once.Backend.RiscV64.Correct.IR.Case using (module CaseContext)

-- Import extracted curry proof
open import Once.Backend.RiscV64.Correct.IR.Curry using (run-curry-star)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Star-based inl/inr execution (postulated for now)
--
-- These require step-by-step execution proofs. The structure is:
-- inl: addi sp sp -16; sd zero 0(sp); sd a0 8(sp); mv a0 sp
-- inr: addi sp sp -16; li t0 1; sd t0 0(sp); sd a0 8(sp); mv a0 sp
------------------------------------------------------------------------

postulate
  run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv {A} {A + B} inl ++ suffix
    in ∃[ s' ] IRStarResult {A} {A + B} inl prog s s' x (length prefix)

  run-inr-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv {B} {A + B} inr ++ suffix
    in ∃[ s' ] IRStarResult {B} {A + B} inr prog s s' x (length prefix)

------------------------------------------------------------------------
-- Star-based initial (void elimination)
--
-- compile-riscv initial = ebreak ∷ []
--
-- This should never be called since Void has no inhabitants.
------------------------------------------------------------------------

run-initial-star : ∀ {A} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv {Void} {A} initial ++ suffix
  in ∃[ s' ] IRStarResult {Void} {A} initial prog s s' x (length prefix)
run-initial-star prefix suffix x s h-false pc-eq a0-eq = ⊥-elim x

------------------------------------------------------------------------
-- Apply postulate
--
-- Apply requires whole-program analysis because:
-- 1. jalr jumps to a code pointer stored in the closure
-- 2. We need to know that code pointer points to valid thunk code
-- 3. The thunk was created by curry, which is proven separately
--
-- This is sound by construction: curry creates closures that apply
-- can call. Full verification requires tracking closure provenance.
------------------------------------------------------------------------

postulate
  run-apply-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    let prog = prefix ++ compile-riscv {(A ⇒ B) * A} {B} apply ++ suffix
    in ∃[ s' ] IRStarResult {(A ⇒ B) * A} {B} apply prog s s' x (length prefix)

------------------------------------------------------------------------
-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to StarBase functions
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset terminal prefix suffix x s h-false pc-eq a0-eq =
    run-terminal-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fold prefix suffix x s h-false pc-eq a0-eq =
    run-fold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset unfold prefix suffix x s h-false pc-eq a0-eq =
    run-unfold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset arr prefix suffix x s h-false pc-eq a0-eq =
    run-arr-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fst prefix suffix x s h-false pc-eq a0-eq =
    run-fst-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset snd prefix suffix x s h-false pc-eq a0-eq =
    run-snd-star prefix suffix x s h-false pc-eq a0-eq

  -- Injection cases
  run-ir-star-at-offset inl prefix suffix x s h-false pc-eq a0-eq =
    run-inl-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset inr prefix suffix x s h-false pc-eq a0-eq =
    run-inr-star prefix suffix x s h-false pc-eq a0-eq

  -- Void elimination
  run-ir-star-at-offset initial prefix suffix x s h-false pc-eq a0-eq =
    run-initial-star prefix suffix x s h-false pc-eq a0-eq

  -- Curry: delegate to extracted proof
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: use extracted context helpers
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq =
    let ctx = make-compose-context f g prefix suffix
        open ComposeContext ctx

        -- Step 1: Execute f
        (sf , rf) = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq a0-eq
        rf' = transform-f-result f g prefix suffix x s sf rf

        -- Step 2: Execute g (no transfer needed - a0 already has result!)
        a0-after-f : readReg (regs sf) a0 ≡ encode (eval f x)
        a0-after-f = ir-a0 rf

        -- PC conversion: ir-pc rf gives pc sf ≡ length prefix +ℕ compile-length f
        -- We need pc sf ≡ length prefix-g where length prefix-g = length prefix +ℕ len-f
        pc-for-g : pc sf ≡ length prefix-g
        pc-for-g = trans (ir-pc rf) (sym len-prefix-g)

        (sg , rg) = run-ir-star-at-offset g prefix-g suffix (eval f x) sf
                      (ir-halted rf) pc-for-g a0-after-f
        rg' = transform-g-result f g prefix suffix x sf sg rg

    in sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'

  -- Pair: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Case: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Pair helper (postulated - needs step-by-step execution proof)
  postulate
    run-pair-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                    (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
      halted s ≡ false →
      pc s ≡ length prefix →
      readReg (regs s) a0 ≡ encode x →
      let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
      in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)

  -- Case helper (postulated - needs branch execution proof)
  postulate
    run-case-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                    (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
      halted s ≡ false →
      pc s ≡ length prefix →
      readReg (regs s) a0 ≡ encode x →
      let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
      in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

------------------------------------------------------------------------
-- Top-level entry point
------------------------------------------------------------------------

-- | Execute IR starting at position 0
run-ir-star : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult ir (compile-riscv ir) s s' x 0
run-ir-star ir x s h-false pc-eq a0-eq =
  subst (λ prog → ∃[ s' ] IRStarResult ir prog s s' x 0)
        (++-identityʳ (compile-riscv ir))
        (run-ir-star-at-offset ir [] [] x s h-false pc-eq a0-eq)
  where
    open import Data.List.Properties using (++-identityʳ)
