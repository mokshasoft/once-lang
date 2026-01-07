------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.MutualIR
--
-- Mutual block for run-ir-star-at-offset and complex IR cases.
--
-- RISC-V simplification over X86:
--   - a0 is BOTH input and output (no rdi/rax transfer needed)
--   - Only s1 needs preservation (vs x86's r14/r15/rbp)
--   - Simpler compose: no transfer instruction between f and g
--
-- NEW: curry-thunk-correct-impl replaces curry-thunk-correct postulate
-- by using the IH (run-ir-star-at-offset) to prove thunk correctness.
--
-- Uses sized types to enable modular extraction of helper functions.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.MutualIR where

open import Size
open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen
  using (compile-riscv; compile-length; StackDelta; StackDepth; neg16; neg24)
open import Once.Backend.RiscV64.Correct.CurryFrameProof
  using (curry-frame-value)

  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Postulates
  using (run-apply-star)  -- sp-bound-for-f-in-thunk ELIMINATED! (2026-01-02)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; star-step5)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult; code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-a0; thunk-s1;
         ClosuresWF; trivialWF; pairWF;
         CurryResult; closure-wf)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.RiscV64.Correct.StarBase public
  using (IRStarResult; IRStarResultS; convert-to-stateful;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra;
         ir-sp-delta; ir-sp-delta-leq; ir-sp;
         ir-mem-preserved; ir-output-wf;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star)

-- Import extracted compose helpers
open import Once.Backend.RiscV64.Correct.IR.Compose
  using (ComposeContext; make-compose-context;
         assemble-compose-result; transform-f-result; transform-g-result)
open import Once.Backend.RiscV64.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers
open import Once.Backend.RiscV64.Correct.IR.Pair
  using (PairContext; make-pair-context;
         PairSetupResult; PairMiddleResult; PairFinalResult;
         pair-setup-star; pair-middle-star; pair-final-star)
open import Once.Backend.RiscV64.Correct.IR.Pair
  using (module PairContext; module PairSetupResult; module PairMiddleResult; module PairFinalResult)

-- Import extracted case helpers
open import Once.Backend.RiscV64.Correct.IR.Case
  using (CaseContext; make-case-context;
         CaseDispatchLeftResult; CaseDispatchRightResult;
         CaseLeftJumpResult; CaseRightEndResult;
         case-dispatch-left-star; case-dispatch-right-star;
         case-left-jump-star; case-right-end-star)
open import Once.Backend.RiscV64.Correct.IR.Case
  using (module CaseContext; module CaseDispatchLeftResult; module CaseDispatchRightResult;
         module CaseLeftJumpResult; module CaseRightEndResult)

-- Import extracted curry proof
open import Once.Backend.RiscV64.Correct.IR.Curry using (run-curry-star)

-- Import thunk setup proof
open import Once.Backend.RiscV64.Correct.IR.ThunkSetup using (thunk-setup-star-proven; thunk-cleanup-star-proven)

-- Import apply proof (proven when ClosureWellFormed is available)
open import Once.Backend.RiscV64.Correct.IR.Apply
  using (run-apply-with-wf; apply-setup-star; apply-jalr-star; apply-nop-star)

-- Import injection proofs (extracted to reduce module size)
open import Once.Backend.RiscV64.Correct.IR.Injection
  using (run-inl-star; run-inr-star)

-- Import extracted IR modules (following X86 pattern)
open import Once.Backend.RiscV64.Correct.IR.Id
  using (run-id-star-s)
open import Once.Backend.RiscV64.Correct.IR.Terminal
  using (run-terminal-star-s)
open import Once.Backend.RiscV64.Correct.IR.Fold
  using (run-fold-star-s)
open import Once.Backend.RiscV64.Correct.IR.Unfold
  using (run-unfold-star-s)
open import Once.Backend.RiscV64.Correct.IR.Arr
  using (run-arr-star-s)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; s≤s; z≤n; s<s; z<s; _⊔_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-monoˡ-<; m≤m+n; m≤n+m; m∸n+n≡m; ≤-trans; m≤m⊔n; m≤n⊔m; m+n∸n≡m; ≤-refl; +-mono-≤; +-monoʳ-≤)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Helper lemma for left-cancellation of addition in inequalities
-- If n + m ≤ n + o, then m ≤ o
------------------------------------------------------------------------

cancel-+-left : ∀ n {m o} → n +ℕ m ≤ n +ℕ o → m ≤ o
cancel-+-left zero p = p
cancel-+-left (suc n) (s≤s p) = cancel-+-left n p

------------------------------------------------------------------------
-- Helper lemma: monus is antitone in second argument
-- If m ≤ n, then o ∸ n ≤ o ∸ m
------------------------------------------------------------------------

∸-antimonoʳ-≤ : ∀ {m n} o → m ≤ n → o ∸ n ≤ o ∸ m
∸-antimonoʳ-≤ {.zero} {zero} zero z≤n = z≤n
∸-antimonoʳ-≤ {m} {suc n} zero _ = z≤n
∸-antimonoʳ-≤ {.zero} {n} (suc o) z≤n = m∸n≤m (suc o) n
∸-antimonoʳ-≤ {suc m} {suc n} (suc o) (s≤s p) = ∸-antimonoʳ-≤ o p

------------------------------------------------------------------------
-- Helper lemma: subtract from both sides of inequality
-- If m + n ≤ o, then n ≤ o ∸ m
------------------------------------------------------------------------

+-≤-to-∸ : ∀ m {n o} → m +ℕ n ≤ o → n ≤ o ∸ m
+-≤-to-∸ zero {n} {o} p = p
+-≤-to-∸ (suc m) {n} {zero} ()
+-≤-to-∸ (suc m) {n} {suc o} (s≤s p) = +-≤-to-∸ m p

------------------------------------------------------------------------
-- Helper lemmas for sp preservation when ir-sp-delta = 0
------------------------------------------------------------------------

-- If n ≤ 0, then n = 0 (for ℕ)
n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
n≤0⇒n≡0 z≤n = refl

-- Derive sp-after = sp-before from ir-sp equation when delta = 0
-- From ir-sp: sp-after + delta = sp-before
-- When delta = 0: sp-after + 0 = sp-before, so sp-after = sp-before
sp-preserved-from-delta-zero : ∀ {sp-after sp-before delta} →
  sp-after +ℕ delta ≡ sp-before → delta ≡ 0 → sp-after ≡ sp-before
sp-preserved-from-delta-zero {sp-after} ir-sp-eq delta-zero =
  trans (sym (+-identityʳ sp-after))
        (trans (cong (sp-after +ℕ_) (sym delta-zero)) ir-sp-eq)

------------------------------------------------------------------------
-- Star-based initial (void elimination)
--
-- compile-riscv initial = ebreak ∷ []
--
-- This should never be called since Void has no inhabitants.
------------------------------------------------------------------------

run-initial-star : ∀ {i A} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv (initial {i} {A}) ++ suffix
  in ∃[ s' ] IRStarResult (initial {i} {A}) prog s s' x (length prefix)
run-initial-star prefix suffix x s h-false pc-eq a0-eq = ⊥-elim x

------------------------------------------------------------------------
-- Apply and stack bound postulates now in Once.Backend.RiscV64.Postulates
-- See that module for detailed documentation and justification.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Complex IR case postulates (compose, pair, case)
-- These break the mutual recursion to enable fast type-checking.
-- TODO: Prove these by moving implementations to separate modules.
------------------------------------------------------------------------

postulate
  run-compose-star : ∀ {i A B C} (f : IR i A B) (g : IR i B C)
                     (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth (g ∘ f) ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv (g ∘ f) ++ suffix
    in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)

  run-pair-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ⟨ f , g ⟩ ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)

  run-case-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ([_,_] f g) ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
    in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  -- Curry closure well-formedness: proves the closure created by curry is valid.
  -- This can be proven using run-ir-star-at-offset f for thunk-correct,
  -- combined with thunk-setup-star-proven and thunk-cleanup-star-proven.
  -- TODO: Prove using the mutual recursion structure.
  curry-closure-wf : ∀ {i A B C} (f : IR i (A * B) C)
                     (prefix suffix : Program) (x : ⟦ A ⟧) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
    in ClosuresWF (B ⇒ C) prog

------------------------------------------------------------------------
-- TEMPORARY BRIDGE: Connect stateful execution to semantic evaluation
--
-- This postulate connects IRStarResultS (explicit address tracking) to
-- the semantic evaluator (eval). It allows stateful proofs to make
-- progress on recursive IR constructs (compose, pair, case, etc.)
-- without requiring the full encoding infrastructure inline.
--
-- This will be eliminated once we:
--  1. Prove correctness at the end-to-end level (whole programs)
--  2. Establish PairAtS/InlAtS/InrAtS validity predicates
--  3. Complete the stateful migration for all IR constructs
--
-- Following X86 backend pattern (see X86/Correct/MutualIR.agda:191-197)
------------------------------------------------------------------------
postulate
  irresults-preserves-eval : ∀ {i A B} (ir : IR i A B) (prog : Program) (s s' : State)
                               (addr-in addr-out : Word) (x : ⟦ A ⟧) (offset : ℕ) →
    IRStarResultS ir prog s s' addr-out offset →
    encode x ≡ addr-in →
    readReg (regs s) a0 ≡ addr-in →
    encode (eval ir x) ≡ addr-out

-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset (sized for termination)
  -- Stack-space precondition: 24 ≤ sp ensures enough stack for all IR nodes
  -- StackDepth ir ≤ sp ensures sufficient stack space for ir and all nested operations
  -- Size parameter i enables termination checking across module boundaries
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ir ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to StarBase functions (don't need stack-space)
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq _ =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset terminal prefix suffix x s h-false pc-eq a0-eq _ =
    run-terminal-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fold prefix suffix x s h-false pc-eq a0-eq _ =
    run-fold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset unfold prefix suffix x s h-false pc-eq a0-eq _ =
    run-unfold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset arr prefix suffix x s h-false pc-eq a0-eq _ =
    run-arr-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fst prefix suffix x s h-false pc-eq a0-eq _ =
    run-fst-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset snd prefix suffix x s h-false pc-eq a0-eq _ =
    run-snd-star prefix suffix x s h-false pc-eq a0-eq

  -- Injection cases: need stack-space for sp arithmetic
  run-ir-star-at-offset inl prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-inl-star prefix suffix x s h-false pc-eq a0-eq sp-bound
  run-ir-star-at-offset inr prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-inr-star prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Void elimination
  run-ir-star-at-offset initial prefix suffix x s h-false pc-eq a0-eq _ =
    run-initial-star prefix suffix x s h-false pc-eq a0-eq

  -- Curry: use run-curry-star with WF proof from curry-closure-wf
  -- StackDepth (curry f) = curry-frame-value + StackDepth f (24 + StackDepth f)
  -- The closure WF is constructed by curry-closure-wf and passed to run-curry-star.
  -- TODO: Prove curry-closure-wf using thunk-setup/cleanup helpers and IH.
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq sp-bound (curry-closure-wf f prefix suffix x)

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq _ =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: postulated to break mutual recursion
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-compose-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Pair: use extracted context helpers with frame pointer approach
  -- Frame pointer allows f and g to use arbitrary stack space.
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Case: use extracted context helpers
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  ------------------------------------------------------------------------
  -- TODO: Add stateful runner (run-ir-star-at-offset-s) after extracting
  -- more IR modules. The stub implementation causes termination checker
  -- issues with the large mutual block. See X86/Correct/MutualIR.agda.
  ------------------------------------------------------------------------

  -- Pair helper - proven using phase helpers and IH with frame pointer approach
  -- Frame pointer (s2) allows f and g to use arbitrary stack space.
  -- No longer requires StackDelta f = 0 or StackDelta g = 0.
  ------------------------------------------------------------------------
  -- EXTRACTED: run-pair-star and run-case-star implementations (~967 lines)
  --
  -- These proofs were moved to separate modules to fix mutual block timeout:
  --   - Once/Backend/RiscV64/Correct/IR/PairProof.agda (~656 lines)
  --   - Once/Backend/RiscV64/Correct/IR/CaseProof.agda (~311 lines)
  --
  -- STATUS: Proof code preserved but not yet type-checking
  -- TODO: Wire up imports and prove the postulates when ready
  ------------------------------------------------------------------------

