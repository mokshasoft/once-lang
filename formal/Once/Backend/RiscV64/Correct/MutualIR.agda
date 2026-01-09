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
  using (compile-riscv; compile-length; StackDelta; StackDepth; neg16; neg24;
         thunk-entry-offset; curry-overhead; thunk-body-offset;
         auipc-thunk-offset; curry-jump-offset; curry-end-label-base)
open import Once.Backend.RiscV64.Correct.CurryFrameProof
  using (curry-frame-value)

open import Once.Backend.RiscV64.Postulates
  using (run-apply-star; run-prim-star)  -- sp-bound-for-f-in-thunk ELIMINATED! (2026-01-02)

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
         run-arr-star; run-fst-star; run-snd-star;
         run-fst-star-v; run-snd-star-v)

-- Import memory validity predicates
open import Once.Backend.RiscV64.Correct.MemoryValid
  using (PairAt; pair-at; fst-valid; snd-valid; InlAt; InrAt)

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

  -- NOTE: curry-closure-wf moved into the mutual block below
  -- It can now call run-ir-star-at-offset f to prove thunk-correct

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

------------------------------------------------------------------------
-- Lemma: thunk offset (|prefix| + 7) is within program bounds
-- prog = prefix ++ compile-riscv (curry f) ++ suffix
-- compile-length (curry f) = curry-overhead + compile-length f = 19 + compile-length f ≥ 19
-- So |prefix| + 7 < |prefix| + 19 ≤ |prefix ++ compile-riscv (curry f) ++ suffix|
------------------------------------------------------------------------
thunk-offset-in-bounds : ∀ {i A B C} (f : IR i (A * B) C) (prefix suffix : Program) →
  length prefix +ℕ thunk-entry-offset < length (prefix ++ compile-riscv (curry f) ++ suffix)
thunk-offset-in-bounds {i} {A} {B} {C} f prefix suffix = goal
  where
    open import Data.List.Properties as LP using (length-++)
    open import Data.Nat.Properties using (+-monoʳ-<; m≤m+n; <-≤-trans)

    -- Length of compile-riscv (curry f) is curry-overhead + compile-length f = 19 + compile-length f
    curry-len : length (compile-riscv (curry f)) ≡ curry-overhead +ℕ compile-length f
    curry-len = compile-length-correct (curry f)

    -- curry-overhead = 19 (defined in CodeGen)
    curry-overhead-eq : curry-overhead ≡ 19
    curry-overhead-eq = refl

    -- Length of full program
    prog-len : length (prefix ++ compile-riscv (curry f) ++ suffix)
             ≡ length prefix +ℕ length (compile-riscv (curry f) ++ suffix)
    prog-len = LP.length-++ prefix

    inner-len : length (compile-riscv (curry f) ++ suffix)
              ≡ length (compile-riscv (curry f)) +ℕ length suffix
    inner-len = LP.length-++ (compile-riscv (curry f))

    -- thunk-entry-offset = 7 < 19 = curry-overhead (obviously)
    -- 7 < 19 means suc 7 ≤ 19, i.e., 8 ≤ 19
    7<19 : thunk-entry-offset < curry-overhead
    7<19 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

    -- 7 < 19 + compile-length f (using: 7 < 19 and 19 ≤ 19 + compile-length f)
    7<19+f : thunk-entry-offset < curry-overhead +ℕ compile-length f
    7<19+f = <-≤-trans 7<19 (m≤m+n curry-overhead (compile-length f))

    -- 7 < 19 + compile-length f + length suffix
    7<19+f+s : thunk-entry-offset < curry-overhead +ℕ compile-length f +ℕ length suffix
    7<19+f+s = <-≤-trans 7<19+f (m≤m+n (curry-overhead +ℕ compile-length f) (length suffix))

    -- |prefix| + 7 < |prefix| + (19 + compile-length f + length suffix)
    step1 : length prefix +ℕ thunk-entry-offset < length prefix +ℕ (curry-overhead +ℕ compile-length f +ℕ length suffix)
    step1 = +-monoʳ-< (length prefix) 7<19+f+s

    -- Rewrite using curry-len and inner-len
    step2 : length prefix +ℕ (curry-overhead +ℕ compile-length f +ℕ length suffix)
          ≡ length prefix +ℕ (length (compile-riscv (curry f)) +ℕ length suffix)
    step2 = cong (length prefix +ℕ_) (cong (_+ℕ length suffix) (sym curry-len))

    step3 : length prefix +ℕ (length (compile-riscv (curry f)) +ℕ length suffix)
          ≡ length prefix +ℕ length (compile-riscv (curry f) ++ suffix)
    step3 = cong (length prefix +ℕ_) (sym inner-len)

    step4 : length prefix +ℕ length (compile-riscv (curry f) ++ suffix)
          ≡ length (prefix ++ compile-riscv (curry f) ++ suffix)
    step4 = sym prog-len

    goal : length prefix +ℕ thunk-entry-offset < length (prefix ++ compile-riscv (curry f) ++ suffix)
    goal = subst (length prefix +ℕ thunk-entry-offset <_) (trans step2 (trans step3 step4)) step1

------------------------------------------------------------------------
-- InputValid: Memory validity predicate for input values
--
-- Captures what validity proof is needed for each input type:
-- - Pairs need PairAt (for fst/snd to read from memory)
-- - Sums need InlAt/InrAt (for case to read the tag)
-- - Other types don't read from memory, so trivially valid (⊤)
------------------------------------------------------------------------

-- | InputValid A x m: memory m has valid encoding for value x of type A
-- Only pairs and sums need actual validity proofs; other types trivially valid.
InputValid : (A : Type) → ⟦ A ⟧ → Memory → Set
InputValid (A * B) x m = PairAt (proj₁ x) (proj₂ x) (encode x) m
InputValid (A + B) (inj₁ a) m = InlAt {A} {B} a (encode {A + B} (inj₁ a)) m
InputValid (A + B) (inj₂ b) m = InrAt {A} {B} b (encode {A + B} (inj₂ b)) m
InputValid Void () _  -- Void has no inhabitants (absurd pattern)
InputValid _ _ _ = ⊤  -- All other types: trivially valid

-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset (sized for termination)
  -- Stack-space precondition: 24 ≤ sp ensures enough stack for all IR nodes
  -- StackDepth ir ≤ sp ensures sufficient stack space for ir and all nested operations
  -- InputValid A x (memory s) ensures memory validity for fst/snd/case operations
  -- Size parameter i enables termination checking across module boundaries
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ir ≤ readReg (regs s) sp →
    InputValid A x (memory s) →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to StarBase functions (don't need stack-space or validity)
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset terminal prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-terminal-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fold prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-fold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset unfold prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-unfold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset arr prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-arr-star prefix suffix x s h-false pc-eq a0-eq

  -- fst/snd: use validity-based versions (eliminates encode-pair-fst/snd postulates!)
  run-ir-star-at-offset fst prefix suffix x s h-false pc-eq a0-eq _ pair-valid =
    run-fst-star-v prefix suffix (proj₁ x) (proj₂ x) s h-false pc-eq a0-eq pair-valid
  run-ir-star-at-offset snd prefix suffix x s h-false pc-eq a0-eq _ pair-valid =
    run-snd-star-v prefix suffix (proj₁ x) (proj₂ x) s h-false pc-eq a0-eq pair-valid

  -- Injection cases: need stack-space for sp arithmetic
  run-ir-star-at-offset inl prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-inl-star prefix suffix x s h-false pc-eq a0-eq sp-bound
  run-ir-star-at-offset inr prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-inr-star prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Void elimination
  run-ir-star-at-offset initial prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-initial-star prefix suffix x s h-false pc-eq a0-eq

  -- Curry: use run-curry-star with WF proof from curry-closure-wf
  -- StackDepth (curry f) = curry-frame-value + StackDepth f (24 + StackDepth f)
  -- The closure WF is constructed by curry-closure-wf and passed to run-curry-star.
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq sp-bound (curry-closure-wf f prefix suffix x)

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Prim: opaque primitive - correctness postulated until proper Prim compilation
  run-ir-star-at-offset (Prim {A} {B} name) prefix suffix x s h-false pc-eq a0-eq _ _ =
    run-prim-star name prefix suffix x s h-false pc-eq a0-eq

  -- Compose: postulated to break mutual recursion
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-compose-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Pair: use extracted context helpers with frame pointer approach
  -- Frame pointer allows f and g to use arbitrary stack space.
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Case: use extracted context helpers
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq sp-bound _ =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  ------------------------------------------------------------------------
  -- Curry closure well-formedness: proven inside mutual block
  --
  -- This proves that closures created by curry are well-formed by using:
  --   1. thunk-setup-star-proven: setup the pair (env, arg)
  --   2. run-ir-star-at-offset f: execute f on the pair (mutual recursion!)
  --   3. thunk-cleanup-star-proven: cleanup and prepare for ret
  --   4. ret instruction: return to caller
  ------------------------------------------------------------------------
  curry-closure-wf : ∀ {i A B C} (f : IR i (A * B) C)
                     (prefix suffix : Program) (x : ⟦ A ⟧) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
    in ClosuresWF (B ⇒ C) prog
  curry-closure-wf {i} {A} {B} {C} f prefix suffix x =
    clos-code-ptr , clos-env-addr , clos-sem , clos-stack-req , record
      { code-ptr-valid = clos-code-ptr-valid-proof
      ; thunk-correct = thunk-correct-proof
      }
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      offset = length prefix

      -- Concrete values for the closure
      clos-code-ptr : ℕ
      clos-code-ptr = offset +ℕ thunk-entry-offset  -- thunk starts at position 7

      clos-env-addr : ℕ
      clos-env-addr = encode x  -- captured environment

      clos-sem : ⟦ B ⟧ → ⟦ C ⟧
      clos-sem = λ b → eval f (x , b)  -- partial application semantics

      clos-stack-req : ℕ
      clos-stack-req = StackDepth (curry f)

      -- Proof 1: clos-code-ptr is within program bounds
      -- clos-code-ptr = offset + 7, and prog has at least offset + curry-overhead + len-f instructions
      clos-code-ptr-valid-proof : clos-code-ptr < length prog
      clos-code-ptr-valid-proof = thunk-offset-in-bounds f prefix suffix

      -- Proof 2: thunk executes correctly for any input
      -- This uses run-ir-star-at-offset f (mutual recursion!)
      thunk-correct-proof : ∀ (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
        halted s ≡ false →
        pc s ≡ clos-code-ptr →
        readReg (regs s) a0 ≡ encode arg →
        readReg (regs s) s0 ≡ clos-env-addr →
        readReg (regs s) ra ≡ ret-addr →
        clos-stack-req ≤ readReg (regs s) sp →
        ∃[ s' ] (ThunkResult prog s s' clos-sem arg × pc s' ≡ ret-addr)
      thunk-correct-proof arg s ret-addr h-false pc-eq a0-eq s0-eq ra-eq sp-bound =
        s-final , thunk-result , pc-final
        where
          -- Phase 1: Thunk setup (positions 7-13)
          -- Entry: pc=clos-code-ptr, a0=encode arg, s0=encode x
          -- Exit: pc=14+offset, a0=encode (x, arg), s2=frame pointer
          setup-result = thunk-setup-star-proven f prefix suffix x arg s
                           h-false pc-eq a0-eq s0-eq
          st1 = proj₁ setup-result
          star1 = proj₁ (proj₂ setup-result)
          h1 = proj₁ (proj₂ (proj₂ setup-result))
          pc1-eq = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
          a0-after-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
          s1-after-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
          ra-after-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
          s2-after-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
          sp-after-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
          rest-after-sp = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
          mem-s2-saved = proj₁ rest-after-sp
          -- Pair memory layout from thunk setup (for InputValid):
          mem-pair-fst = proj₁ (proj₂ rest-after-sp)  -- readMem st1 new-sp ≡ just (encode x)
          mem-pair-snd = proj₂ (proj₂ rest-after-sp)  -- readMem st1 (new-sp+8) ≡ just (encode arg)

          -- Phase 2: Execute f (positions 14 to 14+len-f)
          -- Program decomposition: prog = prefix-f ++ compile-riscv f ++ suffix-f
          -- where prefix-f = prefix ++ closure-setup ++ thunk-setup (14 instructions)
          --       suffix-f = thunk-tail ++ suffix (5 instructions)

          len-f = compile-length f

          -- Define the curry code structure (same as in CodeGen)
          code-ptr-offset = thunk-entry-offset
          auipc-offset = auipc-thunk-offset
          end-offset = + (curry-jump-offset +ℕ len-f)

          curry-closure-setup : Program
          curry-closure-setup =
            addi sp sp neg16 ∷
            sd a0 fstOffset sp ∷
            auipc t0 (+ 0) ∷
            addi t0 t0 (+ auipc-offset) ∷
            sd t0 sndOffset sp ∷
            mv a0 sp ∷
            j end-offset ∷ []

          curry-thunk-setup : Program
          curry-thunk-setup =
            label code-ptr-offset ∷
            addi sp sp neg24 ∷
            sd s2 (+ 16) sp ∷
            mv s2 sp ∷
            sd s0 fstOffset sp ∷
            sd a0 sndOffset sp ∷
            mv a0 sp ∷ []

          curry-thunk-tail : Program
          curry-thunk-tail =
            mv sp s2 ∷
            ld s2 (+ 16) sp ∷
            addi sp sp (+ 24) ∷
            ret ∷
            label (curry-end-label-base +ℕ len-f) ∷ []

          prefix-f : Program
          prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup

          suffix-f : Program
          suffix-f = curry-thunk-tail ++ suffix

          -- Program equality proof: prog = prefix-f ++ compile-riscv f ++ suffix-f
          -- This requires showing compile-riscv (curry f) = closure-setup ++ thunk-setup ++ f ++ tail
          open import Data.List.Properties as LP using (length-++; ++-assoc)
          open import Data.Nat.Properties using (+-assoc; +-comm; m+n∸n≡m; ∸-+-assoc;
                                                  ≤-trans; +-monoˡ-≤; m∸n≤m)

          -- The curry structure equality (definitional)
          curry-structure : compile-riscv (curry f) ≡
                            curry-closure-setup ++ curry-thunk-setup ++ compile-riscv f ++ curry-thunk-tail
          curry-structure = refl

          -- Program equality using curry-structure and list reassociation
          prog-eq-f : prog ≡ prefix-f ++ compile-riscv f ++ suffix-f
          prog-eq-f = trans (cong (λ c → prefix ++ c ++ suffix) curry-structure) prog-reassoc
            where
              ccs = curry-closure-setup
              cts = curry-thunk-setup
              code-f = compile-riscv f
              ctt = curry-thunk-tail

              -- Goal: prefix ++ (ccs ++ cts ++ code-f ++ ctt) ++ suffix ≡ (prefix ++ ccs ++ cts) ++ code-f ++ (ctt ++ suffix)
              prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ ctt) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
              prog-reassoc =
                let inner-assoc1 : ccs ++ (cts ++ (code-f ++ ctt)) ≡ (ccs ++ cts) ++ (code-f ++ ctt)
                    inner-assoc1 = sym (++-assoc ccs cts (code-f ++ ctt))

                    inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ ctt)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ ctt) ++ suffix)
                    inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ ctt) suffix

                    inner-assoc3 : (code-f ++ ctt) ++ suffix ≡ code-f ++ (ctt ++ suffix)
                    inner-assoc3 = ++-assoc code-f ctt suffix

                    inner-combined : (ccs ++ (cts ++ (code-f ++ ctt))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (ctt ++ suffix))
                    inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                     (trans inner-assoc2
                                            (cong ((ccs ++ cts) ++_) inner-assoc3))

                    outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ ctt))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (ctt ++ suffix)))
                    outer-step = cong (prefix ++_) inner-combined

                    final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (ctt ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (ctt ++ suffix))
                    final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (ctt ++ suffix)))

                in trans outer-step final-assoc

          -- Length of prefix-f = length prefix + 14 (thunk-body-offset)
          len-prefix-f : length prefix-f ≡ length prefix +ℕ thunk-body-offset
          len-prefix-f = trans (LP.length-++ prefix {curry-closure-setup ++ curry-thunk-setup})
                               (cong (length prefix +ℕ_) (LP.length-++ curry-closure-setup {curry-thunk-setup}))

          -- Stack bound for f after setup
          -- StackDepth (curry f) = curry-frame + StackDepth f = 24 + StackDepth f
          -- After setup: sp = original_sp - 24
          -- Precondition: StackDepth (curry f) ≤ original_sp
          -- i.e., 24 + StackDepth f ≤ original_sp
          -- Need: StackDepth f ≤ original_sp - 24
          sp-bound-f : StackDepth f ≤ readReg (regs st1) sp
          sp-bound-f = subst (StackDepth f ≤_) (sym sp-after-setup) f≤sp-24
            where
              open import Data.Nat.Properties using (m+n≤o⇒m≤o∸n)

              orig-sp = readReg (regs s) sp

              -- curry-frame = 24 = curry-frame-value (by definition of StackDepth)
              -- StackDepth (curry f) = curry-frame-value + StackDepth f = 24 + StackDepth f
              curry-frame-eq : StackDepth (curry f) ≡ 24 +ℕ StackDepth f
              curry-frame-eq = refl

              -- From sp-bound: 24 + StackDepth f ≤ orig-sp
              24+f≤sp : 24 +ℕ StackDepth f ≤ orig-sp
              24+f≤sp = subst (_≤ orig-sp) curry-frame-eq sp-bound

              -- Rewrite to StackDepth f + 24 ≤ orig-sp
              f+24≤sp : StackDepth f +ℕ 24 ≤ orig-sp
              f+24≤sp = subst (_≤ orig-sp) (+-comm 24 (StackDepth f)) 24+f≤sp

              -- StackDepth f ≤ orig-sp - 24 using m+n≤o⇒m≤o∸n
              -- m+n≤o⇒m≤o∸n : ∀ m {n o} → m + n ≤ o → m ≤ o ∸ n
              f≤sp-24 : StackDepth f ≤ orig-sp ∸ 24
              f≤sp-24 = m+n≤o⇒m≤o∸n (StackDepth f) f+24≤sp

          -- Call IH: run-ir-star-at-offset f
          pc-for-f : pc st1 ≡ length prefix-f
          pc-for-f = trans pc1-eq (sym len-prefix-f)

          -- Construct InputValid (PairAt) proof for the pair (x, arg)
          -- The thunk setup allocated this pair at new-sp, so:
          --   new-sp = encode (x, arg)
          --   memory[new-sp] = encode x
          --   memory[new-sp + 8] = encode arg
          new-sp : Word
          new-sp = readReg (regs s) sp ∸ 24

          -- Derive: new-sp ≡ encode (x, arg)
          pair-addr-eq : new-sp ≡ encode (x , arg)
          pair-addr-eq = encode-pair-construct x arg new-sp (memory st1) mem-pair-fst mem-pair-snd

          -- Construct PairAt by substituting the address equality
          pair-valid : PairAt x arg (encode (x , arg)) (memory st1)
          pair-valid = pair-at
            (subst (λ addr → readMem (memory st1) addr ≡ just (encode x)) pair-addr-eq mem-pair-fst)
            (subst (λ addr → readMem (memory st1) (addr +ℕ 8) ≡ just (encode arg)) pair-addr-eq mem-pair-snd)

          f-result = run-ir-star-at-offset f prefix-f suffix-f (x , arg) st1
                       h1 pc-for-f a0-after-setup sp-bound-f pair-valid
          st2 = proj₁ f-result
          ir-f = proj₂ f-result
          star2-raw : Star (prefix-f ++ compile-riscv f ++ suffix-f) st1 st2
          star2-raw = ir-star ir-f
          star2 : Star prog st1 st2
          star2 = subst (λ p → Star p st1 st2) (sym prog-eq-f) star2-raw

          h2 : halted st2 ≡ false
          h2 = ir-halted ir-f

          pc2-raw : pc st2 ≡ length prefix-f +ℕ compile-length f
          pc2-raw = ir-pc ir-f

          a0-after-f : readReg (regs st2) a0 ≡ encode (eval f (x , arg))
          a0-after-f = ir-a0 ir-f

          s1-after-f : readReg (regs st2) s1 ≡ readReg (regs st1) s1
          s1-after-f = ir-s1 ir-f

          -- Phase 3: Cleanup (positions 14+len-f to 17+len-f)
          -- Use thunk-cleanup-star-proven
          cleanup-pc : pc st2 ≡ length prefix +ℕ thunk-body-offset +ℕ compile-length f
          cleanup-pc = trans pc2-raw (cong (_+ℕ compile-length f) len-prefix-f)

          -- Memory at s2+16 preserved through f execution
          -- Chain: st2.s2 = st1.s2 = st1.sp, and ir-mem-preserved preserves at st1.sp + 16
          s2-after-f : readReg (regs st2) s2 ≡ readReg (regs st1) s2
          s2-after-f = ir-s2 ir-f

          -- st1.s2 = st1.sp (both = orig-sp - 24)
          s2-eq-sp : readReg (regs st1) s2 ≡ readReg (regs st1) sp
          s2-eq-sp = trans s2-after-setup (sym sp-after-setup)

          -- Memory address: st2.s2 + 16 = st1.sp + 16
          addr-eq : readReg (regs st2) s2 +ℕ 16 ≡ readReg (regs st1) sp +ℕ 16
          addr-eq = cong (_+ℕ 16) (trans s2-after-f s2-eq-sp)

          -- Memory preserved by f at st1.sp + 16
          mem-f-preserved : readMem (memory st2) (readReg (regs st1) sp +ℕ 16) ≡
                            readMem (memory st1) (readReg (regs st1) sp +ℕ 16)
          mem-f-preserved = ir-mem-preserved ir-f 16

          -- st1.sp + 16 = orig-sp - 24 + 16 = orig-sp - 8
          -- mem-s2-saved gives memory at orig-sp - 24 + 16
          addr-eq-orig : readReg (regs st1) sp +ℕ 16 ≡ readReg (regs s) sp ∸ 24 +ℕ 16
          addr-eq-orig = cong (_+ℕ 16) sp-after-setup

          mem-s2-preserved : readMem (memory st2) (readReg (regs st2) s2 +ℕ 16) ≡
                             just (readReg (regs s) s2)
          mem-s2-preserved = begin
            readMem (memory st2) (readReg (regs st2) s2 +ℕ 16)
              ≡⟨ cong (readMem (memory st2)) addr-eq ⟩
            readMem (memory st2) (readReg (regs st1) sp +ℕ 16)
              ≡⟨ mem-f-preserved ⟩
            readMem (memory st1) (readReg (regs st1) sp +ℕ 16)
              ≡⟨ cong (readMem (memory st1)) addr-eq-orig ⟩
            readMem (memory st1) (readReg (regs s) sp ∸ 24 +ℕ 16)
              ≡⟨ mem-s2-saved ⟩
            just (readReg (regs s) s2) ∎
            where open ≡-Reasoning

          cleanup-result = thunk-cleanup-star-proven f prefix suffix (readReg (regs s) s2) st2
                             h2 cleanup-pc mem-s2-preserved
          st3 = proj₁ cleanup-result
          star3 = proj₁ (proj₂ cleanup-result)
          h3 = proj₁ (proj₂ (proj₂ cleanup-result))
          pc3-eq = proj₁ (proj₂ (proj₂ (proj₂ cleanup-result)))
          a0-after-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))
          s1-after-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result)))))
          ra-after-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))))
          s2-after-cleanup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))))

          -- Phase 4: Execute ret instruction
          -- pc is at ret-offset, ra contains ret-addr
          -- ret-offset = length prefix + (thunk-body-offset + 3) + len-f
          ret-offset-calc : ℕ
          ret-offset-calc = length prefix +ℕ (thunk-body-offset +ℕ 3) +ℕ len-f

          -- State after ret
          st4-def : State
          st4-def = record st3 { pc = readReg (regs st3) ra }

          -- ra contains ret-addr (preserved through cleanup)
          ra-is-ret : readReg (regs st3) ra ≡ ret-addr
          ra-is-ret = trans ra-after-cleanup
                      (trans (ir-ra ir-f)
                      (trans ra-after-setup ra-eq))

          -- pc st3 = ret-offset
          -- pc3-eq : pc st3 ≡ length prefix +ℕ (thunk-body-offset +ℕ 3) +ℕ compile-length f

          -- Need to show ret is at position ret-offset in prog
          -- prog = prefix ++ compile-riscv (curry f) ++ suffix
          -- compile-riscv (curry f) has ret at position thunk-body-offset + 3 + len-f = 17 + len-f
          -- So ret is at position length prefix + 17 + len-f = ret-offset in prog

          -- The prefix for step-ret-at-offset needs to be everything before ret
          ret-prefix : Program
          ret-prefix = prefix ++ curry-closure-setup ++ curry-thunk-setup ++ compile-riscv f ++
                       (mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ [])

          ret-suffix : Program
          ret-suffix = label (curry-end-label-base +ℕ len-f) ∷ suffix

          -- Show that prog = ret-prefix ++ ret ∷ ret-suffix
          -- curry-thunk-tail = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (curry-end-label-base +ℕ len-f) ∷ []
          -- ret-prefix has the first 3 of curry-thunk-tail, ret-suffix has the label ∷ suffix
          prog-eq-ret : prog ≡ ret-prefix ++ ret ∷ ret-suffix
          prog-eq-ret = trans (cong (λ c → prefix ++ c ++ suffix) curry-structure)
                              (prog-ret-reassoc)
            where
              ccs = curry-closure-setup
              cts = curry-thunk-setup
              code-f = compile-riscv f
              cleanup3 = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ []
              lbl = label (curry-end-label-base +ℕ len-f) ∷ []

              -- curry-thunk-tail = cleanup3 ++ ret ∷ lbl
              tail-split : curry-thunk-tail ≡ cleanup3 ++ ret ∷ lbl
              tail-split = refl

              -- Need: prefix ++ (ccs ++ cts ++ code-f ++ (cleanup3 ++ ret ∷ lbl)) ++ suffix
              --     = (prefix ++ ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ (lbl ++ suffix)
              prog-ret-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ curry-thunk-tail) ++ suffix ≡ ret-prefix ++ ret ∷ ret-suffix
              prog-ret-reassoc =
                let -- First, expand curry-thunk-tail
                    step1 : prefix ++ (ccs ++ cts ++ code-f ++ curry-thunk-tail) ++ suffix ≡
                            prefix ++ (ccs ++ cts ++ code-f ++ (cleanup3 ++ ret ∷ lbl)) ++ suffix
                    step1 = cong (λ t → prefix ++ (ccs ++ cts ++ code-f ++ t) ++ suffix) tail-split

                    -- Reassociate: code-f ++ (cleanup3 ++ ret ∷ lbl) = (code-f ++ cleanup3) ++ ret ∷ lbl
                    inner1 : code-f ++ (cleanup3 ++ ret ∷ lbl) ≡ (code-f ++ cleanup3) ++ ret ∷ lbl
                    inner1 = sym (++-assoc code-f cleanup3 (ret ∷ lbl))

                    -- Reassociate: cts ++ ((code-f ++ cleanup3) ++ ret ∷ lbl) = (cts ++ code-f ++ cleanup3) ++ ret ∷ lbl
                    inner2 : cts ++ ((code-f ++ cleanup3) ++ ret ∷ lbl) ≡ (cts ++ code-f ++ cleanup3) ++ ret ∷ lbl
                    inner2 = trans (sym (++-assoc cts (code-f ++ cleanup3) (ret ∷ lbl)))
                                   (cong (_++ ret ∷ lbl) (sym (++-assoc cts code-f cleanup3)))

                    -- Reassociate: ccs ++ ((cts ++ code-f ++ cleanup3) ++ ret ∷ lbl) = (ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ lbl
                    inner3 : ccs ++ ((cts ++ code-f ++ cleanup3) ++ ret ∷ lbl) ≡ (ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ lbl
                    inner3 = trans (sym (++-assoc ccs (cts ++ code-f ++ cleanup3) (ret ∷ lbl)))
                                   (cong (_++ ret ∷ lbl) (sym (++-assoc ccs cts (code-f ++ cleanup3))))

                    -- Combine inner steps
                    inner-all : ccs ++ cts ++ code-f ++ (cleanup3 ++ ret ∷ lbl) ≡ (ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ lbl
                    inner-all = trans (cong (ccs ++_) (cong (cts ++_) inner1))
                                (trans (cong (ccs ++_) inner2)
                                       inner3)

                    -- Now handle the suffix
                    -- (X ++ ret ∷ lbl) ++ suffix = X ++ ret ∷ (lbl ++ suffix)
                    suffix-reassoc : ∀ X → (X ++ ret ∷ lbl) ++ suffix ≡ X ++ ret ∷ (lbl ++ suffix)
                    suffix-reassoc X = ++-assoc X (ret ∷ lbl) suffix

                    -- prefix ++ (inner) ++ suffix
                    step2 : prefix ++ (ccs ++ cts ++ code-f ++ (cleanup3 ++ ret ∷ lbl)) ++ suffix ≡
                            prefix ++ ((ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ lbl) ++ suffix
                    step2 = cong (λ i → prefix ++ i ++ suffix) inner-all

                    step3 : prefix ++ ((ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ lbl) ++ suffix ≡
                            prefix ++ ((ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ (lbl ++ suffix))
                    step3 = cong (prefix ++_) (suffix-reassoc (ccs ++ cts ++ code-f ++ cleanup3))

                    -- Finally: prefix ++ (Y ++ ret ∷ Z) = (prefix ++ Y) ++ ret ∷ Z
                    step4 : prefix ++ ((ccs ++ cts ++ code-f ++ cleanup3) ++ ret ∷ (lbl ++ suffix)) ≡
                            (prefix ++ (ccs ++ cts ++ code-f ++ cleanup3)) ++ ret ∷ (lbl ++ suffix)
                    step4 = sym (++-assoc prefix (ccs ++ cts ++ code-f ++ cleanup3) (ret ∷ (lbl ++ suffix)))

                in trans step1 (trans step2 (trans step3 step4))

          -- Length of ret-prefix = ret-offset-calc
          -- ret-prefix = prefix ++ ccs ++ cts ++ compile-riscv f ++ cleanup3 where cleanup3 has 3 elements
          -- length = |prefix| + 7 + 7 + |f| + 3 = |prefix| + 17 + |f|
          -- ret-offset-calc = |prefix| + (thunk-body-offset + 3) + len-f = |prefix| + 17 + len-f
          len-ret-prefix : length ret-prefix ≡ ret-offset-calc
          len-ret-prefix = len-calc
            where
              -- Compute lengths step by step
              len-ccs : length curry-closure-setup ≡ 7
              len-ccs = refl

              len-cts : length curry-thunk-setup ≡ 7
              len-cts = refl

              cleanup3 = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ []
              len-cleanup3 : length cleanup3 ≡ 3
              len-cleanup3 = refl

              len-f-code : length (compile-riscv f) ≡ len-f
              len-f-code = compile-length-correct f

              -- Total: |prefix| + 7 + 7 + |f| + 3 = |prefix| + (14 + 3) + |f| = |prefix| + 17 + |f|
              -- = |prefix| + (thunk-body-offset + 3) + len-f
              len-calc : length ret-prefix ≡ ret-offset-calc
              len-calc =
                begin
                  length ret-prefix
                ≡⟨ LP.length-++ prefix {curry-closure-setup ++ curry-thunk-setup ++ compile-riscv f ++ cleanup3} ⟩
                  length prefix +ℕ length (curry-closure-setup ++ curry-thunk-setup ++ compile-riscv f ++ cleanup3)
                ≡⟨ cong (λ n → length prefix +ℕ n) (LP.length-++ curry-closure-setup {curry-thunk-setup ++ compile-riscv f ++ cleanup3}) ⟩
                  length prefix +ℕ (7 +ℕ length (curry-thunk-setup ++ compile-riscv f ++ cleanup3))
                ≡⟨ cong (λ n → length prefix +ℕ n) (cong (λ n → 7 +ℕ n) (LP.length-++ curry-thunk-setup {compile-riscv f ++ cleanup3})) ⟩
                  length prefix +ℕ (7 +ℕ (7 +ℕ length (compile-riscv f ++ cleanup3)))
                ≡⟨ cong (λ n → length prefix +ℕ n) (cong (λ n → 7 +ℕ n) (cong (λ n → 7 +ℕ n) (LP.length-++ (compile-riscv f) {cleanup3}))) ⟩
                  length prefix +ℕ (7 +ℕ (7 +ℕ (length (compile-riscv f) +ℕ 3)))
                ≡⟨ cong (λ n → length prefix +ℕ n) (cong (λ n → 7 +ℕ n) (cong (λ n → 7 +ℕ n) (cong (λ n → n +ℕ 3) len-f-code))) ⟩
                  length prefix +ℕ (7 +ℕ (7 +ℕ (len-f +ℕ 3)))
                ≡⟨ cong (λ n → length prefix +ℕ n) arith-eq ⟩
                  length prefix +ℕ (17 +ℕ len-f)
                ≡⟨ sym (+-assoc (length prefix) 17 len-f) ⟩
                  (length prefix +ℕ 17) +ℕ len-f
                ∎
                where
                  open ≡-Reasoning
                  -- 7 + (7 + (len-f + 3)) = 17 + len-f
                  arith-eq : 7 +ℕ (7 +ℕ (len-f +ℕ 3)) ≡ 17 +ℕ len-f
                  arith-eq =
                    begin
                      7 +ℕ (7 +ℕ (len-f +ℕ 3))
                    ≡⟨ cong (λ x → 7 +ℕ x) (cong (λ x → 7 +ℕ x) (+-comm len-f 3)) ⟩
                      7 +ℕ (7 +ℕ (3 +ℕ len-f))
                    ≡⟨ cong (λ x → 7 +ℕ x) (sym (+-assoc 7 3 len-f)) ⟩
                      7 +ℕ (10 +ℕ len-f)
                    ≡⟨ sym (+-assoc 7 10 len-f) ⟩
                      17 +ℕ len-f
                    ∎

          -- pc3-eq has pc st3 = cleanup exit position, need to relate to ret-offset-calc
          -- From thunk-cleanup-star-proven: pc s' ≡ ret-offset where ret-offset = length prefix +ℕ (thunk-body-offset +ℕ 3) +ℕ len-f
          pc3-at-ret : pc st3 ≡ length ret-prefix
          pc3-at-ret = trans pc3-eq (sym len-ret-prefix)

          -- Step the ret instruction
          step-ret : step (ret-prefix ++ ret ∷ ret-suffix) st3 ≡ just st4-def
          step-ret = step-ret-at-offset ret-prefix ret-suffix st3 h3 pc3-at-ret

          -- Convert to prog using prog-eq-ret
          step-ret-prog : step prog st3 ≡ just st4-def
          step-ret-prog = subst (λ p → step p st3 ≡ just st4-def) (sym prog-eq-ret) step-ret

          -- Build Star proof
          star-ret : Star prog st3 st4-def
          star-ret = star-single h3 step-ret-prog

          -- Properties of st4-def
          h4-def : halted st4-def ≡ false
          h4-def = h3  -- ret doesn't change halted

          pc4-def : pc st4-def ≡ ret-addr
          pc4-def = ra-is-ret

          a0-ret-def : readReg (regs st4-def) a0 ≡ readReg (regs st3) a0
          a0-ret-def = refl  -- ret doesn't change a0

          s1-ret-def : readReg (regs st4-def) s1 ≡ readReg (regs st3) s1
          s1-ret-def = refl  -- ret doesn't change s1

          ret-result : ∃[ st4 ] (Star prog st3 st4
                                × halted st4 ≡ false
                                × pc st4 ≡ ret-addr
                                × readReg (regs st4) a0 ≡ readReg (regs st3) a0
                                × readReg (regs st4) s1 ≡ readReg (regs st3) s1)
          ret-result = st4-def , star-ret , h4-def , pc4-def , a0-ret-def , s1-ret-def

          st4 = proj₁ ret-result
          star4 = proj₁ (proj₂ ret-result)
          h4 = proj₁ (proj₂ (proj₂ ret-result))
          pc4 = proj₁ (proj₂ (proj₂ (proj₂ ret-result)))
          a0-after-ret = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))
          s1-after-ret = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))

          -- Compose all Star proofs
          star-all : Star prog s st4
          star-all = star-trans star1 (star-trans star2 (star-trans star3 star4))

          -- Build final results
          s-final : State
          s-final = st4

          pc-final : pc s-final ≡ ret-addr
          pc-final = pc4

          -- s1 preserved through all phases
          s1-preserved : readReg (regs s-final) s1 ≡ readReg (regs s) s1
          s1-preserved = trans s1-after-ret
                         (trans s1-after-cleanup
                         (trans s1-after-f s1-after-setup))

          -- a0 contains result
          a0-result : readReg (regs s-final) a0 ≡ encode (eval f (x , arg))
          a0-result = trans a0-after-ret (trans a0-after-cleanup a0-after-f)

          thunk-result : ThunkResult prog s s-final clos-sem arg
          thunk-result = record
            { thunk-star = star-all
            ; thunk-halted = h4
            ; thunk-a0 = a0-result
            ; thunk-s1 = s1-preserved
            }

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

