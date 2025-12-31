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
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen
  using (compile-riscv; compile-length; StackDelta; StackDepth; neg16; neg24)

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Postulates
  using (run-apply-star; sp-bound-for-f-in-thunk)

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
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra;
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

  -- Curry: use run-curry-star from IR/Curry.agda
  -- StackDepth (curry f) = 16 + StackDepth f, but curry only allocates 16 bytes
  -- TODO: Replace curry-output-wf postulate with proven WF from run-curry-star-with-wf
  --       This requires refactoring to avoid type-checking timeout.
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq sp-bound-16
    where
      -- Derive 16 ≤ sp from 16 + StackDepth f ≤ sp
      sp-bound-16 : 16 ≤ readReg (regs s) sp
      sp-bound-16 = ≤-trans (m≤m+n 16 (StackDepth f)) sp-bound

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq _ =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: use extracted context helpers (needs to pass sp-bound through)
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'
    where
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- SP bound for f: StackDepth f ≤ StackDepth (g ∘ f) ≤ sp
      -- Since StackDepth (g ∘ f) = StackDepth f ⊔ (StackDelta f + StackDepth g)
      sp-bound-for-f : StackDepth f ≤ readReg (regs s) sp
      sp-bound-for-f = ≤-trans (m≤m⊔n (StackDepth f) (StackDelta f +ℕ StackDepth g)) sp-bound

      -- Step 1: Execute f
      step-f = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq a0-eq sp-bound-for-f
      sf = proj₁ step-f
      rf = proj₂ step-f
      rf' = transform-f-result f g prefix suffix x s sf rf

      -- Step 2: Execute g (no transfer needed - a0 already has result!)
      a0-after-f : readReg (regs sf) a0 ≡ encode (eval f x)
      a0-after-f = ir-a0 rf

      -- PC conversion
      pc-for-g : pc sf ≡ length prefix-g
      pc-for-g = trans (ir-pc rf) (sym len-prefix-g)

      -- SP bound for g: Derive StackDepth g ≤ sf.sp from:
      --   1. StackDelta f + StackDepth g ≤ StackDepth (g ∘ f) ≤ s.sp  (from m≤n⊔m)
      --   2. sf.sp + delta_f = s.sp (from ir-sp)
      --   3. delta_f ≤ StackDelta f (from ir-sp-delta-leq)
      -- Chain: StackDelta f + StackDepth g ≤ sf.sp + delta_f ≤ sf.sp + StackDelta f
      -- Then use +-cancelˡ-≤ to get StackDepth g ≤ sf.sp

      -- StackDelta f + StackDepth g ≤ s.sp
      compose-bound : StackDelta f +ℕ StackDepth g ≤ readReg (regs s) sp
      compose-bound = ≤-trans (m≤n⊔m (StackDepth f) (StackDelta f +ℕ StackDepth g)) sp-bound

      -- sf.sp + delta_f = s.sp, rearranged: s.sp = sf.sp + delta_f
      -- So: StackDelta f + StackDepth g ≤ sf.sp + delta_f
      bound-rhs : StackDelta f +ℕ StackDepth g ≤ readReg (regs sf) sp +ℕ ir-sp-delta rf
      bound-rhs = subst (StackDelta f +ℕ StackDepth g ≤_) (sym (ir-sp rf)) compose-bound

      -- sf.sp + delta_f ≤ sf.sp + StackDelta f (using +-monoʳ-≤)
      step1-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ readReg (regs sf) sp +ℕ StackDelta f
      step1-g = +-monoʳ-≤ (readReg (regs sf) sp) (ir-sp-delta-leq rf)

      -- sf.sp + StackDelta f = StackDelta f + sf.sp (by commutativity)
      step2-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ StackDelta f +ℕ readReg (regs sf) sp
      step2-g = subst (readReg (regs sf) sp +ℕ ir-sp-delta rf ≤_)
                  (+-comm (readReg (regs sf) sp) (StackDelta f)) step1-g

      -- Chain: StackDelta f + StackDepth g ≤ StackDelta f + sf.sp
      bound-chain : StackDelta f +ℕ StackDepth g ≤ StackDelta f +ℕ readReg (regs sf) sp
      bound-chain = ≤-trans bound-rhs step2-g

      sp-bound-for-g : StackDepth g ≤ readReg (regs sf) sp
      sp-bound-for-g = cancel-+-left (StackDelta f) bound-chain

      step-g = run-ir-star-at-offset g prefix-g suffix (eval f x) sf
                 (ir-halted rf) pc-for-g a0-after-f sp-bound-for-g
      sg = proj₁ step-g
      rg = proj₂ step-g
      rg' = transform-g-result f g prefix suffix x sf sg rg

  -- Pair: use extracted context helpers with frame pointer approach
  -- Frame pointer allows f and g to use arbitrary stack space.
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Case: use extracted context helpers
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Pair helper - proven using phase helpers and IH with frame pointer approach
  -- Frame pointer (s2) allows f and g to use arbitrary stack space.
  -- No longer requires StackDelta f = 0 or StackDelta g = 0.
  run-pair-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ⟨ f , g ⟩ ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  -- TODO: Implement frame pointer pair proof
  -- This proof chains:
  -- 1. pair-setup-star (5 instructions) - allocate frame, save s1/s2, set frame pointer
  -- 2. run-ir-star-at-offset f - execute f with IH
  -- 3. pair-middle-star (2 instructions) - store f result at frame, restore input
  -- 4. run-ir-star-at-offset g - execute g with IH
  -- 5. pair-final-star (5 instructions) - store g result, return pair pointer, restore s1/s2
  run-pair-star {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = sp-delta-final
      ; ir-sp-delta-leq = sp-delta-leq-final
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf-final
      }
    where
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix
      orig-sp = readReg (regs s) sp
      orig-s1 = readReg (regs s) s1
      orig-s2 = readReg (regs s) s2

      -- Derive 32 ≤ sp from StackDepth bound
      -- StackDepth ⟨ f , g ⟩ = 32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤ sp
      32≤sp : 32 ≤ orig-sp
      32≤sp = ≤-trans (m≤m+n 32 (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g))) sp-bound

      -- =====================================================================
      -- Phase 1: Setup (5 instructions)
      -- =====================================================================
      setup-result = pair-setup-star f g prefix suffix x s h-false pc-eq a0-eq 32≤sp
      s-setup = proj₁ setup-result
      private module SetupR = PairSetupResult (proj₂ setup-result)
      star-setup = SetupR.star-setup
      h-setup = SetupR.h-setup
      pc-setup' = SetupR.pc-setup
      a0-setup = SetupR.a0-setup
      s1-setup = SetupR.s1-setup
      sp-setup = SetupR.sp-setup
      s2-setup = SetupR.s2-setup
      ra-setup = SetupR.ra-setup
      mem-s1-setup = SetupR.mem-s1-setup
      mem-s2-setup = SetupR.mem-s2-setup
      mem-preserved-setup = SetupR.mem-preserved-setup

      -- PC for f: offset + 5 = length prefix-f
      pc-for-f : pc s-setup ≡ length prefix-f
      pc-for-f = trans pc-setup' (sym len-prefix-f)

      -- Derive sp-bound for f: StackDepth f ≤ sp-setup = orig-sp - 32
      -- From: 32 + (StackDepth f ⊔ (StackDelta f + StackDepth g)) ≤ orig-sp
      -- Get: StackDepth f ⊔ (StackDelta f + StackDepth g) ≤ orig-sp - 32
      inner-bound : StackDepth f ⊔ (StackDelta f +ℕ StackDepth g) ≤ orig-sp ∸ 32
      inner-bound = cancel-+-left 32 sp-bound-rewritten
        where
          -- Rewrite orig-sp as 32 + (orig-sp - 32)
          orig-sp-eq : orig-sp ≡ 32 +ℕ (orig-sp ∸ 32)
          orig-sp-eq = trans (sym (m∸n+n≡m 32≤sp)) (+-comm (orig-sp ∸ 32) 32)
          -- Transform sp-bound to use the rewritten form
          sp-bound-rewritten : 32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤ 32 +ℕ (orig-sp ∸ 32)
          sp-bound-rewritten = subst (32 +ℕ (StackDepth f ⊔ (StackDelta f +ℕ StackDepth g)) ≤_) orig-sp-eq sp-bound

      sp-bound-f : StackDepth f ≤ readReg (regs s-setup) sp
      sp-bound-f = subst (StackDepth f ≤_) (sym sp-setup) (≤-trans (m≤m⊔n (StackDepth f) (StackDelta f +ℕ StackDepth g)) inner-bound)

      -- =====================================================================
      -- Phase 2: Execute f with IH
      -- =====================================================================
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup h-setup pc-for-f a0-setup sp-bound-f
      sf = proj₁ step-f
      rf = proj₂ step-f

      -- =====================================================================
      -- Phase 3: Middle (2 instructions)
      -- =====================================================================
      -- Need: sf.s2 = orig-sp ∸ 32 (frame pointer preserved through f)
      s2-sf : readReg (regs sf) s2 ≡ orig-sp ∸ 32
      s2-sf = trans (ir-s2 rf) s2-setup

      -- pc for middle: mid-offset = offset + 5 + len-f
      -- ir-pc rf : pc sf ≡ length prefix-f +ℕ compile-length f (= len-f)
      -- len-prefix-f : length prefix-f ≡ length prefix +ℕ 5
      -- len-f = compile-length f (by definition in PairContext)
      pc-for-mid : pc sf ≡ length prefix +ℕ 5 +ℕ len-f
      pc-for-mid = trans (ir-pc rf) (cong (_+ℕ len-f) len-prefix-f)

      -- s1-sf: s1 preserved through f, still contains input x
      s1-sf : readReg (regs sf) s1 ≡ encode x
      s1-sf = trans (ir-s1 rf) s1-setup

      middle-result = pair-middle-star f g prefix suffix x orig-sp sf (ir-halted rf) pc-for-mid
                        (ir-a0 rf) s1-sf 32≤sp s2-sf
      s-mid = proj₁ middle-result
      private module MiddleR = PairMiddleResult (proj₂ middle-result)
      star-mid = MiddleR.star-mid
      h-mid = MiddleR.h-mid
      pc-mid' = MiddleR.pc-mid
      a0-mid = MiddleR.a0-mid
      s1-mid = MiddleR.s1-mid
      sp-mid = MiddleR.sp-mid
      s2-mid = MiddleR.s2-mid
      ra-mid = MiddleR.ra-mid
      mem-f-stored = MiddleR.mem-f-stored
      mem-s2+16-mid = MiddleR.mem-s2+16-mid
      mem-s2+24-mid = MiddleR.mem-s2+24-mid
      mem-preserved-mid = MiddleR.mem-preserved-mid

      -- =====================================================================
      -- Phase 4: Execute g with IH
      -- =====================================================================
      -- PC for g: length prefix-g = offset + 7 + len-f
      -- pc-mid' : pc s-mid ≡ (length prefix +ℕ 5 +ℕ len-f) +ℕ 2
      -- len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      -- Need to show: ((a + 5) + b) + 2 = (a + 7) + b
      -- Step 1: ((a + 5) + b) + 2 = (a + 5) + (b + 2)  by +-assoc
      -- Step 2: (a + 5) + (b + 2) = (a + 5) + (2 + b)  by +-comm on inner
      -- Step 3: (a + 5) + (2 + b) = ((a + 5) + 2) + b  by sym +-assoc
      -- Step 4: ((a + 5) + 2) + b = (a + 7) + b        by (a+5)+2 = a+7

      -- Helper: (a + 5) + 2 = a + 7  (using a + (5 + 2) = a + 7)
      a5-plus-2 : (length prefix +ℕ 5) +ℕ 2 ≡ length prefix +ℕ 7
      a5-plus-2 = +-assoc (length prefix) 5 2  -- (a + 5) + 2 = a + (5 + 2) = a + 7

      mid-to-prefix-g : (length prefix +ℕ 5 +ℕ len-f) +ℕ 2 ≡ length prefix +ℕ 7 +ℕ len-f
      mid-to-prefix-g =
        trans (+-assoc (length prefix +ℕ 5) len-f 2)  -- (a+5) + (b+2)
          (trans (cong (length prefix +ℕ 5 +ℕ_) (+-comm len-f 2))  -- (a+5) + (2+b)
            (trans (sym (+-assoc (length prefix +ℕ 5) 2 len-f))  -- ((a+5)+2) + b
              (cong (_+ℕ len-f) a5-plus-2)))  -- (a+7) + b

      pc-for-g : pc s-mid ≡ length prefix-g
      pc-for-g = trans pc-mid' (trans mid-to-prefix-g (sym len-prefix-g))

      -- SP bound for g: StackDepth g ≤ s-mid.sp
      -- Similar to compose: derive from inner-bound and sf's state
      -- After f: sf.sp + ir-sp-delta rf = s-setup.sp = orig-sp - 32
      -- After middle: s-mid.sp = sf.sp
      -- Need: StackDepth g ≤ sf.sp

      -- From inner-bound: StackDelta f + StackDepth g ≤ orig-sp - 32
      delta-g-bound : StackDelta f +ℕ StackDepth g ≤ orig-sp ∸ 32
      delta-g-bound = ≤-trans (m≤n⊔m (StackDepth f) (StackDelta f +ℕ StackDepth g)) inner-bound

      -- sf.sp + delta_rf = s-setup.sp = orig-sp - 32
      -- So StackDelta f + StackDepth g ≤ sf.sp + delta_rf
      bound-rhs-g : StackDelta f +ℕ StackDepth g ≤ readReg (regs sf) sp +ℕ ir-sp-delta rf
      bound-rhs-g = subst (StackDelta f +ℕ StackDepth g ≤_)
                      (sym (trans (ir-sp rf) sp-setup)) delta-g-bound

      -- sf.sp + delta_rf ≤ sf.sp + StackDelta f
      step1-bound-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ readReg (regs sf) sp +ℕ StackDelta f
      step1-bound-g = +-monoʳ-≤ (readReg (regs sf) sp) (ir-sp-delta-leq rf)

      -- Chain and cancel
      step2-bound-g : readReg (regs sf) sp +ℕ ir-sp-delta rf ≤ StackDelta f +ℕ readReg (regs sf) sp
      step2-bound-g = subst (readReg (regs sf) sp +ℕ ir-sp-delta rf ≤_)
                        (+-comm (readReg (regs sf) sp) (StackDelta f)) step1-bound-g

      bound-chain-g : StackDelta f +ℕ StackDepth g ≤ StackDelta f +ℕ readReg (regs sf) sp
      bound-chain-g = ≤-trans bound-rhs-g step2-bound-g

      sp-bound-g' : StackDepth g ≤ readReg (regs sf) sp
      sp-bound-g' = cancel-+-left (StackDelta f) bound-chain-g

      -- sp-mid = sp-sf
      sp-bound-g : StackDepth g ≤ readReg (regs s-mid) sp
      sp-bound-g = subst (StackDepth g ≤_) (sym sp-mid) sp-bound-g'

      step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid h-mid pc-for-g a0-mid sp-bound-g
      sg = proj₁ step-g
      rg = proj₂ step-g

      -- =====================================================================
      -- Phase 5: Final (5 instructions)
      -- =====================================================================
      -- Need to set up preconditions for pair-final-star
      -- Chain s2 preservation: s-mid.s2 = sf.s2 = orig-sp - 32
      s2-mid-eq : readReg (regs s-mid) s2 ≡ orig-sp ∸ 32
      s2-mid-eq = trans s2-mid s2-sf

      s2-sg : readReg (regs sg) s2 ≡ orig-sp ∸ 32
      s2-sg = trans (ir-s2 rg) s2-mid-eq

      -- PC for final: final-offset = offset + 7 + len-f + len-g
      -- ir-pc rg : pc sg ≡ length prefix-g +ℕ compile-length g (= len-g)
      -- len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      -- len-g = compile-length g (by definition in PairContext)
      pc-for-final : pc sg ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      pc-for-final = trans (ir-pc rg) (cong (_+ℕ len-g) len-prefix-g)

      -- Memory at frame pointer: need f result stored (from middle)
      frame-ptr-sg = readReg (regs sg) s2
      frame-ptr-eq-sg : frame-ptr-sg ≡ orig-sp ∸ 32
      frame-ptr-eq-sg = s2-sg

      -- f result is at frame-ptr (stored in middle, preserved through g)
      -- Key: frame-ptr = s-mid.sp + ir-sp-delta rf, so use ir-mem-preserved rg

      -- SP relationship: s-mid.sp + ir-sp-delta rf = orig-sp - 32
      sp-mid-to-frame : readReg (regs s-mid) sp +ℕ ir-sp-delta rf ≡ orig-sp ∸ 32
      sp-mid-to-frame = trans (cong (_+ℕ ir-sp-delta rf) sp-mid) (trans (ir-sp rf) sp-setup)

      -- Memory at (s-mid.sp + delta) preserved through g
      mem-frame-preserved : readMem (memory sg) (readReg (regs s-mid) sp +ℕ ir-sp-delta rf)
                          ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ ir-sp-delta rf)
      mem-frame-preserved = ir-mem-preserved rg (ir-sp-delta rf)

      -- mem-f-stored gives memory at sf.s2 in s-mid has f result
      -- sf.s2 = orig-sp - 32, so this is memory at (orig-sp - 32)
      mem-f-at-frame : readMem (memory s-mid) (orig-sp ∸ 32) ≡ just (encode (eval f x))
      mem-f-at-frame = subst (λ addr → readMem (memory s-mid) addr ≡ just (encode (eval f x)))
                         s2-sf mem-f-stored

      -- Chain through address equality
      -- frame-ptr-sg = orig-sp - 32 = s-mid.sp + delta
      mem-frame-sg : readMem (memory sg) frame-ptr-sg ≡ just (encode (eval f x))
      mem-frame-sg =
        trans (cong (readMem (memory sg)) frame-ptr-eq-sg)  -- at orig-sp - 32
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame))  -- at s-mid.sp + delta
            (trans mem-frame-preserved  -- preserved through g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame)  -- back to orig-sp - 32
                mem-f-at-frame)))

      -- g's result is in a0
      a0-sg : readReg (regs sg) a0 ≡ encode (eval g x)
      a0-sg = ir-a0 rg

      -- s1 saved at frame+16: chain through f and middle
      -- Setup: mem-s1-setup says memory at (s-setup.s2 + 16) = just orig-s1
      -- Through f: ir-mem-preserved rf preserves at (s-setup.sp + n)
      -- Through middle: mem-s2+16-mid preserves at (sf.s2 + 16)

      -- Memory preserved through g
      mem-s1-preserved-g : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16))
                         ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16))
      mem-s1-preserved-g = ir-mem-preserved rg (ir-sp-delta rf +ℕ 16)

      -- (s-mid.sp + delta) + 16 = (orig-sp - 32) + 16
      sp-mid-to-frame+16 : readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 16) ≡ (orig-sp ∸ 32) +ℕ 16
      sp-mid-to-frame+16 = trans (sym (+-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf) 16))
                             (cong (_+ℕ 16) sp-mid-to-frame)

      -- Memory preserved through f: at s-setup.sp + 16
      mem-s1-preserved-f : readMem (memory sf) (readReg (regs s-setup) sp +ℕ 16)
                         ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ 16)
      mem-s1-preserved-f = ir-mem-preserved rf 16

      -- s-setup.sp = s-setup.s2 = orig-sp - 32
      s2-eq-sp-setup : readReg (regs s-setup) s2 ≡ readReg (regs s-setup) sp
      s2-eq-sp-setup = trans s2-setup (sym sp-setup)

      -- sf.s2 = s-setup.s2 (preserved through f)
      sf-s2-eq : readReg (regs sf) s2 ≡ readReg (regs s-setup) s2
      sf-s2-eq = ir-s2 rf

      -- Memory at (orig-sp - 32) + 16 in s-mid
      -- = memory at sf.s2 + 16 in s-mid (via s2-sf)
      -- = memory at sf.s2 + 16 in sf (via mem-s2+16-mid)
      -- = memory at s-setup.s2 + 16 in sf (via sf-s2-eq)
      -- = memory at s-setup.sp + 16 in sf (via s2-eq-sp-setup)
      -- = memory at s-setup.sp + 16 in s-setup (via mem-s1-preserved-f)
      -- = memory at s-setup.s2 + 16 in s-setup (via s2-eq-sp-setup)
      -- = just orig-s1 (via mem-s1-setup)
      mem-s1-at-frame : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 16) ≡ just orig-s1
      mem-s1-at-frame =
        let addr-s2-sf = readReg (regs sf) s2 +ℕ 16
            addr-s2-setup = readReg (regs s-setup) s2 +ℕ 16
            addr-sp-setup = readReg (regs s-setup) sp +ℕ 16
            -- s-mid at (orig-sp - 32 + 16) = s-mid at sf.s2 + 16
            step1 : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 16) ≡ readMem (memory s-mid) addr-s2-sf
            step1 = cong (λ a → readMem (memory s-mid) (a +ℕ 16)) (sym s2-sf)
            -- = sf at sf.s2 + 16 (via mem-s2+16-mid)
            step2 : readMem (memory s-mid) addr-s2-sf ≡ readMem (memory sf) addr-s2-sf
            step2 = mem-s2+16-mid
            -- = sf at s-setup.s2 + 16 (via sf-s2-eq)
            step3 : readMem (memory sf) addr-s2-sf ≡ readMem (memory sf) addr-s2-setup
            step3 = cong (λ a → readMem (memory sf) (a +ℕ 16)) sf-s2-eq
            -- = sf at s-setup.sp + 16 (via s2-eq-sp-setup)
            step4 : readMem (memory sf) addr-s2-setup ≡ readMem (memory sf) addr-sp-setup
            step4 = cong (λ a → readMem (memory sf) (a +ℕ 16)) s2-eq-sp-setup
            -- = s-setup at s-setup.sp + 16 (via mem-s1-preserved-f)
            step5 : readMem (memory sf) addr-sp-setup ≡ readMem (memory s-setup) addr-sp-setup
            step5 = mem-s1-preserved-f
            -- = s-setup at s-setup.s2 + 16 (via s2-eq-sp-setup)
            step6 : readMem (memory s-setup) addr-sp-setup ≡ readMem (memory s-setup) addr-s2-setup
            step6 = cong (λ a → readMem (memory s-setup) (a +ℕ 16)) (sym s2-eq-sp-setup)
            -- = just orig-s1 (via mem-s1-setup)
            step7 : readMem (memory s-setup) addr-s2-setup ≡ just orig-s1
            step7 = mem-s1-setup
        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))

      -- Chain: frame-ptr-sg + 16 = (orig-sp - 32) + 16 = s-mid.sp + (delta + 16)
      mem-s1-sg : readMem (memory sg) (frame-ptr-sg +ℕ 16) ≡ just orig-s1
      mem-s1-sg =
        trans (cong (λ a → readMem (memory sg) (a +ℕ 16)) frame-ptr-eq-sg)
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame+16))
            (trans mem-s1-preserved-g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame+16)
                mem-s1-at-frame)))

      -- s2 saved at frame+24: similar 7-step pattern as s1
      mem-s2-preserved-g : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24))
                         ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24))
      mem-s2-preserved-g = ir-mem-preserved rg (ir-sp-delta rf +ℕ 24)

      sp-mid-to-frame+24 : readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 24) ≡ (orig-sp ∸ 32) +ℕ 24
      sp-mid-to-frame+24 = trans (sym (+-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf) 24))
                             (cong (_+ℕ 24) sp-mid-to-frame)

      -- Memory preserved through f: at s-setup.sp + 24
      mem-s2-preserved-f : readMem (memory sf) (readReg (regs s-setup) sp +ℕ 24)
                         ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ 24)
      mem-s2-preserved-f = ir-mem-preserved rf 24

      -- Memory at (orig-sp - 32) + 24 in s-mid = just orig-s2
      -- Chain through middle → sf → s-setup
      mem-s2-at-frame : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 24) ≡ just orig-s2
      mem-s2-at-frame =
        let addr-s2-sf = readReg (regs sf) s2 +ℕ 24
            addr-s2-setup = readReg (regs s-setup) s2 +ℕ 24
            addr-sp-setup = readReg (regs s-setup) sp +ℕ 24
            -- s-mid at (orig-sp - 32 + 24) = s-mid at sf.s2 + 24
            step1 : readMem (memory s-mid) ((orig-sp ∸ 32) +ℕ 24) ≡ readMem (memory s-mid) addr-s2-sf
            step1 = cong (λ a → readMem (memory s-mid) (a +ℕ 24)) (sym s2-sf)
            -- = sf at sf.s2 + 24 (via mem-s2+24-mid)
            step2 : readMem (memory s-mid) addr-s2-sf ≡ readMem (memory sf) addr-s2-sf
            step2 = mem-s2+24-mid
            -- = sf at s-setup.s2 + 24 (via sf-s2-eq)
            step3 : readMem (memory sf) addr-s2-sf ≡ readMem (memory sf) addr-s2-setup
            step3 = cong (λ a → readMem (memory sf) (a +ℕ 24)) sf-s2-eq
            -- = sf at s-setup.sp + 24 (via s2-eq-sp-setup)
            step4 : readMem (memory sf) addr-s2-setup ≡ readMem (memory sf) addr-sp-setup
            step4 = cong (λ a → readMem (memory sf) (a +ℕ 24)) s2-eq-sp-setup
            -- = s-setup at s-setup.sp + 24 (via mem-s2-preserved-f)
            step5 : readMem (memory sf) addr-sp-setup ≡ readMem (memory s-setup) addr-sp-setup
            step5 = mem-s2-preserved-f
            -- = s-setup at s-setup.s2 + 24 (via s2-eq-sp-setup)
            step6 : readMem (memory s-setup) addr-sp-setup ≡ readMem (memory s-setup) addr-s2-setup
            step6 = cong (λ a → readMem (memory s-setup) (a +ℕ 24)) (sym s2-eq-sp-setup)
            -- = just orig-s2 (via mem-s2-setup)
            step7 : readMem (memory s-setup) addr-s2-setup ≡ just orig-s2
            step7 = mem-s2-setup
        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))

      mem-s2-sg : readMem (memory sg) (frame-ptr-sg +ℕ 24) ≡ just orig-s2
      mem-s2-sg =
        trans (cong (λ a → readMem (memory sg) (a +ℕ 24)) frame-ptr-eq-sg)
          (trans (cong (readMem (memory sg)) (sym sp-mid-to-frame+24))
            (trans mem-s2-preserved-g
              (trans (cong (readMem (memory s-mid)) sp-mid-to-frame+24)
                mem-s2-at-frame)))

      final-phase = pair-final-star f g prefix suffix x orig-s1 orig-s2 orig-sp sg (ir-halted rg)
                       pc-for-final a0-sg mem-frame-sg mem-s1-sg mem-s2-sg 32≤sp s2-sg
      s-final = proj₁ final-phase
      private module FinalR = PairFinalResult (proj₂ final-phase)
      star-final = FinalR.star-final
      h-final = FinalR.h-final
      pc-final' = FinalR.pc-final
      a0-final' = FinalR.a0-final
      s1-final' = FinalR.s1-final
      s2-final' = FinalR.s2-final
      ra-final' = FinalR.ra-final
      sp-final' = FinalR.sp-final
      mem-preserved-final' = FinalR.mem-preserved-final

      -- =====================================================================
      -- Assemble final result
      -- =====================================================================
      -- Chain all Star proofs
      -- Convert ir-star rf from (prefix-f ++ code-f ++ suffix-f) to prog using prog-eq-f
      ir-star-rf-prog : Star prog s-setup sf
      ir-star-rf-prog = subst (λ p → Star p s-setup sf) (sym prog-eq-f) (ir-star rf)

      -- Convert ir-star rg from (prefix-g ++ code-g ++ suffix-g) to prog using prog-eq-g
      ir-star-rg-prog : Star prog s-mid sg
      ir-star-rg-prog = subst (λ p → Star p s-mid sg) (sym prog-eq-g) (ir-star rg)

      star-setup-f = star-trans star-setup ir-star-rf-prog
      star-setup-f-mid = star-trans star-setup-f star-mid
      star-setup-f-mid-g = star-trans star-setup-f-mid ir-star-rg-prog
      star-all = star-trans star-setup-f-mid-g star-final

      -- PC: offset + 12 + len-f + len-g = offset + compile-length pair
      -- pc-final' : pc s-final ≡ (length prefix +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5
      -- compile-length ⟨ f , g ⟩ : length (compile-riscv ⟨ f , g ⟩) ≡ (12 +ℕ len-f) +ℕ len-g
      -- Need: (a + 7 + b + c) + 5 = a + ((12 + b) + c)
      pc-arith : (offset +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5 ≡ offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
      pc-arith = begin
        (offset +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 5
          ≡⟨ +-assoc (offset +ℕ 7 +ℕ len-f) len-g 5 ⟩
        (offset +ℕ 7 +ℕ len-f) +ℕ (len-g +ℕ 5)
          ≡⟨ cong ((offset +ℕ 7 +ℕ len-f) +ℕ_) (+-comm len-g 5) ⟩
        (offset +ℕ 7 +ℕ len-f) +ℕ (5 +ℕ len-g)
          ≡⟨ sym (+-assoc (offset +ℕ 7 +ℕ len-f) 5 len-g) ⟩
        ((offset +ℕ 7 +ℕ len-f) +ℕ 5) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (+-assoc (offset +ℕ 7) len-f 5) ⟩
        ((offset +ℕ 7) +ℕ (len-f +ℕ 5)) +ℕ len-g
          ≡⟨ cong (λ x → ((offset +ℕ 7) +ℕ x) +ℕ len-g) (+-comm len-f 5) ⟩
        ((offset +ℕ 7) +ℕ (5 +ℕ len-f)) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (offset +ℕ 7) 5 len-f)) ⟩
        (((offset +ℕ 7) +ℕ 5) +ℕ len-f) +ℕ len-g
          ≡⟨ cong (λ x → (x +ℕ len-f) +ℕ len-g) (+-assoc offset 7 5) ⟩
        ((offset +ℕ 12) +ℕ len-f) +ℕ len-g
          ≡⟨ cong (_+ℕ len-g) (+-assoc offset 12 len-f) ⟩
        (offset +ℕ (12 +ℕ len-f)) +ℕ len-g
          ≡⟨ +-assoc offset (12 +ℕ len-f) len-g ⟩
        offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
          ∎

      -- compile-length ⟨ f , g ⟩ = (12 +ℕ len-f) +ℕ len-g  (definitional)
      -- pc-arith ends at: offset +ℕ ((12 +ℕ len-f) +ℕ len-g)
      -- which equals: offset +ℕ compile-length ⟨ f , g ⟩
      pc-final : pc s-final ≡ offset +ℕ compile-length ⟨ f , g ⟩
      pc-final = trans pc-final' pc-arith

      -- a0 = encode (eval f x, eval g x)
      a0-final : readReg (regs s-final) a0 ≡ encode (eval f x , eval g x)
      a0-final = a0-final'

      -- s1 restored
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = s1-final'

      -- s2 restored
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = s2-final'

      -- ra preserved through all phases
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-final' (trans (ir-ra rg) (trans ra-mid (trans (ir-ra rf) ra-setup)))

      -- Stack delta: 32 + StackDelta f + StackDelta g
      sp-delta-final : ℕ
      sp-delta-final = 32 +ℕ ir-sp-delta rf +ℕ ir-sp-delta rg

      -- sp-delta-final = 32 + delta-rf + delta-rg
      -- StackDelta ⟨ f , g ⟩ = 32 + StackDelta f + StackDelta g
      -- From IH: delta-rf ≤ StackDelta f, delta-rg ≤ StackDelta g
      sp-delta-leq-final : sp-delta-final ≤ StackDelta ⟨ f , g ⟩
      sp-delta-leq-final =
        let
          -- From inductive hypothesis
          leq-f : ir-sp-delta rf ≤ StackDelta f
          leq-f = ir-sp-delta-leq rf

          leq-g : ir-sp-delta rg ≤ StackDelta g
          leq-g = ir-sp-delta-leq rg

          -- 32 ≤ 32
          leq-32 : 32 ≤ 32
          leq-32 = ≤-refl

          -- (32 + delta-rf) ≤ (32 + StackDelta f)
          leq-inner : 32 +ℕ ir-sp-delta rf ≤ 32 +ℕ StackDelta f
          leq-inner = +-mono-≤ leq-32 leq-f

          -- (32 + delta-rf) + delta-rg ≤ (32 + StackDelta f) + StackDelta g
          leq-outer : (32 +ℕ ir-sp-delta rf) +ℕ ir-sp-delta rg ≤ (32 +ℕ StackDelta f) +ℕ StackDelta g
          leq-outer = +-mono-≤ leq-inner leq-g

        in leq-outer

      -- sp relationship: chain through all phases
      -- s-final.sp = sg.sp (from sp-final')
      -- sg.sp + delta-g = s-mid.sp (from ir-sp rg)
      -- s-mid.sp = sf.sp (from sp-mid)
      -- sf.sp + delta-f = s-setup.sp (from ir-sp rf)
      -- s-setup.sp = orig-sp - 32 (from sp-setup)
      -- (orig-sp - 32) + 32 = orig-sp (from m∸n+n≡m)
      sp-final : readReg (regs s-final) sp +ℕ sp-delta-final ≡ readReg (regs s) sp
      sp-final =
        let
          -- Rename for clarity
          sp-f = readReg (regs sf) sp
          delta-f = ir-sp-delta rf
          delta-g = ir-sp-delta rg
          sp-g = readReg (regs sg) sp
          sp-mid-val = readReg (regs s-mid) sp

          -- Step 1: s-final.sp + (32 + delta-f + delta-g) = sg.sp + (32 + delta-f + delta-g)
          step1 : readReg (regs s-final) sp +ℕ sp-delta-final ≡ sp-g +ℕ sp-delta-final
          step1 = cong (_+ℕ sp-delta-final) sp-final'

          -- Step 2: Rearrange (32 + delta-f) + delta-g → delta-g + (32 + delta-f)
          rearrange1 : (32 +ℕ delta-f) +ℕ delta-g ≡ delta-g +ℕ (32 +ℕ delta-f)
          rearrange1 = +-comm (32 +ℕ delta-f) delta-g

          -- Step 3: sg.sp + (delta-g + (32 + delta-f)) = (sg.sp + delta-g) + (32 + delta-f)
          step3 : sp-g +ℕ (delta-g +ℕ (32 +ℕ delta-f)) ≡ (sp-g +ℕ delta-g) +ℕ (32 +ℕ delta-f)
          step3 = sym (+-assoc sp-g delta-g (32 +ℕ delta-f))

          -- Step 4: sg.sp + delta-g = s-mid.sp (from ir-sp rg)
          step4 : (sp-g +ℕ delta-g) +ℕ (32 +ℕ delta-f) ≡ sp-mid-val +ℕ (32 +ℕ delta-f)
          step4 = cong (_+ℕ (32 +ℕ delta-f)) (ir-sp rg)

          -- Step 5: s-mid.sp = sf.sp (from sp-mid)
          step5 : sp-mid-val +ℕ (32 +ℕ delta-f) ≡ sp-f +ℕ (32 +ℕ delta-f)
          step5 = cong (_+ℕ (32 +ℕ delta-f)) sp-mid

          -- Step 6: Rearrange 32 + delta-f → delta-f + 32
          rearrange2 : 32 +ℕ delta-f ≡ delta-f +ℕ 32
          rearrange2 = +-comm 32 delta-f

          -- Step 7: sf.sp + (delta-f + 32) = (sf.sp + delta-f) + 32
          step7 : sp-f +ℕ (delta-f +ℕ 32) ≡ (sp-f +ℕ delta-f) +ℕ 32
          step7 = sym (+-assoc sp-f delta-f 32)

          -- Step 8: sf.sp + delta-f = s-setup.sp (from ir-sp rf)
          step8 : (sp-f +ℕ delta-f) +ℕ 32 ≡ readReg (regs s-setup) sp +ℕ 32
          step8 = cong (_+ℕ 32) (ir-sp rf)

          -- Step 9: s-setup.sp = orig-sp - 32 (from sp-setup)
          step9 : readReg (regs s-setup) sp +ℕ 32 ≡ (orig-sp ∸ 32) +ℕ 32
          step9 = cong (_+ℕ 32) sp-setup

          -- Step 10: (orig-sp - 32) + 32 = orig-sp
          step10 : (orig-sp ∸ 32) +ℕ 32 ≡ orig-sp
          step10 = m∸n+n≡m 32≤sp

        in trans step1
            (trans (cong (sp-g +ℕ_) rearrange1)
            (trans step3
            (trans step4
            (trans step5
            (trans (cong (sp-f +ℕ_) rearrange2)
            (trans step7
            (trans step8
            (trans step9 step10))))))))

      -- Memory preserved at orig-sp and above
      -- Chain through all 5 phases: s → s-setup → sf → s-mid → sg → s-final
      mem-preserved-final : (n : ℕ) → readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
      mem-preserved-final n =
        let
          -- Phase 1: s → s-setup (setup preserves at orig-sp + n)
          step1 : readMem (memory s-setup) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          step1 = mem-preserved-setup n

          -- Phase 2: s-setup → sf (f preserves at s-setup.sp + k for any k)
          -- Key: orig-sp + n = s-setup.sp + (32 + n) since s-setup.sp = orig-sp - 32
          addr-as-setup-offset : orig-sp +ℕ n ≡ readReg (regs s-setup) sp +ℕ (32 +ℕ n)
          addr-as-setup-offset =
            let
              -- orig-sp = (orig-sp - 32) + 32
              step-a : orig-sp ≡ (orig-sp ∸ 32) +ℕ 32
              step-a = sym (m∸n+n≡m 32≤sp)
              -- orig-sp + n = ((orig-sp - 32) + 32) + n
              step-b : orig-sp +ℕ n ≡ ((orig-sp ∸ 32) +ℕ 32) +ℕ n
              step-b = cong (_+ℕ n) step-a
              -- ((orig-sp - 32) + 32) + n = (orig-sp - 32) + (32 + n)
              step-c : ((orig-sp ∸ 32) +ℕ 32) +ℕ n ≡ (orig-sp ∸ 32) +ℕ (32 +ℕ n)
              step-c = +-assoc (orig-sp ∸ 32) 32 n
              -- (orig-sp - 32) = s-setup.sp
              step-d : (orig-sp ∸ 32) +ℕ (32 +ℕ n) ≡ readReg (regs s-setup) sp +ℕ (32 +ℕ n)
              step-d = cong (_+ℕ (32 +ℕ n)) (sym sp-setup)
            in trans step-b (trans step-c step-d)

          step2' : readMem (memory sf) (readReg (regs s-setup) sp +ℕ (32 +ℕ n))
                 ≡ readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ (32 +ℕ n))
          step2' = ir-mem-preserved rf (32 +ℕ n)

          step2 : readMem (memory sf) (orig-sp +ℕ n) ≡ readMem (memory s-setup) (orig-sp +ℕ n)
          step2 = trans (cong (readMem (memory sf)) addr-as-setup-offset)
                    (trans step2' (cong (readMem (memory s-setup)) (sym addr-as-setup-offset)))

          -- Phase 3: sf → s-mid (middle preserves at orig-sp + n)
          step3 : readMem (memory s-mid) (orig-sp +ℕ n) ≡ readMem (memory sf) (orig-sp +ℕ n)
          step3 = mem-preserved-mid n

          -- Phase 4: s-mid → sg (g preserves at s-mid.sp + k for any k)
          -- Key: orig-sp + n = s-mid.sp + (delta-f + 32 + n) since s-mid.sp = sf.sp and sf.sp + delta-f = orig-sp - 32
          addr-as-mid-offset : orig-sp +ℕ n ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n)
          addr-as-mid-offset =
            let
              -- sf.sp + ir-sp-delta rf = s-setup.sp = orig-sp - 32
              sf-sp-eq : readReg (regs sf) sp +ℕ ir-sp-delta rf ≡ orig-sp ∸ 32
              sf-sp-eq = trans (ir-sp rf) sp-setup
              -- s-mid.sp = sf.sp
              mid-sp-eq : readReg (regs s-mid) sp ≡ readReg (regs sf) sp
              mid-sp-eq = sp-mid
              -- orig-sp = (orig-sp - 32) + 32
              orig-from-monus : orig-sp ≡ (orig-sp ∸ 32) +ℕ 32
              orig-from-monus = sym (m∸n+n≡m 32≤sp)
              -- orig-sp = (sf.sp + delta) + 32
              orig-as-sf : orig-sp ≡ (readReg (regs sf) sp +ℕ ir-sp-delta rf) +ℕ 32
              orig-as-sf = trans orig-from-monus (cong (_+ℕ 32) (sym sf-sp-eq))
              -- (sf.sp + delta) + 32 = sf.sp + (delta + 32)
              reassoc-sf : (readReg (regs sf) sp +ℕ ir-sp-delta rf) +ℕ 32 ≡ readReg (regs sf) sp +ℕ (ir-sp-delta rf +ℕ 32)
              reassoc-sf = +-assoc (readReg (regs sf) sp) (ir-sp-delta rf) 32
              -- sf.sp + (delta + 32) = s-mid.sp + (delta + 32)
              sf-to-mid : readReg (regs sf) sp +ℕ (ir-sp-delta rf +ℕ 32) ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)
              sf-to-mid = cong (_+ℕ (ir-sp-delta rf +ℕ 32)) (sym mid-sp-eq)
              -- orig-sp = s-mid.sp + (delta + 32)
              orig-as-mid : orig-sp ≡ readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)
              orig-as-mid = trans orig-as-sf (trans reassoc-sf sf-to-mid)
              -- orig-sp + n = (s-mid.sp + (delta + 32)) + n
              step-a : orig-sp +ℕ n ≡ (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)) +ℕ n
              step-a = cong (_+ℕ n) orig-as-mid
              -- (s-mid.sp + (delta + 32)) + n = s-mid.sp + ((delta + 32) + n)
              step-b : (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32)) +ℕ n ≡ readReg (regs s-mid) sp +ℕ ((ir-sp-delta rf +ℕ 32) +ℕ n)
              step-b = +-assoc (readReg (regs s-mid) sp) (ir-sp-delta rf +ℕ 32) n
            in trans step-a step-b

          step4' : readMem (memory sg) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n))
                 ≡ readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (ir-sp-delta rf +ℕ 32 +ℕ n))
          step4' = ir-mem-preserved rg (ir-sp-delta rf +ℕ 32 +ℕ n)

          step4 : readMem (memory sg) (orig-sp +ℕ n) ≡ readMem (memory s-mid) (orig-sp +ℕ n)
          step4 = trans (cong (readMem (memory sg)) addr-as-mid-offset)
                    (trans step4' (cong (readMem (memory s-mid)) (sym addr-as-mid-offset)))

          -- Phase 5: sg → s-final (final preserves at orig-sp + n)
          step5 : readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory sg) (orig-sp +ℕ n)
          step5 = mem-preserved-final' n

        in trans step5 (trans step4 (trans step3 (trans step2 step1)))

      -- Output well-formedness for pair
      -- Convert ir-output-wf from subprogram-indexed to prog-indexed
      wf-f-prog : ClosuresWF A prog
      wf-f-prog = subst (ClosuresWF A) (sym prog-eq-f) (ir-output-wf rf)

      wf-g-prog : ClosuresWF B prog
      wf-g-prog = subst (ClosuresWF B) (sym prog-eq-g) (ir-output-wf rg)

      output-wf-final : ClosuresWF (A * B) prog
      output-wf-final = pairWF wf-f-prog wf-g-prog

  -- Case helper - proven using dispatch helpers and IH
  run-case-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    StackDepth ([ f , g ]) ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
    in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  -- Left path implementation (inj₁ a)
  run-case-star {_} {A} {B} {C} f g prefix suffix (inj₁ a) s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = ir-sp-delta r-f
      ; ir-sp-delta-leq = sp-delta-leq
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (3 instructions, branch NOT taken)
      dispatch-result = case-dispatch-left-star f g prefix suffix a s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      private module DispatchLR = CaseDispatchLeftResult (proj₂ dispatch-result)
      star-dispatch = DispatchLR.star-dispatch
      h-dispatch = DispatchLR.h-dispatch
      pc-dispatch = DispatchLR.pc-dispatch
      a0-dispatch = DispatchLR.a0-dispatch
      t0-dispatch = DispatchLR.t0-dispatch
      s1-dispatch = DispatchLR.s1-dispatch
      s2-dispatch = DispatchLR.s2-dispatch
      ra-dispatch = DispatchLR.ra-dispatch
      sp-dispatch = DispatchLR.sp-dispatch
      mem-dispatch = DispatchLR.mem-dispatch

      -- Phase 2: Execute f (IH call)
      -- PC for f: need length prefix-f
      pc-for-f : pc s-dispatch ≡ length prefix-f
      pc-for-f = trans pc-dispatch (sym len-prefix-f)

      -- sp-bound for f: StackDepth f ≤ StackDepth f ⊔ StackDepth g = StackDepth ([ f , g ]) ≤ sp
      -- dispatch preserves sp, so StackDepth f ≤ s-dispatch.sp
      sp-bound-f : StackDepth f ≤ readReg (regs s-dispatch) sp
      sp-bound-f = subst (StackDepth f ≤_) (sym sp-dispatch) (≤-trans (m≤m⊔n (StackDepth f) (StackDepth g)) sp-bound)

      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-dispatch h-dispatch pc-for-f a0-dispatch sp-bound-f
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

      -- Stack delta proof: delta_f ≤ max(StackDelta f, StackDelta g)
      sp-delta-leq : ir-sp-delta r-f ≤ StackDelta ([ f , g ])
      sp-delta-leq = ≤-trans (ir-sp-delta-leq r-f) (m≤m⊔n (StackDelta f) (StackDelta g))

      -- Convert f result to use prog
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-dispatch s-after-f-raw
      star-f-raw = ir-star r-f

      star-f : Star prog s-dispatch s-after-f-raw
      star-f = subst (λ p → Star p s-dispatch s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract f result properties
      h-after-f = ir-halted r-f
      a0-after-f = ir-a0 r-f
      s1-after-f = ir-s1 r-f
      ra-after-f = ir-ra r-f

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ len-f
      pc-f-raw = ir-pc r-f

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 3 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      s2-after-f = ir-s2 r-f

      -- Phase 3: Jump over g (2 instructions)
      jump-result = case-left-jump-star f g prefix suffix s-after-f-raw h-after-f pc-after-f
      s-final = proj₁ jump-result
      private module JumpR = CaseLeftJumpResult (proj₂ jump-result)
      star-jump = JumpR.star-jump
      h-final = JumpR.h-jump
      pc-jump = JumpR.pc-jump
      a0-jump = JumpR.a0-jump
      s1-jump = JumpR.s1-jump
      s2-jump = JumpR.s2-jump
      ra-jump = JumpR.ra-jump
      sp-jump = JumpR.sp-jump
      mem-jump = JumpR.mem-jump

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-f star-jump)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-left-jump-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-jump pc-convert

      -- Final a0: eval [f,g] (inj₁ a) = eval f a
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₁ a))
      a0-final = trans a0-jump (trans a0-after-f refl)

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-jump (trans s1-after-f s1-dispatch)

      -- s2 preservation
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = trans s2-jump (trans s2-after-f s2-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-jump (trans ra-after-f ra-dispatch)

      -- sp tracking: case inherits f's delta
      -- Chains through: dispatch (delta=0) → f (delta_f) → jump (delta=0)
      -- Total: sp_final + delta_f = sp_s
      sp-after-f : readReg (regs s-after-f-raw) sp +ℕ ir-sp-delta r-f ≡ readReg (regs s-dispatch) sp
      sp-after-f = ir-sp r-f
      sp-final : readReg (regs s-final) sp +ℕ ir-sp-delta r-f ≡ readReg (regs s) sp
      sp-final = begin
        readReg (regs s-final) sp +ℕ ir-sp-delta r-f
          ≡⟨ cong (_+ℕ ir-sp-delta r-f) sp-jump ⟩
        readReg (regs s-after-f-raw) sp +ℕ ir-sp-delta r-f
          ≡⟨ ir-sp r-f ⟩
        readReg (regs s-dispatch) sp
          ≡⟨ sp-dispatch ⟩
        readReg (regs s) sp
          ∎

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → f (ir-mem-preserved) → jump (mem unchanged)
      -- The key is that dispatch and jump don't write memory, and f preserves caller's frame
      mem-preserved-final : ∀ n → readMem (memory s-final) (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
      mem-preserved-final n = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-jump ⟩
        readMem (memory s-after-f-raw) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-after-f-raw) (a +ℕ n)) (sym sp-dispatch) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ ir-mem-preserved r-f n ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ n)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ n)
          ∎

      -- Output WF: comes from f's output (left path)
      output-wf : ClosuresWF C prog
      output-wf = subst (ClosuresWF C) (sym prog-eq-f) (ir-output-wf r-f)

  -- Right path implementation (inj₂ b)
  run-case-star {_} {A} {B} {C} f g prefix suffix (inj₂ b) s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = ir-sp-delta r-g
      ; ir-sp-delta-leq = sp-delta-leq
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (4 instructions, branch TAKEN + landing label)
      dispatch-result = case-dispatch-right-star f g prefix suffix b s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      private module DispatchRR = CaseDispatchRightResult (proj₂ dispatch-result)
      star-dispatch = DispatchRR.star-dispatch
      h-dispatch = DispatchRR.h-dispatch
      pc-dispatch = DispatchRR.pc-dispatch
      a0-dispatch = DispatchRR.a0-dispatch
      s1-dispatch = DispatchRR.s1-dispatch
      s2-dispatch = DispatchRR.s2-dispatch
      ra-dispatch = DispatchRR.ra-dispatch
      sp-dispatch = DispatchRR.sp-dispatch
      mem-dispatch = DispatchRR.mem-dispatch

      -- Phase 2: Execute g (IH call)
      pc-for-g : pc s-dispatch ≡ length prefix-g
      pc-for-g = trans pc-dispatch (sym len-prefix-g)

      -- sp-bound for g: StackDepth g ≤ StackDepth f ⊔ StackDepth g = StackDepth ([ f , g ]) ≤ sp
      -- dispatch preserves sp, so StackDepth g ≤ s-dispatch.sp
      sp-bound-g : StackDepth g ≤ readReg (regs s-dispatch) sp
      sp-bound-g = subst (StackDepth g ≤_) (sym sp-dispatch) (≤-trans (m≤n⊔m (StackDepth f) (StackDepth g)) sp-bound)

      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-dispatch h-dispatch pc-for-g a0-dispatch sp-bound-g
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

      -- Stack delta proof: delta_g ≤ max(StackDelta f, StackDelta g)
      sp-delta-leq : ir-sp-delta r-g ≤ StackDelta ([ f , g ])
      sp-delta-leq = ≤-trans (ir-sp-delta-leq r-g) (m≤n⊔m (StackDelta f) (StackDelta g))

      -- Convert g result to use prog
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-dispatch s-after-g-raw
      star-g-raw = ir-star r-g

      star-g : Star prog s-dispatch s-after-g-raw
      star-g = subst (λ p → Star p s-dispatch s-after-g-raw) (sym prog-eq-g) star-g-raw

      -- Extract g result properties
      h-after-g = ir-halted r-g
      a0-after-g = ir-a0 r-g
      s1-after-g = ir-s1 r-g
      ra-after-g = ir-ra r-g

      pc-g-raw : pc s-after-g-raw ≡ length prefix-g +ℕ len-g
      pc-g-raw = ir-pc r-g

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      s2-after-g = ir-s2 r-g

      -- Phase 3: Execute end-label (1 instruction)
      end-result = case-right-end-star f g prefix suffix s-after-g-raw h-after-g pc-after-g
      s-final = proj₁ end-result
      private module EndR = CaseRightEndResult (proj₂ end-result)
      star-end = EndR.star-end
      h-final = EndR.h-end
      pc-end = EndR.pc-end
      a0-end = EndR.a0-end
      s1-end = EndR.s1-end
      s2-end = EndR.s2-end
      ra-end = EndR.ra-end
      sp-end = EndR.sp-end
      mem-end = EndR.mem-end

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-g star-end)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-right-end-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-end pc-convert

      -- Final a0: eval [f,g] (inj₂ b) = eval g b
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₂ b))
      a0-final = trans a0-end a0-after-g

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-end (trans s1-after-g s1-dispatch)

      -- s2 preservation
      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = trans s2-end (trans s2-after-g s2-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-end (trans ra-after-g ra-dispatch)

      -- sp tracking: case inherits g's delta
      -- Chains through: dispatch (delta=0) → g (delta_g) → end-label (delta=0)
      -- Total: sp_final + delta_g = sp_s
      sp-after-g : readReg (regs s-after-g-raw) sp +ℕ ir-sp-delta r-g ≡ readReg (regs s-dispatch) sp
      sp-after-g = ir-sp r-g
      sp-final : readReg (regs s-final) sp +ℕ ir-sp-delta r-g ≡ readReg (regs s) sp
      sp-final = begin
        readReg (regs s-final) sp +ℕ ir-sp-delta r-g
          ≡⟨ cong (_+ℕ ir-sp-delta r-g) sp-end ⟩
        readReg (regs s-after-g-raw) sp +ℕ ir-sp-delta r-g
          ≡⟨ ir-sp r-g ⟩
        readReg (regs s-dispatch) sp
          ≡⟨ sp-dispatch ⟩
        readReg (regs s) sp
          ∎

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → g (ir-mem-preserved) → end-label (mem unchanged)
      mem-preserved-final : ∀ n → readMem (memory s-final) (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
      mem-preserved-final n = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-end ⟩
        readMem (memory s-after-g-raw) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-after-g-raw) (a +ℕ n)) (sym sp-dispatch) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ ir-mem-preserved r-g n ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ n)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ n)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ n)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ n)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ n)
          ∎

      -- Output WF: comes from g's output (right path)
      output-wf : ClosuresWF C prog
      output-wf = subst (ClosuresWF C) (sym prog-eq-g) (ir-output-wf r-g)

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- RISC-V thunk layout within curry (positions 7 onwards):
  --   7: label code-ptr (thunk entry)
  --   8: addi sp sp -24 (allocate 24 bytes: 8 saved-s2 + 16 pair)
  --   9: sd s2 16(sp) (save frame pointer)
  --   10: mv s2 sp (set frame pointer)
  --   11: sd s0 0(sp) (store env = a at pair.fst)
  --   12: sd a0 8(sp) (store arg = b at pair.snd)
  --   13: mv a0 sp (a0 = pair pointer)
  --   14 to 13+len-f: compile-riscv f
  --   14+len-f: mv sp s2 (restore sp)
  --   15+len-f: ld s2 16(sp) (restore s2)
  --   16+len-f: addi sp sp 24 (deallocate)
  --   17+len-f: ret
  --   18+len-f: label end
  --
  -- Structure:
  --   1. Trace 7 setup instructions (label, addi, sd s2, mv s2, sd s0, sd a0, mv a0)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace 4 cleanup/ret instructions (mv sp, ld s2, addi sp, ret)
  --   4. Compose via star-trans
  ------------------------------------------------------------------------

  -- Prove thunk setup: 7 instructions (label, addi sp -24, sd s2, mv s2, sd s0, sd a0, mv a0)
  -- Now using the proven version from ThunkSetup module
  thunk-setup-star : ∀ {i A B C} (f : IR i (A * B) C)
                     (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 7
        f-offset = length prefix +ℕ 14
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) a0 ≡ encode arg →
    readReg (regs s) s0 ≡ encode env →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ f-offset
            × readReg (regs s') a0 ≡ encode (env , arg)
            × readReg (regs s') s1 ≡ readReg (regs s) s1
            × readReg (regs s') ra ≡ readReg (regs s) ra
            × readReg (regs s') s2 ≡ readReg (regs s) sp ∸ 24  -- s2 = frame pointer
            × readReg (regs s') sp ≡ readReg (regs s) sp ∸ 24  -- sp = new-sp
            × readMem (memory s') (readReg (regs s) sp ∸ 24 +ℕ 16) ≡ just (readReg (regs s) s2))  -- saved s2
  thunk-setup-star = thunk-setup-star-proven

  -- Prove ret instruction tracing (after cleanup)
  -- The thunk cleanup does: mv sp s2, ld s2 16(sp), addi sp sp 24, ret
  -- We prove just the ret here; cleanup is traced separately or postulated
  thunk-ret-star : ∀ {i A B C} (f : IR i (A * B) C)
                   (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        ret-offset = length prefix +ℕ 17 +ℕ compile-length f
    in
    halted s ≡ false →
    pc s ≡ ret-offset →
    readReg (regs s) ra ≡ ret-addr →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ ret-addr
            × readReg (regs s') a0 ≡ readReg (regs s) a0
            × readReg (regs s') s1 ≡ readReg (regs s) s1)
  thunk-ret-star {_} {A} {B} {C} f prefix suffix ret-addr s h-false pc-eq ra-eq =
    s' , star-all , h' , pc' , a0' , s1'
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      offset = length prefix
      ret-offset = offset +ℕ 17 +ℕ compile-length f

      -- The ret instruction is at ret-offset in curry
      -- curry layout: [7 closure setup] [7 thunk setup] [compile-riscv f] [3 cleanup] [ret] [label end]
      -- ret is at position 17 + len(f) within curry

      len-f = compile-length f

      -- First 14 instructions of curry (closure setup + thunk setup)
      curry-prefix-to-14 : Program
      curry-prefix-to-14 = addi sp sp neg16 ∷       -- 0
                           sd a0 (+ 0) sp ∷         -- 1
                           auipc t0 (+ 0) ∷         -- 2
                           addi t0 t0 (+ 5) ∷       -- 3
                           sd t0 (+ 8) sp ∷         -- 4
                           mv a0 sp ∷               -- 5
                           j (+ (12 +ℕ len-f)) ∷    -- 6 (jump over thunk, updated offset)
                           label 7 ∷                -- 7
                           addi sp sp neg24 ∷       -- 8
                           sd s2 (+ 16) sp ∷        -- 9
                           mv s2 sp ∷               -- 10
                           sd s0 (+ 0) sp ∷         -- 11
                           sd a0 (+ 8) sp ∷         -- 12
                           mv a0 sp ∷               -- 13
                           []

      -- Cleanup instructions after f
      thunk-cleanup : Program
      thunk-cleanup = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ []

      -- curry code = curry-prefix-to-14 ++ compile-riscv f ++ cleanup ++ ret ∷ label-end ∷ []
      curry-code-eq : compile-riscv (curry f) ≡
                      curry-prefix-to-14 ++ compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []
      curry-code-eq = refl

      -- Build prefix up to ret
      prefix-to-ret : Program
      prefix-to-ret = ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ thunk-cleanup

      len-prefix-to-ret : length prefix-to-ret ≡ ret-offset
      len-prefix-to-ret = begin
        length prefix-to-ret
          ≡⟨ List-length-++ ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ⟩
        length ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) +ℕ 3
          ≡⟨ cong (_+ℕ 3) (List-length-++ (prefix ++ curry-prefix-to-14)) ⟩
        (length (prefix ++ curry-prefix-to-14) +ℕ length (compile-riscv f)) +ℕ 3
          ≡⟨ cong (λ x → (x +ℕ length (compile-riscv f)) +ℕ 3) (List-length-++ prefix) ⟩
        ((offset +ℕ 14) +ℕ length (compile-riscv f)) +ℕ 3
          ≡⟨ cong (λ x → ((offset +ℕ 14) +ℕ x) +ℕ 3) (compile-length-correct f) ⟩
        ((offset +ℕ 14) +ℕ len-f) +ℕ 3
          ≡⟨ +-assoc (offset +ℕ 14) len-f 3 ⟩
        (offset +ℕ 14) +ℕ (len-f +ℕ 3)
          ≡⟨ +-assoc offset 14 (len-f +ℕ 3) ⟩
        offset +ℕ (14 +ℕ (len-f +ℕ 3))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 14 len-f 3)) ⟩
        offset +ℕ ((14 +ℕ len-f) +ℕ 3)
          ≡⟨ cong (λ x → offset +ℕ (x +ℕ 3)) (+-comm 14 len-f) ⟩
        offset +ℕ ((len-f +ℕ 14) +ℕ 3)
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 14 3) ⟩
        offset +ℕ (len-f +ℕ 17)
          ≡⟨ cong (offset +ℕ_) (+-comm len-f 17) ⟩
        offset +ℕ (17 +ℕ len-f)
          ≡⟨ sym (+-assoc offset 17 len-f) ⟩
        (offset +ℕ 17) +ℕ len-f
          ∎

      -- Show prog decomposes to prefix-to-ret ++ ret ∷ suffix'
      prog-eq-ret : prog ≡ prefix-to-ret ++ ret ∷ _
      prog-eq-ret = begin
        prog
          ≡⟨ cong (λ c → prefix ++ c ++ suffix) curry-code-eq ⟩
        prefix ++ (curry-prefix-to-14 ++ compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong (prefix ++_) (++-assoc curry-prefix-to-14 _ suffix) ⟩
        prefix ++ (curry-prefix-to-14 ++ (compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc prefix curry-prefix-to-14 _) ⟩
        (prefix ++ curry-prefix-to-14) ++ (compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong ((prefix ++ curry-prefix-to-14) ++_) (++-assoc (compile-riscv f) _ suffix) ⟩
        (prefix ++ curry-prefix-to-14) ++ (compile-riscv f ++ (thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc (prefix ++ curry-prefix-to-14) (compile-riscv f) _) ⟩
        ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ (thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong (((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++_) (++-assoc thunk-cleanup _ suffix) ⟩
        ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ (thunk-cleanup ++ (ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) thunk-cleanup _) ⟩
        prefix-to-ret ++ (ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ refl ⟩
        prefix-to-ret ++ ret ∷ _
          ∎

      fetch-ret : fetch prog ret-offset ≡ just ret
      fetch-ret = subst₂ (λ p n → fetch p n ≡ just ret) (sym prog-eq-ret) len-prefix-to-ret
                         (fetch-at-prefix-end prefix-to-ret ret _)

      -- State after ret: pc = ra, everything else unchanged
      s' : State
      s' = record s { pc = readReg (regs s) ra }

      -- Step execution using ret semantics
      step-ret : step prog s ≡ just s'
      step-ret = trans (step-exec prog s ret h-false (subst (λ p → fetch prog p ≡ just ret) (sym pc-eq) fetch-ret))
                       (execRet prog s)

      star-all : Star prog s s'
      star-all = ⟨ h-false , step-ret ⟩◅ refl*

      h' : halted s' ≡ false
      h' = h-false

      pc' : pc s' ≡ ret-addr
      pc' = ra-eq

      -- Register preservation (ret doesn't modify any registers, just pc)
      a0' : readReg (regs s') a0 ≡ readReg (regs s) a0
      a0' = refl

      s1' : readReg (regs s') s1 ≡ readReg (regs s) s1
      s1' = refl

  -- | curry-thunk-correct-impl: Implementation using IH
  -- This composes: setup tracing → IH on f → ret tracing
  curry-thunk-correct-impl : ∀ {i A B C} (f : IR i (A * B) C)
                             (prefix suffix : Program) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 7
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) a0 ≡ encode arg →
    readReg (regs s) s0 ≡ encode env →
    readReg (regs s) ra ≡ ret-addr →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
  curry-thunk-correct-impl {_} {A} {B} {C} f prefix suffix env arg s ret-addr
                           h-eq pc-eq a0-eq s0-eq ra-eq =
    s-final , thunk-result , pc-final
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 7
      f-offset = length prefix +ℕ 14
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f

      -- Step 1: Trace 7 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq a0-eq s0-eq
      s-after-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      ra-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      s2-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))  -- frame pointer
      sp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))  -- sp = new-sp
      mem-s2-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))  -- saved s2

      -- saved-s2-value is the original s2 at thunk entry
      saved-s2-value : Word
      saved-s2-value = readReg (regs s) s2

      -- new-sp = frame pointer
      new-sp : Word
      new-sp = readReg (regs s) sp ∸ 24

      -- Step 2: Call IH on f using program reassociation
      -- Key insight: curry compiles to structured form that we can reassociate
      len-f = compile-length f
      code-f = compile-riscv f

      -- RISC-V curry structure (7 + 7 + len-f + 5 = 19 + len-f instructions)
      -- curry-closure-setup: 7 instructions (0-6)
      curry-closure-setup : Program
      curry-closure-setup = addi sp sp neg16 ∷
                            sd a0 (+ 0) sp ∷
                            auipc t0 (+ 0) ∷
                            addi t0 t0 (+ 5) ∷
                            sd t0 (+ 8) sp ∷
                            mv a0 sp ∷
                            j (+ (12 +ℕ len-f)) ∷ []  -- updated offset

      -- curry-thunk-setup: 7 instructions (7-13)
      curry-thunk-setup : Program
      curry-thunk-setup = label 7 ∷
                          addi sp sp neg24 ∷
                          sd s2 (+ 16) sp ∷
                          mv s2 sp ∷
                          sd s0 (+ 0) sp ∷
                          sd a0 (+ 8) sp ∷
                          mv a0 sp ∷ []

      -- curry-tail: 5 instructions (14+len-f to 18+len-f)
      curry-tail : Program
      curry-tail = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ []

      -- prefix-f and suffix-f for calling IH
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
      len-prefix-f = trans (List-length-++ prefix)
                           (cong (length prefix +ℕ_) refl)

      -- curry-structure: compile-riscv (curry f) = closure-setup ++ thunk-setup ++ f ++ tail
      curry-structure : compile-riscv (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup ++ code-f ++ curry-tail
      curry-structure = refl

      -- Program reassociation proof
      -- prog = prefix ++ (A ++ B ++ f ++ C) ++ suffix = (prefix ++ A ++ B) ++ f ++ (C ++ suffix)
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          ccs = curry-closure-setup
          cts = curry-thunk-setup
          cta = curry-tail

          prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
          prog-reassoc =
            let inner-assoc1 : ccs ++ (cts ++ (code-f ++ cta)) ≡ (ccs ++ cts) ++ (code-f ++ cta)
                inner-assoc1 = sym (++-assoc ccs cts (code-f ++ cta))

                inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ cta) suffix

                inner-assoc3 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
                inner-assoc3 = ++-assoc code-f cta suffix

                inner-combined : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (cta ++ suffix))
                inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                 (trans inner-assoc2
                                        (cong ((ccs ++ cts) ++_) inner-assoc3))

                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined

                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))

            in trans outer-step final-assoc

      -- Call IH on f
      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      -- SP bound for f: thunk setup allocates 24 bytes, need StackDepth f ≤ sp-after-setup
      -- Using module-level postulate
      sp-bound-for-f : StackDepth f ≤ readReg (regs s-after-setup) sp
      sp-bound-for-f = sp-bound-for-f-in-thunk f s-after-setup

      step-f : ∃[ s-f ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f (env , arg) s-after-setup
                 h-setup pc-setup-f a0-setup sp-bound-for-f

      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = ir-star r-f

      -- Convert star-f to use prog
      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract properties from IH result
      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = ir-pc r-f

      -- After f, PC is at length prefix + 14 + len-f = cleanup-offset
      -- We need cleanup tracing to get to ret-offset = length prefix + 17 + len-f
      cleanup-offset = length prefix +ℕ 14 +ℕ len-f

      pc-f-is-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-is-cleanup = trans pc-f-raw (trans (cong (_+ℕ len-f) len-prefix-f) refl)

      -- Step 2.5: Trace cleanup instructions (3 instructions)
      -- thunk-cleanup-star-proven traces: mv sp s2, ld s2 16(sp), addi sp sp +24

      -- Memory preservation through f:
      -- Thunk setup: memory at new-sp + 16 = saved-s2-value
      -- After f: s-after-f-raw.s2 = s-after-setup.s2 = new-sp (f preserves s2)
      -- f preserves memory at its caller's sp + n, which is s-after-setup.sp + n = new-sp + n
      -- So memory at new-sp + 16 is preserved through f

      -- s-after-f-raw.s2 = s-after-setup.s2 = new-sp (f preserves s2, setup sets s2 = new-sp)
      s2-after-f : readReg (regs s-after-f-raw) s2 ≡ new-sp
      s2-after-f = trans (ir-s2 r-f) s2-setup

      -- s-after-setup.sp = new-sp (from thunk setup)
      sp-after-setup : readReg (regs s-after-setup) sp ≡ new-sp
      sp-after-setup = sp-setup  -- thunk setup returns sp = new-sp

      -- Memory at new-sp + 16 is preserved through f (ir-mem-preserved at offset 16)
      -- Chain: convert new-sp to s-after-setup.sp → ir-mem-preserved → convert back
      mem-preserved-through-f : readMem (memory s-after-f-raw) (new-sp +ℕ 16) ≡ readMem (memory s-after-setup) (new-sp +ℕ 16)
      mem-preserved-through-f = trans (cong (λ addr → readMem (memory s-after-f-raw) (addr +ℕ 16)) (sym sp-after-setup))
                                      (trans (ir-mem-preserved r-f 16)
                                             (cong (λ addr → readMem (memory s-after-setup) (addr +ℕ 16)) sp-after-setup))

      -- Chain: memory at new-sp + 16 = saved-s2-value (from setup, preserved through f)
      mem-s2-after-f : readMem (memory s-after-f-raw) (new-sp +ℕ 16) ≡ just saved-s2-value
      mem-s2-after-f = trans mem-preserved-through-f mem-s2-setup

      -- Cleanup precondition: memory at s-after-f-raw.s2 + 16 = saved-s2-value
      -- Since s-after-f-raw.s2 = new-sp, this is exactly mem-s2-after-f
      mem-s2-precond : readMem (memory s-after-f-raw) (readReg (regs s-after-f-raw) s2 +ℕ 16) ≡ just saved-s2-value
      mem-s2-precond = subst (λ addr → readMem (memory s-after-f-raw) (addr +ℕ 16) ≡ just saved-s2-value)
                             (sym s2-after-f) mem-s2-after-f

      cleanup-result = thunk-cleanup-star-proven f prefix suffix saved-s2-value s-after-f-raw
                         (ir-halted r-f) pc-f-is-cleanup mem-s2-precond
      s-after-cleanup = proj₁ cleanup-result
      star-cleanup-raw = proj₁ (proj₂ cleanup-result)
      h-cleanup = proj₁ (proj₂ (proj₂ cleanup-result))
      pc-cleanup = proj₁ (proj₂ (proj₂ (proj₂ cleanup-result)))
      a0-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))
      s1-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result)))))
      ra-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))))
      s2-cleanup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))))

      -- star-cleanup-raw has type Star (prefix ++ compile-riscv (curry f) ++ suffix) = Star prog
      -- But we need Star (prefix-f ++ code-f ++ suffix-f) for composition
      -- prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      star-cleanup-converted : Star (prefix-f ++ code-f ++ suffix-f) s-after-f-raw s-after-cleanup
      star-cleanup-converted = subst (λ p → Star p s-after-f-raw s-after-cleanup) prog-eq-f star-cleanup-raw

      -- ra preservation: chain through IH, setup, and cleanup
      ra-preserved : readReg (regs s-after-cleanup) ra ≡ ret-addr
      ra-preserved = trans ra-cleanup (trans (ir-ra r-f) (trans ra-setup ra-eq))

      -- Combine f execution and cleanup
      star-f-and-cleanup : Star (prefix-f ++ code-f ++ suffix-f) s-after-setup s-after-cleanup
      star-f-and-cleanup = star-trans star-f-raw star-cleanup-converted

      -- Convert to use prog
      star-f-and-cleanup-prog : Star prog s-after-setup s-after-cleanup
      star-f-and-cleanup-prog = subst (λ p → Star p s-after-setup s-after-cleanup) (sym prog-eq-f) star-f-and-cleanup

      f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                 × halted s-f ≡ false
                                 × pc s-f ≡ ret-offset
                                 × readReg (regs s-f) a0 ≡ encode (eval f (env , arg))
                                 × readReg (regs s-f) s1 ≡ readReg (regs s-after-setup) s1
                                 × readReg (regs s-f) ra ≡ ret-addr)
      f-result-bridge = s-after-cleanup ,
                        star-f-and-cleanup-prog ,
                        h-cleanup ,
                        pc-cleanup ,
                        trans a0-cleanup (ir-a0 r-f) ,
                        trans s1-cleanup (ir-s1 r-f) ,
                        ra-preserved

      s-after-f = proj₁ f-result-bridge
      star-f = proj₁ (proj₂ f-result-bridge)
      h-f = proj₁ (proj₂ (proj₂ f-result-bridge))
      pc-f = proj₁ (proj₂ (proj₂ (proj₂ f-result-bridge)))
      a0-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))
      s1-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))
      ra-f = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))

      -- Step 3: Trace ret instruction
      ret-result = thunk-ret-star f prefix suffix ret-addr s-after-f
                     h-f pc-f ra-f
      s-final = proj₁ ret-result
      star-ret = proj₁ (proj₂ ret-result)
      h-final = proj₁ (proj₂ (proj₂ ret-result))
      pc-final = proj₁ (proj₂ (proj₂ (proj₂ ret-result)))
      a0-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))
      s1-final = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      thunk-result : ThunkResult prog s s-final (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-a0 = trans a0-final a0-f
        ; thunk-s1 = trans s1-final (trans s1-f s1-setup)
        }

  ------------------------------------------------------------------------
  -- run-curry-star-with-wf: Curry with ClosureWellFormed proof
  --
  -- This is an enhanced version of run-curry-star that also produces
  -- a ClosureWellFormed proof. The proof is constructed using
  -- curry-thunk-correct-impl, which is available in this mutual block.
  ------------------------------------------------------------------------

  open import Once.Backend.RiscV64.Correct.ClosureWellFormed
    using (CurryResult; curry-star; curry-halted; curry-pc; curry-a0; curry-s1; closure-wf)
  open import Data.Nat using (_<_)

  run-curry-star-with-wf : ∀ {i A B C} (f : IR i (A * B) C)
                           (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    16 ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        offset = length prefix
    in ∃[ s' ] CurryResult f prog s s' x offset

  run-curry-star-with-wf {_} {A} {B} {C} f prefix suffix x s h-false pc-eq a0-eq sp-bound =
    let (s' , result) = run-curry-star f prefix suffix x s h-false pc-eq a0-eq sp-bound
        offset = length prefix
        prog = prefix ++ compile-riscv (curry f) ++ suffix
    in s' , record
      { curry-star   = ir-star result
      ; curry-halted = ir-halted result
      ; curry-pc     = ir-pc result
      ; curry-a0     = ir-a0 result
      ; curry-s1     = ir-s1 result
      ; closure-wf   = record
          { code-ptr-valid = code-ptr-valid-proof
          ; thunk-correct  = λ arg s' ret-addr h-eq' pc-eq' a0-eq' s0-eq' ra-eq' →
              curry-thunk-correct-impl f prefix suffix x arg s' ret-addr
                h-eq' pc-eq' a0-eq' s0-eq' ra-eq'
          }
      }
    where
      offset = length prefix
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      curry-code = compile-riscv (curry f)

      -- code-ptr = offset + 7 < length prog
      -- Proof: length prog = length prefix + length curry-code + length suffix
      --        length curry-code = 19 + compile-length f ≥ 19
      --        So offset + 7 < offset + 19 ≤ length prog
      code-ptr-valid-proof : offset +ℕ 7 < length prog
      code-ptr-valid-proof = proof
        where
          open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-<)

          -- 7 < 19 = 8 ≤ 19
          seven-lt-nineteen : 7 < 19
          seven-lt-nineteen = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

          -- length curry-code = 19 + compile-length f
          len-curry : length curry-code ≡ 19 +ℕ compile-length f
          len-curry = compile-length-correct (curry f)

          -- 19 ≤ 19 + compile-length f
          nineteen-le-curry : 19 ≤ 19 +ℕ compile-length f
          nineteen-le-curry = m≤m+n 19 (compile-length f)

          -- 7 < 19 ≤ 19 + compile-length f = length curry-code
          seven-lt-curry : 7 < length curry-code
          seven-lt-curry = subst (7 <_) (sym len-curry)
                            (<-≤-trans seven-lt-nineteen nineteen-le-curry)

          -- length prog = length prefix + length (curry-code ++ suffix)
          len-prog-eq : length prog ≡ length prefix +ℕ length (curry-code ++ suffix)
          len-prog-eq = List-length-++ prefix

          -- length (curry-code ++ suffix) = length curry-code + length suffix
          len-curry-suffix : length (curry-code ++ suffix) ≡ length curry-code +ℕ length suffix
          len-curry-suffix = List-length-++ curry-code

          -- length curry-code ≤ length curry-code + length suffix = length (curry-code ++ suffix)
          curry-le-curry-suffix : length curry-code ≤ length (curry-code ++ suffix)
          curry-le-curry-suffix = subst (length curry-code ≤_) (sym len-curry-suffix)
                                        (m≤m+n (length curry-code) (length suffix))

          -- 7 < length curry-code ≤ length (curry-code ++ suffix)
          seven-lt-curry-suffix : 7 < length (curry-code ++ suffix)
          seven-lt-curry-suffix = <-≤-trans seven-lt-curry curry-le-curry-suffix

          -- Use +-monoʳ-< : i < j → n + i < n + j
          step1 : offset +ℕ 7 < offset +ℕ length (curry-code ++ suffix)
          step1 = +-monoʳ-< offset seven-lt-curry-suffix

          -- offset + length (curry-code ++ suffix) = length prog
          proof : offset +ℕ 7 < length prog
          proof = subst (offset +ℕ 7 <_) (sym len-prog-eq) step1

------------------------------------------------------------------------
-- Top-level entry point
------------------------------------------------------------------------

-- | Execute IR starting at position 0
run-ir-star : ∀ {i A B} (ir : IR i A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  StackDepth ir ≤ readReg (regs s) sp →
  ∃[ s' ] IRStarResult ir (compile-riscv ir) s s' x 0
run-ir-star ir x s h-false pc-eq a0-eq sp-bound =
  subst (λ prog → ∃[ s' ] IRStarResult ir prog s s' x 0)
        (++-identityʳ (compile-riscv ir))
        (run-ir-star-at-offset ir [] [] x s h-false pc-eq a0-eq sp-bound)
  where
    open import Data.List.Properties using (++-identityʳ)
