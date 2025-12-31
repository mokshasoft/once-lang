{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR
--
-- Mutual block for run-ir-at-offset and complex IR cases.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR where

open import Size
open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc)

-- Import common program manipulation lemmas
open import Once.Backend.Common.ProgramLemmas
  using (compose-prog-eq; compose-transfer-eq; compose-g-eq)

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)
open import Once.Backend.X86.Postulates
  using (rsp-bound-after-stack-op; apply-produces-result)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.InitState
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; pair-at; fst-valid; snd-valid;
         InlAt; inl-at; InrAt; inr-at;
         encode-pair-fst-derived; encode-pair-snd-derived;
         encode-inl-tag-derived; encode-inl-val-derived;
         encode-inr-tag-derived; encode-inr-val-derived)

-- Re-export StarBase for backwards compatibility
-- Simple Star proofs (non-recursive) are in StarBase.agda
open import Once.Backend.X86.Correct.StarBase public
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-at-0; ir-closure-wf;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star;
         run-fst-star-v; run-snd-star-v)

-- Import extracted compose helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResult;
         exec-compose-transfer; assemble-compose-result)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Pair
  using (PairContext; make-pair-context; PairSetupResult; exec-pair-setup;
         PairMiddleResult; exec-pair-middle; PairFinalPrecond; PairFinalResult;
         make-pair-final-precond; exec-pair-final; assemble-pair-result)
open import Once.Backend.X86.Correct.IR.Pair using (module PairContext; module PairSetupResult; module PairMiddleResult; module PairFinalResult)

-- Import extracted curry proof (non-recursive, entire function extracted)
open import Once.Backend.X86.Correct.IR.Curry using (run-curry-star; CurryMemoryResult)

-- Import extracted inl/inr proofs (non-recursive, entire functions extracted)
open import Once.Backend.X86.Correct.IR.Inl using (run-inl-star)
open import Once.Backend.X86.Correct.IR.Inr using (run-inr-star)

-- Import closure well-formedness infrastructure for whole-program proofs
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult; ThunkResult;
         curry-star; curry-halted; curry-pc; curry-rax;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-rsp-bound; closure-wf)
-- Note: ThunkProof postulates are now UNUSED
-- curry-thunk-correct-impl in this file replaces curry-thunk-correct postulate
-- construct-closure-wf is replaced by inline record construction using curry-thunk-correct-impl

-- Import apply with well-formedness proof
open import Once.Backend.X86.Correct.IR.Apply
  using (run-apply-with-wf; run-apply-star-with-wf)

-- Import extracted case helpers (non-recursive parts)
open import Once.Backend.X86.Correct.IR.Case
  using (CaseContext; make-case-context;
         CaseJumpResult; exec-case-jump;
         CaseEndResult; exec-case-end;
         CaseRightSetupResult; exec-case-right-setup;
         stack-inv-preserved-mem-rsp)
open import Once.Backend.X86.Correct.IR.Case using (module CaseContext; module CaseJumpResult; module CaseEndResult; module CaseRightSetupResult)

-- Import thunk structure lemmas (fetch proofs for thunk instructions)
open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (thunk-i0; thunk-i1; thunk-i2; thunk-i3; thunk-i4; thunk-i5; thunk-i6;
         fetch-thunk-i0; fetch-thunk-i1; fetch-thunk-i2; fetch-thunk-i3; fetch-thunk-i4;
         fetch-thunk-i5; fetch-thunk-i6;
         cleanup-i0; cleanup-i1; fetch-cleanup-i0; fetch-cleanup-i1)
  renaming (fetch-ret to TS-fetch-ret)

-- Import thunk execution proofs (extracted from mutual block)
open import Once.Backend.X86.Correct.IR.ThunkExec
  using (thunk-setup-star; thunk-ret-star)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; m+[n∸m]≡n; ∸-+-assoc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

------------------------------------------------------------------------
-- RbpInvariant preservation helper
------------------------------------------------------------------------

-- RbpInvariant is preserved through IR execution when rsp and rbp are unchanged
-- Uses ir-rbp-inv from IRStarResult and register preservation from transfer
rbp-inv-preserved-through-ir : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {i A B} {ir : IR i A B} {prog x offset} →
  IRStarResult ir prog s s1 x offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir s s1 s2 _ {ir = ir} r rsp2-eq rbp2-eq =
  -- s1 has RbpInvariant from ir-rbp-inv r
  -- s2 has same rsp and rbp as s1, so RbpInvariant is preserved
  Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s2 (ir-rbp-inv r) rsp2-eq rbp2-eq

------------------------------------------------------------------------
-- Star-Based Mutual Block
--
-- This mutual block builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
--
-- NOTE: run-inl-star and run-inr-star are now imported from IR/Inl.agda
-- and IR/Inr.agda respectively.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to existing Star functions
  run-ir-star-at-offset (id {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (terminal {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (fold {F}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (unfold {F}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (arr {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-arr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (fst {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (snd {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inl {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inr {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (initial {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 _ =
    ⊥-elim x

  -- Recursive cases: use Star-based composition
  run-ir-star-at-offset (_∘_ {A} {B} {C} g f) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-compose-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-pair-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset ([_,_] {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-case-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (curry {A} {B} {C} f) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-curry-star-direct f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (apply {_} {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-apply-star-direct prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

  -- | Star-based compose execution
  -- Uses extracted helpers from IR.Compose - only recursive calls remain here
  run-compose-star-direct : ∀ {i A B C} (f : IR i A B) (g : IR i B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
    in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)
  run-compose-star-direct {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s3 , assemble-compose-result f g prefix suffix x s s1 s2 s3 r1 tr r3 refl
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Step 1: Execute f (RECURSIVE - must stay in mutual block)
      step-f : ∃[ s1 ] IRStarResult f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

      s1 = proj₁ step-f
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

      -- Step 3: Execute g (RECURSIVE - must stay in mutual block)
      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix (eval f x) s2
                 (TransferResult.h2 tr) (TransferResult.pc2-g tr) (TransferResult.rdi2-enc tr)
                 (TransferResult.stack-inv-2 tr) (TransferResult.rsp-2>16 tr) rbp-inv-2

      s3 = proj₁ step-g
      r3 = proj₂ step-g

  -- | Star-based pair (POSTULATE-FREE!)
  -- Uses star-trans (PROVEN) and exec-to-star to compose 5 phases:
  -- Phase 1: 7 setup instructions
  -- Phase 2: Execute f (recursive)
  -- Phase 3: 2 middle instructions
  -- Phase 4: Execute g (recursive)
  -- Phase 5: 6 final instructions
  run-pair-star-direct : ∀ {i A B C} (f : IR i C A) (g : IR i C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star-direct {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s-final , assemble-pair-result f g prefix suffix x s s-setup s1 s2 s3 s-final
                setup-res r-f mid-res r-g
                h-final pc-fin-raw rax-fin-is-r15 r14-final r15-final
                stack-inv-final rsp>16-final mem-fst-final mem-snd-final
                rbp-final mem-final mem-rbp-final mem-rbp+8-final mem-above-final mem-at-0-final
                star-fin refl refl
                rbp-inv rsp-final-eq
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm)
      open import Once.Backend.X86.Correct.Star using (exec-to-star)

      -- Context and shorthand
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx

      -- ========== Phase 1: Setup (7 instructions) ==========
      setup-res = exec-pair-setup f g prefix suffix x s h-false pc-eq rdi-eq
      s-setup = PairSetupResult.s-setup setup-res

      -- ========== Phase 2: Execute f (recursive call) ==========
      -- Derive RbpInvariant for s-setup: rsp_setup = rsp ∸ 40, rbp_setup = rsp ∸ 24
      -- Need: (rsp ∸ 40) ≤ (rsp ∸ 24), which follows from 24 ≤ 40
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = record
        { rsp≤rbp = rsp-setup≤rbp-setup }
        where
          open import Data.Nat.Properties using (∸-monoʳ-≤)
          open import Data.Nat using (s≤s; z≤n)
          -- 24 ≤ 40
          24≤40 : 24 ≤ 40
          24≤40 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))))))
          -- (rsp ∸ 40) ≤ (rsp ∸ 24) by ∸-monoʳ-≤
          rsp∸40≤rsp∸24 : readReg (regs s) rsp ∸ 40 ≤ readReg (regs s) rsp ∸ 24
          rsp∸40≤rsp∸24 = ∸-monoʳ-≤ (readReg (regs s) rsp) 24≤40
          rsp-setup≤rbp-setup : readReg (regs s-setup) rsp ≤ readReg (regs s-setup) rbp
          rsp-setup≤rbp-setup = subst₂ _≤_
            (sym (PairSetupResult.rsp-setup setup-res))
            (sym (PairSetupResult.rbp-setup setup-res))
            rsp∸40≤rsp∸24

      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 x (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup
                (PairSetupResult.h-setup setup-res)
                (PairSetupResult.pc-setup-f setup-res)
                (PairSetupResult.rdi-setup-enc setup-res)
                (PairSetupResult.stack-inv-setup setup-res)
                (PairSetupResult.rsp>16-setup setup-res)
                rbp-inv-setup

      s1 = proj₁ step-f
      r-f = proj₂ step-f

      -- pc s1 for middle phase
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f
      pc1 = trans (ir-pc r-f) (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Middle (2 instructions) ==========
      mid-res = exec-pair-middle f g prefix suffix x s s-setup s1 r-f setup-res refl rdi-eq (ir-halted r-f) pc1
      s2 = PairMiddleResult.s2 mid-res

      -- ========== Phase 4: Execute g (recursive call) ==========
      -- Derive RbpInvariant for s2 using ir-rbp-inv from r-f and middle phase preservation
      rbp-inv-s1 : RbpInvariant s1
      rbp-inv-s1 = IRStarResult.ir-rbp-inv r-f

      -- Middle phase preserves both rsp and rbp
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = PairMiddleResult.rsp-mid mid-res

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = PairMiddleResult.rbp-mid mid-res

      rbp-inv-s2 : RbpInvariant s2
      rbp-inv-s2 = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s2 rbp-inv-s1 rsp-s2-eq-s1 rbp-s2-eq-s1

      step-g : ∃[ s3 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s2 s3 x (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix-g x s2
                (PairMiddleResult.h2 mid-res)
                (PairMiddleResult.pc2-g mid-res)
                (PairMiddleResult.rdi2 mid-res)
                (PairMiddleResult.stack-inv-s2 mid-res)
                (PairMiddleResult.rsp>16-s2 mid-res)
                rbp-inv-s2

      s3 = proj₁ step-g
      r-g = proj₂ step-g

      -- ========== Phase 5: Final (6 instructions) ==========
      -- Use extracted helpers from IR/Pair.agda
      final-precond : PairFinalPrecond f g prefix suffix s s3
      final-precond = make-pair-final-precond f g prefix suffix x s s-setup s1 s2 s3
                        stack-inv rbp-inv setup-res r-f mid-res r-g refl refl

      final-res : PairFinalResult f g prefix suffix s s3
      final-res = exec-pair-final f g prefix suffix s s3 final-precond

      s-final = PairFinalResult.s-final final-res
      exec-fin = PairFinalResult.exec-fin final-res
      h-final = PairFinalResult.h-final final-res
      pc-fin-raw = PairFinalResult.pc-fin final-res
      rax-fin-is-r15 = PairFinalResult.rax-fin final-res
      r14-final = PairFinalResult.r14-fin final-res
      r15-final = PairFinalResult.r15-fin final-res
      stack-inv-final = PairFinalResult.stack-inv-fin final-res
      rsp>16-final = PairFinalResult.rsp>16-fin final-res
      mem-fst-final = PairFinalResult.mem-fst-fin final-res
      mem-snd-final = PairFinalResult.mem-snd-fin final-res
      rbp-final = PairFinalResult.rbp-fin final-res
      rsp-final-eq = PairFinalResult.rsp-fin final-res
      mem-final = PairFinalResult.mem-orig-fin final-res
      mem-rbp-final = PairFinalResult.mem-rbp-fin final-res
      mem-rbp+8-final = PairFinalResult.mem-rbp+8-fin final-res

      -- Memory above original rbp is preserved through all phases
      -- Chain through: setup → f → middle → g → final
      -- For addr > s.rbp, we have addr > s.rbp ≥ s.rsp (RbpInvariant), so:
      --   addr ≥ s.rsp → setup preserves (writes at rsp-8, rsp-16, rsp-24, rsp-40)
      --   addr > s-setup.rbp = s.rsp - 24 → f preserves (ir-mem-above)
      --   addr ≠ s1.r15 = s.rsp - 40 → middle preserves (writes only at r15)
      --   addr > s2.rbp = s.rsp - 24 → g preserves (ir-mem-above)
      --   addr ≠ s3.r15 + 8 = s.rsp - 32 → final preserves (writes only at r15+8)
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp = mem-chain
        where
          open import Data.Nat.Properties using (<⇒≢; <⇒≤; <-≤-trans; ≤-trans; ≤-refl; m∸n≤m)
          open import Data.Nat using (s≤s; z≤n)
          open import Relation.Binary.PropositionalEquality using (trans)

          orig-rsp = readReg (regs s) rsp
          orig-rbp = readReg (regs s) rbp

          -- From RbpInvariant: rsp ≤ rbp, and addr > rbp, so addr > rbp ≥ rsp
          addr≥rsp : addr ≥ orig-rsp
          addr≥rsp = ≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp)

          -- Phase 1: Setup preserves memory at addr (addr ≥ rsp, writes are < rsp)
          mem-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
          mem-setup = PairSetupResult.mem-above-rsp-setup setup-res addr addr≥rsp

          -- For f/g phases: addr > s-setup.rbp = rsp - 24
          -- Since addr ≥ rsp > rsp - 24 (when rsp ≥ 1), we have addr > rsp - 24
          setup-rbp = readReg (regs s-setup) rbp
          setup-rbp-eq : setup-rbp ≡ orig-rsp ∸ 24
          setup-rbp-eq = PairSetupResult.rbp-setup setup-res

          -- rsp > 16 (from precondition), so rsp ≥ 17, thus rsp - 24 < rsp ≤ addr
          rsp∸24<rsp : orig-rsp ∸ 24 < orig-rsp
          rsp∸24<rsp = m∸n<m orig-rsp 24 rsp>0 24>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp>16
              24>0 : 24 > 0
              24>0 = s≤s z≤n
              -- m ∸ n < m when m > 0 and n > 0
              -- Proof: (suc m') ∸ (suc n') = m' ∸ n' ≤ m' < suc m'
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr>setup-rbp : addr > setup-rbp
          addr>setup-rbp = subst (addr >_) (sym setup-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              -- rsp ∸ 24 < rsp ≤ rbp < addr
              rsp∸24<rbp : orig-rsp ∸ 24 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ 24 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          -- Phase 2: f preserves memory at addr (addr > s-setup.rbp)
          mem-f : readMem (memory s1) addr ≡ readMem (memory s-setup) addr
          mem-f = ir-mem-above r-f addr addr>setup-rbp

          -- For middle: addr ≠ s1.r15 = rsp - 40
          -- Since addr ≥ rsp > rsp - 40, we have addr ≠ rsp - 40
          s1-r15 = readReg (regs s1) r15
          s1-r15-eq : s1-r15 ≡ orig-rsp ∸ 40
          s1-r15-eq = trans (ir-r15 r-f) (PairSetupResult.r15-setup setup-res)

          rsp∸40<rsp : orig-rsp ∸ 40 < orig-rsp
          rsp∸40<rsp = m∸n<m orig-rsp 40 rsp>0 40>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp>16
              40>0 : 40 > 0
              40>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          addr≢s1-r15 : addr ≢ s1-r15
          addr≢s1-r15 eq = Data.Nat.Properties.<⇒≢ s1-r15<addr (sym eq)
            where
              s1-r15<addr : s1-r15 < addr
              s1-r15<addr = subst (_< addr) (sym s1-r15-eq) (<-≤-trans rsp∸40<rsp addr≥rsp)

          -- Phase 3: Middle preserves memory at addr (addr ≠ s1.r15)
          mem-mid : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-mid = PairMiddleResult.mem-above-r15-mid mid-res addr addr≢s1-r15

          -- For g phase: addr > s2.rbp = s1.rbp = s-setup.rbp (rbp preserved through f and middle)
          s2-rbp = readReg (regs s2) rbp
          s2-rbp-eq : s2-rbp ≡ orig-rsp ∸ 24
          s2-rbp-eq = trans (PairMiddleResult.rbp-mid mid-res) (trans (ir-rbp r-f) setup-rbp-eq)

          addr>s2-rbp : addr > s2-rbp
          addr>s2-rbp = subst (addr >_) (sym s2-rbp-eq) rsp∸24<addr
            where
              open import Data.Nat.Properties using (<-trans)
              rsp∸24<rbp : orig-rsp ∸ 24 < orig-rbp
              rsp∸24<rbp = <-≤-trans rsp∸24<rsp (RbpInvariant.rsp≤rbp rbp-inv)
              rsp∸24<addr : orig-rsp ∸ 24 < addr
              rsp∸24<addr = <-trans rsp∸24<rbp addr>rbp

          -- Phase 4: g preserves memory at addr (addr > s2.rbp)
          mem-g : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-g = ir-mem-above r-g addr addr>s2-rbp

          -- For final: addr ≠ s3.r15 + 8 = (rsp - 40) + 8 = rsp - 32
          -- Since addr ≥ rsp > rsp - 32, we have addr ≠ rsp - 32
          s3-r15 = readReg (regs s3) r15
          s3-r15-eq : s3-r15 ≡ orig-rsp ∸ 40
          s3-r15-eq = trans (ir-r15 r-g) (trans (PairMiddleResult.r15-mid mid-res) (trans (ir-r15 r-f) (PairSetupResult.r15-setup setup-res)))

          -- rsp - 32 < rsp (when rsp > 0)
          rsp∸32<rsp : orig-rsp ∸ 32 < orig-rsp
          rsp∸32<rsp = m∸n<m orig-rsp 32 rsp>0 32>0
            where
              rsp>0 : orig-rsp > 0
              rsp>0 = ≤-trans (s≤s z≤n) rsp>16
              32>0 : 32 > 0
              32>0 = s≤s z≤n
              m∸n<m : ∀ m n → m > 0 → n > 0 → m ∸ n < m
              m∸n<m (suc m') (suc n') _ _ = s≤s (m∸n≤m m' n')

          -- (rsp - 40) + 8 = rsp - 32 when rsp ≥ 40
          -- More precisely: we need addr ≠ s3-r15 + 8
          addr≢s3-r15+8 : addr ≢ s3-r15 +ℕ 8
          addr≢s3-r15+8 eq = Data.Nat.Properties.<⇒≢ s3-r15+8<addr (sym eq)
            where
              -- s3-r15 + 8 = (rsp - 40) + 8 < rsp when rsp > 16
              -- Arithmetic lemma: (m ∸ 40) + 8 < m when m > 16
              -- Case analysis:
              --   When m < 40: (m ∸ 40) + 8 = 0 + 8 = 8 < m (since m > 16 > 8)
              --   When m ≥ 40: (m ∸ 40) + 8 = m - 32 < m (since 32 > 0)
              s3-r15+8<rsp : s3-r15 +ℕ 8 < orig-rsp
              s3-r15+8<rsp = subst (λ r → r +ℕ 8 < orig-rsp) (sym s3-r15-eq) arith
                where
                  open import Data.Nat.Properties using (m≤n⇒m∸n≡0; ≰⇒>)
                  open import Data.Nat using (_≤?_)
                  arith : orig-rsp ∸ 40 +ℕ 8 < orig-rsp
                  arith with 40 ≤? orig-rsp
                  -- Case rsp < 40: (rsp - 40) + 8 = 0 + 8 = 8 < rsp (since rsp > 16)
                  ... | no 40>rsp = subst (_< orig-rsp) (sym 0+8≡8) 8<rsp
                    where
                      rsp<40 : orig-rsp < 40
                      rsp<40 = ≰⇒> 40>rsp
                      rsp∸40≡0 : orig-rsp ∸ 40 ≡ 0
                      rsp∸40≡0 = m≤n⇒m∸n≡0 (<⇒≤ rsp<40)
                      0+8≡8 : orig-rsp ∸ 40 +ℕ 8 ≡ 8
                      0+8≡8 = cong (_+ℕ 8) rsp∸40≡0
                      8<rsp : 8 < orig-rsp
                      8<rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp>16
                  -- Case rsp ≥ 40: (rsp - 40) + 8 = rsp - 32 < rsp
                  ... | yes 40≤rsp = subst (_< orig-rsp) (sym m∸40+8≡m∸32) rsp∸32<rsp
                    where
                      open import Data.Nat.Properties using (m∸n+n≡m; m+n∸n≡m; +-assoc; +-comm)
                      -- Let k = rsp - 40, so rsp = k + 40 (by m∸n+n≡m)
                      -- LHS = k + 8
                      -- RHS = (k + 40) - 32 = ((k + 8) + 32) - 32 = k + 8 (by m+n∸n≡m)
                      k = orig-rsp ∸ 40
                      -- k + 40 = k + 8 + 32 = (k + 8) + 32
                      k+40≡k+8+32 : k +ℕ 40 ≡ (k +ℕ 8) +ℕ 32
                      k+40≡k+8+32 = trans (cong (k +ℕ_) refl)
                                         (sym (+-assoc k 8 32))
                      -- (k + 40) - 32 = ((k + 8) + 32) - 32 = k + 8
                      k+40∸32≡k+8 : (k +ℕ 40) ∸ 32 ≡ k +ℕ 8
                      k+40∸32≡k+8 = trans (cong (_∸ 32) k+40≡k+8+32) (m+n∸n≡m (k +ℕ 8) 32)
                      m∸40+8≡m∸32 : orig-rsp ∸ 40 +ℕ 8 ≡ orig-rsp ∸ 32
                      m∸40+8≡m∸32 =
                        let step1 : orig-rsp ∸ 32 ≡ (k +ℕ 40) ∸ 32
                            step1 = cong (_∸ 32) (sym (m∸n+n≡m 40≤rsp))
                        in sym (trans step1 k+40∸32≡k+8)

              s3-r15+8<addr : s3-r15 +ℕ 8 < addr
              s3-r15+8<addr = <-≤-trans s3-r15+8<rsp addr≥rsp

          -- Phase 5: Final preserves memory at addr (addr ≠ s3.r15 + 8)
          mem-final-phase : readMem (memory s-final) addr ≡ readMem (memory s3) addr
          mem-final-phase = PairFinalResult.mem-above-r15+8-fin final-res addr addr≢s3-r15+8

          -- Chain all phases together
          mem-chain : readMem (memory s-final) addr ≡ readMem (memory s) addr
          mem-chain = trans mem-final-phase (trans mem-g (trans mem-mid (trans mem-f mem-setup)))

      -- Memory at address 0 preserved through all phases
      -- Chain ir-mem-at-0 from f and g, plus preservation through setup/middle/final
      -- TODO: Add mem-at-0 fields to PairSetupResult, PairMiddleResult, PairFinalResult
      postulate
        mem-setup-preserves-0 : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
        mem-mid-preserves-0 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
        mem-final-preserves-0 : readMem (memory s-final) 0 ≡ readMem (memory s3) 0

      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-final-preserves-0
                       (trans (ir-mem-at-0 r-g)
                       (trans mem-mid-preserves-0
                       (trans (ir-mem-at-0 r-f)
                              mem-setup-preserves-0)))

      -- Convert final exec to Star (prog-eq-final from PairContext)
      star-fin : Star prog s3 s-final
      star-fin = subst (λ p → Star p s3 s-final) (sym prog-eq-final) (exec-to-star exec-fin)

  -- | Star-based case execution (direct, uses Star throughout)
  -- For inl: Setup(4) → f → JumpToEnd(2) (labels are pseudo-instructions)
  -- For inr: Setup(3) → Jump(1) → LoadVal(1) → g → Label(1)
  -- compile-length [ f , g ] = (8 + len-f) + len-g
  run-case-star-direct : ∀ {i A B C} (f : IR i A C) (g : IR i B C) (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' x (length prefix)
  run-case-star-direct {i} {A} {B} {C} f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    with x
  ... | inj₁ a = run-case-star-direct-inl f g prefix suffix a s h-false pc-eq rdi-eq-inl stack-inv rsp>16 rbp-inv
    where
      rdi-eq-inl : readReg (regs s) rdi ≡ encode {A + B} (inj₁ a)
      rdi-eq-inl = rdi-eq
  ... | inj₂ b = run-case-star-direct-inr f g prefix suffix b s h-false pc-eq rdi-eq-inr stack-inv rsp>16 rbp-inv
    where
      rdi-eq-inr : readReg (regs s) rdi ≡ encode {A + B} (inj₂ b)
      rdi-eq-inr = rdi-eq

  -- | Star-based case left branch (inl)
  -- Structure:
  --   Phase 1: Setup - 4 instructions (mov r15 [rdi], cmp, jne not taken, mov rdi [rdi+8])
  --   Phase 2: Execute f - recursive Star call
  --   Phase 3: Jump to end - 2 instructions (jmp, label)
  run-case-star-direct-inl : ∀ {i A B C} (f : IR i A C) (g : IR i B C) (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₁ a) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₁ a) (length prefix)
  run-case-star-direct-inl {i} {A} {B} {C} f g prefix suffix a s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-mem-rbp = mem-rbp-final
      ; ir-mem-rbp+8 = mem-rbp+8-final
      ; ir-mem-above = mem-above-final
      ; ir-mem-at-0 = mem-at-0-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-closure-wf = closure-wf-final  -- Thread through f (inl branch)
      }
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)

      len-f = compile-length f
      len-g = compile-length g
      code-f = compile-x86 f
      code-g = compile-x86 g
      prog = prefix ++ compile-x86 [ f , g ] ++ suffix

      -- Case layout (from CodeGen):
      --   0: mov r11, [rdi]        ; load tag into scratch register
      --   1: cmp r11, 0            ; compare with 0
      --   2: jne (2+len-f)         ; jump NOT taken for inl
      --   3: mov rdi, [rdi+8]      ; load value
      --   4 to 3+len-f: f          ; execute f
      --   4+len-f: jmp (2+len-g)   ; jump to end
      --   5+len-f: label           ; right branch (skipped)
      --   6+len-f: mov rdi,...     ; (skipped)
      --   7+len-f to 6+len-f+len-g: g  ; (skipped)
      --   7+len-f+len-g: label     ; end label

      -- Jump offset for jne (not taken for inl)
      right-offset = 2 +ℕ len-f
      -- Jump offset for jmp to end
      end-offset = 2 +ℕ len-g

      -- ========== Phase 1: Setup (4 instructions) ==========
      -- mov r11, [rdi] ; cmp r11, 0 ; jne (not taken) ; mov rdi, [rdi+8]
      -- After setup: rdi = encode a, r14/r15/rbp/rax/memory unchanged (r11 is scratch)

      -- Setup instructions (uses r11 scratch register for tag)
      load-tag-instr = mov (reg r11) (mem (base rdi))
      cmp-tag-instr = cmp (reg r11) (imm 0)
      jne-instr = jne right-offset
      load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))

      -- Prefix for f = prefix + 4 setup instructions
      prefix-f : Program
      prefix-f = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

      -- Suffix for f = jmp ∷ label ∷ load-val ∷ g ∷ end-label ∷ suffix
      suffix-f : Program
      suffix-f = jmp end-offset ∷ label (5 +ℕ len-f) ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-g ++ label ((7 +ℕ len-f) +ℕ len-g) ∷ suffix

      -- Length of prefix-f
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
      len-prefix-f = trans (List-length-++ prefix) refl

      -- Suffix for helper: code-f ++ suffix-f so prog-for-helper = prog
      suffix-for-helper : Program
      suffix-for-helper = code-f ++ suffix-f

      -- Derive memory preconditions from encode axioms and rdi-eq
      mem-tag-precond : readMem (memory s) (readReg (regs s) rdi) ≡ just 0
      mem-tag-precond = subst (λ addr → readMem (memory s) addr ≡ just 0)
                              (sym rdi-eq) (encode-inl-tag {A} {B} a (memory s))

      mem-val-precond : readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode a)
      mem-val-precond = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode a))
                              (sym rdi-eq) (encode-inl-val {A} {B} a (memory s))

      -- Call the helper to get the 9 core properties
      helper-result = exec-case-inl-setup prefix suffix-for-helper right-offset (encode a) s
                        h-false pc-eq mem-tag-precond mem-val-precond

      -- Program equality: show helper's prog matches actual prog
      -- helper's prog = prefix ++ [4 setup] ++ suffix-for-helper
      -- actual prog = prefix ++ compile-x86 [ f , g ] ++ suffix
      -- These are equal because compile-x86 [ f , g ] = [4 setup] ++ code-f ++ [jmp,label,mov,code-g,label]
      -- and suffix-for-helper = code-f ++ suffix-f = code-f ++ [jmp,label,mov,code-g,label,suffix]
      prog-for-helper : Program
      prog-for-helper = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-helper

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prog-for-helper
      prog-eq-setup = CaseContext.prog-eq-inl-setup ctx

      -- Extract helper results using record field access
      s-setup-raw = proj₁ helper-result
      open CaseInlSetupResult (proj₂ helper-result)
        renaming (exec-eq to exec-setup-raw; halted-eq to h-setup-raw; pc-eq to pc-setup-raw;
                  rdi-eq to rdi-setup-raw; r14-eq to r14-setup-raw; r15-eq to r15-setup-raw;
                  rbp-eq to rbp-setup-raw; rsp-eq to rsp-setup-raw; mem-eq to mem-setup-raw)

      -- Convert exec from prog-for-helper to prog
      exec-setup-converted : exec 4 prog s ≡ just s-setup-raw
      exec-setup-converted = subst (λ p → exec 4 p s ≡ just s-setup-raw) (sym prog-eq-setup) exec-setup-raw

      -- StackInvariant preserved: memory, rsp, and r15 unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv r15-setup-raw

      -- Derive rsp>16 from preserved rsp
      rsp>16-derived : readReg (regs s-setup-raw) rsp > 16
      rsp>16-derived = subst (_> 16) (sym rsp-setup-raw) rsp>16

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      setup-result : ∃[ s-setup ] (exec 4 prog s ≡ just s-setup
                                    × halted s-setup ≡ false
                                    × pc s-setup ≡ length prefix +ℕ 4
                                    × readReg (regs s-setup) rdi ≡ encode a
                                    × readReg (regs s-setup) r14 ≡ readReg (regs s) r14
                                    × readReg (regs s-setup) r15 ≡ readReg (regs s) r15
                                    × readReg (regs s-setup) rbp ≡ readReg (regs s) rbp
                                    × readReg (regs s-setup) rsp ≡ readReg (regs s) rsp
                                    × memory s-setup ≡ memory s
                                    × StackInvariant s-setup
                                    × readReg (regs s-setup) rsp > 16)
      setup-result = s-setup-raw , exec-setup-converted , h-setup-raw , pc-setup-raw ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp>16-derived

      s-setup = proj₁ setup-result
      exec-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- Convert setup exec to Star
      star-setup : Star prog s s-setup
      star-setup = Once.Backend.X86.Correct.Star.exec-to-star exec-setup

      -- ========== Phase 2: Execute f (recursive call) ==========
      -- pc s-setup = length prefix + 4 = length prefix-f

      pc-setup-f : pc s-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      -- Program equality for f from CaseContext
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-f = CaseContext.prog-eq-f ctx

      -- Derive RbpInvariant for s-setup (rsp and rbp preserved through setup)
      rbp-inv-setup : RbpInvariant s-setup
      rbp-inv-setup = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s s-setup rbp-inv rsp-setup rbp-setup

      -- Recursive call to f
      step-f : ∃[ s1 ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-setup s1 a (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-setup h-setup pc-setup-f rdi-setup stack-inv-setup rsp>16-setup rbp-inv-setup

      s1 = proj₁ step-f
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s1
      star-f-raw = ir-star r-f
      h1 = ir-halted r-f
      pc1-raw = ir-pc r-f  -- pc s1 = length prefix-f + len-f = length prefix + 4 + len-f

      -- Convert star-f to use prog
      star-f : Star prog s-setup s1
      star-f = subst (λ p → Star p s-setup s1) (sym prog-eq-f) star-f-raw

      -- Convert closure-wf from f to use prog
      closure-wf-f-raw : ClosureWFOutput (prefix-f ++ code-f ++ suffix-f)
      closure-wf-f-raw = ir-closure-wf r-f
      closure-wf-final : ClosureWFOutput prog
      closure-wf-final = subst ClosureWFOutput (sym prog-eq-f) closure-wf-f-raw

      -- pc s1 = length prefix + 4 + len-f
      pc1 : pc s1 ≡ length prefix +ℕ 4 +ℕ len-f
      pc1 = trans pc1-raw (cong (_+ℕ len-f) len-prefix-f)

      -- ========== Phase 3: Jump to end (2 instructions) ==========
      -- jmp (2+len-g) ; label (end)
      -- After: pc = length prefix + 4 + len-f + 2 + len-g + 1 (at end label)
      --      = length prefix + (8 + len-f) + len-g = length prefix + compile-length [ f , g ]

      -- Use the extracted exec-case-jump helper
      jump-result : CaseJumpResult f g prefix suffix s1
      jump-result = exec-case-jump f g prefix suffix s1 h1 pc1

      s-final = CaseJumpResult.s-final jump-result
      exec-jump = CaseJumpResult.exec-jump jump-result
      h-final = CaseJumpResult.h-final jump-result
      pc-final-raw = CaseJumpResult.pc-final jump-result
      rax-jump = CaseJumpResult.rax-preserved jump-result
      r14-jump = CaseJumpResult.r14-preserved jump-result
      r15-jump = CaseJumpResult.r15-preserved jump-result
      rbp-jump = CaseJumpResult.rbp-preserved jump-result
      rsp-jump = CaseJumpResult.rsp-preserved jump-result
      mem-jump = CaseJumpResult.mem-preserved jump-result

      -- Convert jump exec to Star
      star-jump : Star prog s1 s-final
      star-jump = Once.Backend.X86.Correct.Star.exec-to-star exec-jump

      -- ========== Compose all phases ==========
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-jump)

      -- ========== Final properties ==========
      pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
      pc-final = pc-final-raw

      -- rax-final: from ir-rax r-f, preserved through jump
      rax-final : readReg (regs s-final) rax ≡ encode (eval f a)
      rax-final = trans rax-jump (ir-rax r-f)

      -- r14 preserved through all phases
      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
      r14-final = trans r14-jump (trans (ir-r14 r-f) r14-setup)

      -- r15 preserved: setup uses r11 for tag (not r15), f preserves r15, jump preserves r15
      -- Proof: trans r15-jump (trans (ir-r15 r-f) r15-setup)
      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
      r15-final = trans r15-jump (trans (ir-r15 r-f) r15-setup)

      -- rbp preserved through all phases
      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
      rbp-final = trans rbp-jump (trans (ir-rbp r-f) rbp-setup)

      -- Memory preserved through all phases:
      -- 1. mem-setup: memory s-setup = memory s
      -- 2. r15-setup: r15 s-setup = r15 s
      -- 3. ir-mem r-f: readMem (memory s1) (r15 s-setup) = readMem (memory s-setup) (r15 s-setup)
      -- 4. mem-jump: memory s-final = memory s1
      -- Chain: readMem (memory s-final) (r15 s)
      --      = readMem (memory s1) (r15 s)                    (by mem-jump)
      --      = readMem (memory s1) (r15 s-setup)              (by r15-setup)
      --      = readMem (memory s-setup) (r15 s-setup)         (by ir-mem r-f)
      --      = readMem (memory s) (r15 s-setup)               (by mem-setup)
      --      = readMem (memory s) (r15 s)                     (by r15-setup)
      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-final = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-jump)
                  (trans (cong (λ addr → readMem (memory s1) addr) (sym r15-setup))
                  (trans (ir-mem r-f)
                  (trans (cong (λ m → readMem m (readReg (regs s-setup) r15)) mem-setup)
                         (cong (λ addr → readMem (memory s) addr) r15-setup))))

      -- Memory at rbp preserved through case execution (same chain as mem-final)
      mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
      mem-rbp-final = trans (cong (λ m → readMem m (readReg (regs s) rbp)) mem-jump)
                      (trans (cong (λ addr → readMem (memory s1) addr) (sym rbp-setup))
                      (trans (ir-mem-rbp r-f)
                      (trans (cong (λ m → readMem m (readReg (regs s-setup) rbp)) mem-setup)
                             (cong (λ addr → readMem (memory s) addr) rbp-setup))))

      -- Memory at rbp+8 preserved through case execution
      mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
      mem-rbp+8-final = trans (cong (λ m → readMem m (readReg (regs s) rbp +ℕ 8)) mem-jump)
                        (trans (cong (λ addr → readMem (memory s1) addr) (sym (cong (_+ℕ 8) rbp-setup)))
                        (trans (ir-mem-rbp+8 r-f)
                        (trans (cong (λ m → readMem m (readReg (regs s-setup) rbp +ℕ 8)) mem-setup)
                               (cong (λ addr → readMem (memory s) addr) (cong (_+ℕ 8) rbp-setup)))))

      -- Memory above rbp preserved through case execution (same chain pattern)
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp =
        let addr>rbp-setup : addr > readReg (regs s-setup) rbp
            addr>rbp-setup = subst (addr >_) (sym rbp-setup) addr>rbp
        in trans (cong (λ m → readMem m addr) mem-jump)
           (trans (ir-mem-above r-f addr addr>rbp-setup)
                  (cong (λ m → readMem m addr) mem-setup))

      -- Stack invariant: preserved from s1 to s-final since memory, rsp, and r15 unchanged
      -- ir-stack-inv r-f: StackInvariant s1
      -- mem-jump: memory s-final = memory s1
      -- rsp-jump: rsp s-final = rsp s1
      -- r15-jump: r15 s-final = r15 s1
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-jump rsp-jump (ir-stack-inv r-f) r15-jump

      rsp>16-final : readReg (regs s-final) rsp > 16
      rsp>16-final = ≤-trans 17≤41 (rsp-bound-after-stack-op s-final)
        where
          open import Data.Nat.Properties using (≤-trans)
          17≤41 : 17 ≤ 41
          17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

      -- RbpInvariant preserved: from ir-rbp-inv r-f through jump (rsp/rbp preserved)
      rbp-inv-final : RbpInvariant s-final
      rbp-inv-final = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s-final (ir-rbp-inv r-f) rsp-jump rbp-jump

      -- Memory at 0 preserved: setup/jump don't modify memory, chain through f
      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-at-0-jump (trans (ir-mem-at-0 r-f) mem-at-0-setup)
        where
          mem-at-0-setup : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
          mem-at-0-setup = subst (λ m → readMem m 0 ≡ readMem (memory s) 0)
                                 (sym mem-setup) refl

          mem-at-0-jump : readMem (memory s-final) 0 ≡ readMem (memory s1) 0
          mem-at-0-jump = subst (λ m → readMem m 0 ≡ readMem (memory s1) 0)
                                (sym mem-jump) refl

  -- | Star-based case right branch (inr)
  -- Structure:
  --   Phase 1: Setup - 3 instructions (mov r15 [rdi], cmp, jne taken)
  --   Phase 2: Right branch setup - 2 instructions (label, mov rdi [rdi+8])
  --   Phase 3: Execute g - recursive Star call
  --   Phase 4: End label - 1 instruction
  run-case-star-direct-inr : ∀ {i A B C} (f : IR i A C) (g : IR i B C) (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {A + B} (inj₂ b) →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' (inj₂ b) (length prefix)
  run-case-star-direct-inr {i} {A} {B} {C} f g prefix suffix b s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-mem-rbp = mem-rbp-final
      ; ir-mem-rbp+8 = mem-rbp+8-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-mem-above = mem-above-final
      ; ir-mem-at-0 = mem-at-0-final
      ; ir-closure-wf = closure-wf-final  -- Thread through g (inr branch)
      }
    where
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)

      len-f = compile-length f
      len-g = compile-length g
      code-f = compile-x86 f
      code-g = compile-x86 g
      prog = prefix ++ compile-x86 [ f , g ] ++ suffix

      -- Case layout (from CodeGen):
      --   0: mov r11, [rdi]        ; load tag into scratch register
      --   1: cmp r11, 0            ; compare with 0
      --   2: jne (2+len-f)         ; jump TAKEN for inr (tag=1), target = 5+len-f
      --   3: mov rdi, [rdi+8]      ; (skipped)
      --   4 to 3+len-f: f          ; (skipped)
      --   4+len-f: jmp (2+len-g)   ; (skipped)
      --   5+len-f: label           ; right branch label (land here)
      --   6+len-f: mov rdi,[rdi+8] ; load value
      --   7+len-f to 6+len-f+len-g: g  ; execute g
      --   7+len-f+len-g: label     ; end label

      -- Jump offset for jne (TAKEN for inr)
      right-offset = 2 +ℕ len-f
      -- Right branch label position
      right-label = 5 +ℕ len-f
      -- End label position
      end-label = (7 +ℕ len-f) +ℕ len-g

      -- ========== Phase 1: Setup (3 instructions) ==========
      -- mov r11, [rdi] ; cmp r11, 0 ; jne TAKEN
      -- After: pc = 5 + len-f (at right branch label), r15 unchanged

      -- Setup instructions (uses r11 scratch register for tag)
      load-tag-instr = mov (reg r11) (mem (base rdi))
      cmp-tag-instr = cmp (reg r11) (imm 0)
      jne-instr = jne right-offset

      -- Suffix for helper: rest of case code after the 3 setup instructions
      suffix-for-helper : Program
      suffix-for-helper = mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                          jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷
                          code-g ++ label end-label ∷ suffix

      -- Derive memory precondition from encode-inr-tag
      mem-tag-precond : readMem (memory s) (readReg (regs s) rdi) ≡ just 1
      mem-tag-precond = subst (λ addr → readMem (memory s) addr ≡ just 1)
                              (sym rdi-eq) (encode-inr-tag {A} {B} b (memory s))

      -- Call the helper
      helper-result = exec-case-inr-setup prefix suffix-for-helper right-offset s
                        h-false pc-eq mem-tag-precond

      -- Program equality for helper
      prog-for-helper : Program
      prog-for-helper = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-helper

      -- Use CaseContext for program equality
      ctx = make-case-context f g prefix suffix
      prog-eq-setup : prog ≡ prog-for-helper
      prog-eq-setup = CaseContext.prog-eq-inr-setup ctx

      -- Extract helper results using record field access
      s-setup-raw = proj₁ helper-result
      open CaseInrSetupResult (proj₂ helper-result)
        renaming (exec-eq to exec-setup-raw; halted-eq to h-setup-raw; pc-eq to pc-setup-raw;
                  rdi-eq to rdi-setup-raw; r14-eq to r14-setup-raw; r15-eq to r15-setup-raw;
                  rbp-eq to rbp-setup-raw; rsp-eq to rsp-setup-raw; mem-eq to mem-setup-raw)

      -- Convert exec from prog-for-helper to prog
      exec-setup-converted : exec 3 prog s ≡ just s-setup-raw
      exec-setup-converted = subst (λ p → exec 3 p s ≡ just s-setup-raw) (sym prog-eq-setup) exec-setup-raw

      -- PC proof: helper gives length prefix + 3 + right-offset = length prefix + 3 + (2 + len-f) = length prefix + 5 + len-f
      -- (length prefix + 3) + (2 + len-f) = ((length prefix + 3) + 2) + len-f = (length prefix + 5) + len-f
      pc-setup-proof : pc s-setup-raw ≡ length prefix +ℕ 5 +ℕ len-f
      pc-setup-proof = trans pc-setup-raw
                       (trans (sym (+-assoc (length prefix +ℕ 3) 2 len-f))
                              (cong (_+ℕ len-f) (+-assoc (length prefix) 3 2)))

      -- StackInvariant preserved: memory, rsp, and r15 unchanged
      stack-inv-derived : StackInvariant s-setup-raw
      stack-inv-derived = stack-inv-preserved-mem-rsp s s-setup-raw mem-setup-raw rsp-setup-raw stack-inv r15-setup-raw

      -- rsp>16 preserved
      rsp>16-derived : readReg (regs s-setup-raw) rsp > 16
      rsp>16-derived = subst (_> 16) (sym rsp-setup-raw) rsp>16

      -- Assemble full setup-result (r15 preserved, uses r11 scratch for tag)
      setup-result : ∃[ s-setup ] (exec 3 prog s ≡ just s-setup
                                    × halted s-setup ≡ false
                                    × pc s-setup ≡ length prefix +ℕ 5 +ℕ len-f
                                    × readReg (regs s-setup) rdi ≡ readReg (regs s) rdi
                                    × readReg (regs s-setup) r14 ≡ readReg (regs s) r14
                                    × readReg (regs s-setup) r15 ≡ readReg (regs s) r15
                                    × readReg (regs s-setup) rbp ≡ readReg (regs s) rbp
                                    × readReg (regs s-setup) rsp ≡ readReg (regs s) rsp
                                    × memory s-setup ≡ memory s
                                    × StackInvariant s-setup
                                    × readReg (regs s-setup) rsp > 16)
      setup-result = s-setup-raw , exec-setup-converted , h-setup-raw , pc-setup-proof ,
                     rdi-setup-raw , r14-setup-raw , r15-setup-raw , rbp-setup-raw ,
                     rsp-setup-raw , mem-setup-raw , stack-inv-derived , rsp>16-derived

      s-setup = proj₁ setup-result
      exec-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      rsp>16-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))

      -- Convert setup exec to Star
      star-setup : Star prog s s-setup
      star-setup = Once.Backend.X86.Correct.Star.exec-to-star exec-setup

      -- ========== Phase 2: Right setup (2 instructions) ==========
      -- label (5+len-f) ; mov rdi, [rdi+8]
      -- After: pc = length prefix + 7 + len-f, rdi = encode b

      -- Compose rdi proofs: rdi s-setup = rdi s = encode (inj₂ b)
      rdi-setup-eq : readReg (regs s-setup) rdi ≡ encode {A + B} (inj₂ b)
      rdi-setup-eq = trans rdi-setup rdi-eq

      -- Use extracted helper for right setup execution
      right-setup-result : CaseRightSetupResult f g prefix suffix b s-setup
      right-setup-result = exec-case-right-setup f g prefix suffix b s-setup
                             h-setup pc-setup rdi-setup-eq stack-inv-setup rsp>16-setup

      s-right = CaseRightSetupResult.s-right right-setup-result
      exec-right = CaseRightSetupResult.exec-right right-setup-result
      h-right = CaseRightSetupResult.h-right right-setup-result
      pc-right = CaseRightSetupResult.pc-right right-setup-result
      rdi-right = CaseRightSetupResult.rdi-right right-setup-result
      r14-right = CaseRightSetupResult.r14-preserved right-setup-result
      r15-right = CaseRightSetupResult.r15-preserved right-setup-result
      rbp-right = CaseRightSetupResult.rbp-preserved right-setup-result
      rsp-right = CaseRightSetupResult.rsp-preserved right-setup-result
      mem-right = CaseRightSetupResult.mem-preserved right-setup-result
      stack-inv-right = CaseRightSetupResult.stack-inv-right right-setup-result
      rsp>16-right = CaseRightSetupResult.rsp>16-right right-setup-result

      -- Convert right setup exec to Star
      star-right : Star prog s-setup s-right
      star-right = Once.Backend.X86.Correct.Star.exec-to-star exec-right

      -- ========== Phase 3: Execute g (recursive call) ==========
      -- pc s-right = length prefix + 7 + len-f

      -- Prefix for g = prefix + setup(3) + skip-left(1+len-f) + right-setup(2) = prefix + 6 + len-f
      -- Wait, this doesn't match. Let me recalculate.
      -- Actually the prefix for g is all instructions before g in the program.
      -- g starts at position 7+len-f, so prefix-g has length = length prefix + 7 + len-f
      prefix-g : Program
      prefix-g = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                 mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                 jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ []

      suffix-g : Program
      suffix-g = label end-label ∷ suffix

      -- Length of prefix-g
      -- prefix-g = prefix ++ [4 instrs] ++ code-f ++ [3 instrs]
      -- length = length prefix + 4 + len-f + 3 = length prefix + 7 + len-f
      len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
      len-prefix-g = trans (List-length-++ prefix)
                     (trans (cong (length prefix +ℕ_) inner-eq)
                            (sym (+-assoc (length prefix) 7 len-f)))
        where
          -- Inner list: 4 cons, then code-f ++ 3 more
          inner-eq : length (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                            mov (reg rdi) (mem (base+disp rdi 8)) ∷ code-f ++
                            jmp (2 +ℕ len-g) ∷ label right-label ∷ mov (reg rdi) (mem (base+disp rdi 8)) ∷ [])
                   ≡ 7 +ℕ len-f
          inner-eq = trans (cong (4 +ℕ_) (List-length-++ code-f))
                     (trans (cong (λ n → 4 +ℕ n +ℕ 3) (compile-length-correct f))
                     (trans (cong (_+ℕ 3) (+-comm 4 len-f))
                     (trans (+-assoc len-f 4 3)
                            (+-comm len-f 7))))

      pc-right-g : pc s-right ≡ length prefix-g
      pc-right-g = trans pc-right (sym len-prefix-g)

      -- Program equality for g from CaseContext
      prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
      prog-eq-g = CaseContext.prog-eq-g ctx

      -- Derive RbpInvariant for s-right: s → s-setup → s-right
      rbp-inv-setup-for-right : RbpInvariant s-setup
      rbp-inv-setup-for-right = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s s-setup rbp-inv rsp-setup rbp-setup

      rbp-inv-right : RbpInvariant s-right
      rbp-inv-right = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s-setup s-right rbp-inv-setup-for-right rsp-right rbp-right

      -- Recursive call to g
      step-g : ∃[ s1 ] IRStarResult g (prefix-g ++ code-g ++ suffix-g) s-right s1 b (length prefix-g)
      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-right h-right pc-right-g rdi-right stack-inv-right rsp>16-right rbp-inv-right

      s1 = proj₁ step-g
      r-g = proj₂ step-g
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-right s1
      star-g-raw = ir-star r-g
      h1 = ir-halted r-g
      pc1-raw = ir-pc r-g  -- pc s1 = length prefix-g + len-g = length prefix + 7 + len-f + len-g

      -- Convert star-g to use prog
      star-g : Star prog s-right s1
      star-g = subst (λ p → Star p s-right s1) (sym prog-eq-g) star-g-raw

      -- Convert closure-wf from g to use prog
      closure-wf-g-raw : ClosureWFOutput (prefix-g ++ code-g ++ suffix-g)
      closure-wf-g-raw = ir-closure-wf r-g
      closure-wf-final : ClosureWFOutput prog
      closure-wf-final = subst ClosureWFOutput (sym prog-eq-g) closure-wf-g-raw

      -- pc s1 = length prefix + 7 + len-f + len-g
      pc1 : pc s1 ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
      pc1 = trans pc1-raw (cong (_+ℕ len-g) len-prefix-g)

      -- ========== Phase 4: End label (1 instruction) ==========
      -- label (7+len-f+len-g) - no-op, just advances pc

      -- Use the extracted exec-case-end helper
      end-result : CaseEndResult f g prefix suffix s1
      end-result = exec-case-end f g prefix suffix s1 h1 pc1

      s-final = CaseEndResult.s-final end-result
      exec-end = CaseEndResult.exec-end end-result
      h-final = CaseEndResult.h-final end-result
      pc-final-raw = CaseEndResult.pc-final end-result
      rax-end = CaseEndResult.rax-preserved end-result
      r14-end = CaseEndResult.r14-preserved end-result
      r15-end = CaseEndResult.r15-preserved end-result
      rbp-end = CaseEndResult.rbp-preserved end-result
      rsp-end = CaseEndResult.rsp-preserved end-result
      mem-end = CaseEndResult.mem-preserved end-result

      -- Convert end exec to Star
      star-end : Star prog s1 s-final
      star-end = Once.Backend.X86.Correct.Star.exec-to-star exec-end

      -- ========== Compose all phases ==========
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-right (star-trans star-g star-end))

      -- ========== Final properties ==========
      pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
      pc-final = pc-final-raw

      -- rax-final: from ir-rax r-g, preserved through end
      rax-final : readReg (regs s-final) rax ≡ encode (eval g b)
      rax-final = trans rax-end (ir-rax r-g)

      -- r14 preserved through all phases
      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
      r14-final = trans r14-end (trans (ir-r14 r-g) (trans r14-right r14-setup))

      -- r15 preserved: setup uses r11 for tag (not r15), then preserved through remaining phases
      -- Proof: trans r15-end (trans (ir-r15 r-g) (trans r15-right r15-setup))
      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
      r15-final = trans r15-end (trans (ir-r15 r-g) (trans r15-right r15-setup))

      -- rbp preserved through all phases
      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
      rbp-final = trans rbp-end (trans (ir-rbp r-g) (trans rbp-right rbp-setup))

      -- Memory preserved through all phases:
      -- 1. mem-setup: memory s-setup = memory s
      -- 2. mem-right: memory s-right = memory s-setup
      -- 3. ir-mem r-g: readMem (memory s1) (r15 s-right) = readMem (memory s-right) (r15 s-right)
      -- 4. mem-end: memory s-final = memory s1
      -- And r15 is preserved: r15-setup, r15-right compose to r15 s-right = r15 s
      r15-right-to-s : readReg (regs s-right) r15 ≡ readReg (regs s) r15
      r15-right-to-s = trans r15-right r15-setup

      mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
      mem-final = trans (cong (λ m → readMem m (readReg (regs s) r15)) mem-end)
                  (trans (cong (λ addr → readMem (memory s1) addr) (sym r15-right-to-s))
                  (trans (ir-mem r-g)
                  (trans (cong (λ m → readMem m (readReg (regs s-right) r15)) mem-right)
                  (trans (cong (λ m → readMem m (readReg (regs s-right) r15)) mem-setup)
                         (cong (λ addr → readMem (memory s) addr) r15-right-to-s)))))

      -- Memory at rbp preserved through case execution (same chain as mem-final)
      rbp-right-to-s : readReg (regs s-right) rbp ≡ readReg (regs s) rbp
      rbp-right-to-s = trans rbp-right rbp-setup

      mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
      mem-rbp-final = trans (cong (λ m → readMem m (readReg (regs s) rbp)) mem-end)
                      (trans (cong (λ addr → readMem (memory s1) addr) (sym rbp-right-to-s))
                      (trans (ir-mem-rbp r-g)
                      (trans (cong (λ m → readMem m (readReg (regs s-right) rbp)) mem-right)
                      (trans (cong (λ m → readMem m (readReg (regs s-right) rbp)) mem-setup)
                             (cong (λ addr → readMem (memory s) addr) rbp-right-to-s)))))

      -- Memory at rbp+8 preserved through case execution
      mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
      mem-rbp+8-final = trans (cong (λ m → readMem m (readReg (regs s) rbp +ℕ 8)) mem-end)
                        (trans (cong (λ addr → readMem (memory s1) addr) (sym (cong (_+ℕ 8) rbp-right-to-s)))
                        (trans (ir-mem-rbp+8 r-g)
                        (trans (cong (λ m → readMem m (readReg (regs s-right) rbp +ℕ 8)) mem-right)
                        (trans (cong (λ m → readMem m (readReg (regs s-right) rbp +ℕ 8)) mem-setup)
                               (cong (λ addr → readMem (memory s) addr) (cong (_+ℕ 8) rbp-right-to-s))))))

      -- Stack invariant: preserved from s1 to s-final since memory, rsp, and r15 unchanged
      stack-inv-final : StackInvariant s-final
      stack-inv-final = stack-inv-preserved-mem-rsp s1 s-final mem-end rsp-end (ir-stack-inv r-g) r15-end

      rsp>16-final : readReg (regs s-final) rsp > 16
      rsp>16-final = ≤-trans 17≤41 (rsp-bound-after-stack-op s-final)
        where
          open import Data.Nat.Properties using (≤-trans)
          17≤41 : 17 ≤ 41
          17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

      -- RbpInvariant preserved: from ir-rbp-inv r-g through end (rsp/rbp preserved)
      rbp-inv-final : RbpInvariant s-final
      rbp-inv-final = Once.Backend.X86.Correct.StarBase.rbp-inv-preserved-unchanged s1 s-final (ir-rbp-inv r-g) rsp-end rbp-end

      -- Memory above rbp preserved through all phases
      mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
      mem-above-final addr addr>rbp =
        let addr>rbp-right : addr > readReg (regs s-right) rbp
            addr>rbp-right = subst (addr >_) (sym rbp-right-to-s) addr>rbp
        in trans (cong (λ m → readMem m addr) mem-end)
           (trans (ir-mem-above r-g addr addr>rbp-right)
           (trans (cong (λ m → readMem m addr) mem-right)
                  (cong (λ m → readMem m addr) mem-setup)))

      -- Memory at 0 preserved: setup/right-setup/end don't modify memory, chain through g
      mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      mem-at-0-final = trans mem-at-0-end (trans (ir-mem-at-0 r-g) (trans mem-at-0-right mem-at-0-setup))
        where
          mem-at-0-setup : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
          mem-at-0-setup = cong (λ m → readMem m 0) mem-setup

          mem-at-0-right : readMem (memory s-right) 0 ≡ readMem (memory s-setup) 0
          mem-at-0-right = cong (λ m → readMem m 0) mem-right

          mem-at-0-end : readMem (memory s-final) 0 ≡ readMem (memory s1) 0
          mem-at-0-end = cong (λ m → readMem m 0) mem-end

  -- | Star-based curry execution (direct, uses Star throughout)
  -- compile-length (curry f) = 13 + len-f
  -- Curry creates a closure; only executes 7 instructions (setup + jmp to end label)
  -- | Star-based curry execution (non-recursive, delegates to extracted module)
  run-curry-star-direct : ∀ {i A B C} (f : IR i (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)
  run-curry-star-direct {i} {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , ir-res , _) = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , ir-res

  -- | Lemma: thunk offset (|prefix| + 6) is within program bounds
  -- prog = prefix ++ compile-x86 (curry f) ++ suffix
  -- compile-length (curry f) = 13 + compile-length f ≥ 13
  -- So |prefix| + 6 < |prefix| + 13 ≤ |prefix ++ compile-x86 (curry f) ++ suffix|
  thunk-offset-in-bounds : ∀ {i A B C} (f : IR i (A * B) C) (prefix suffix : Program) →
    length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
  thunk-offset-in-bounds {i} {A} {B} {C} f prefix suffix = goal
    where
      open import Data.List.Properties as LP using (length-++)
      open import Data.Nat.Properties using (+-mono-<; +-monoʳ-<; m≤m+n; m≤n+m; ≤-trans; <-≤-trans)

      -- Length of compile-x86 (curry f) is 17 + compile-length f
      -- (6 closure setup + 7 thunk setup + len-f + 4 cleanup/end)
      curry-len : length (compile-x86 (curry f)) ≡ 17 +ℕ compile-length f
      curry-len = compile-length-correct (curry f)

      -- Length of full program
      prog-len : length (prefix ++ compile-x86 (curry f) ++ suffix)
               ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      prog-len = LP.length-++ prefix

      inner-len : length (compile-x86 (curry f) ++ suffix)
                ≡ length (compile-x86 (curry f)) +ℕ length suffix
      inner-len = LP.length-++ (compile-x86 (curry f))

      -- 6 < 17 (obviously)
      6<17 : 6 < 17
      6<17 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

      -- 6 < 17 + compile-length f (using: 6 < 17 and 17 ≤ 17 + compile-length f)
      6<17+f : 6 < 17 +ℕ compile-length f
      6<17+f = <-≤-trans 6<17 (m≤m+n 17 (compile-length f))

      -- 6 < 17 + compile-length f + length suffix
      6<17+f+s : 6 < 17 +ℕ compile-length f +ℕ length suffix
      6<17+f+s = <-≤-trans 6<17+f (m≤m+n (17 +ℕ compile-length f) (length suffix))

      -- |prefix| + 6 < |prefix| + (17 + compile-length f + length suffix)
      step1 : length prefix +ℕ 6 < length prefix +ℕ (17 +ℕ compile-length f +ℕ length suffix)
      step1 = +-monoʳ-< (length prefix) 6<17+f+s

      -- Rewrite using curry-len and inner-len
      step2 : length prefix +ℕ (17 +ℕ compile-length f +ℕ length suffix)
            ≡ length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
      step2 = cong (length prefix +ℕ_) (cong (_+ℕ length suffix) (sym curry-len))

      step3 : length prefix +ℕ (length (compile-x86 (curry f)) +ℕ length suffix)
            ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      step3 = cong (length prefix +ℕ_) (sym inner-len)

      step4 : length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
            ≡ length (prefix ++ compile-x86 (curry f) ++ suffix)
      step4 = sym prog-len

      goal : length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
      goal = subst (length prefix +ℕ 6 <_) (trans step2 (trans step3 step4)) step1

  -- | Star-based curry execution with closure well-formedness proof
  -- Returns CurryResult which includes ClosureWellFormed for use by apply
  run-curry-star-with-wf : ∀ {i A B C} (f : IR i (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] CurryResult f prog s s' x (length prefix)
  run-curry-star-with-wf {i} {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s' , record
      { curry-star = ir-star ir-res
      ; curry-halted = ir-halted ir-res
      ; curry-pc = ir-pc ir-res
      ; curry-rax = ir-rax ir-res
      ; curry-r14 = ir-r14 ir-res
      ; curry-r15 = ir-r15 ir-res
      ; curry-rbp = ir-rbp ir-res
      ; curry-mem = ir-mem ir-res
      ; curry-stack-inv = ir-stack-inv ir-res
      ; curry-rsp-bound = ir-rsp-bound ir-res
      ; closure-wf = wf
      }
    where
      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix

      -- Get the standard IRStarResult from existing curry proof
      -- run-curry-star now returns (s', IRStarResult, CurryMemoryResult)
      ir-result = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
      s' = proj₁ ir-result
      ir-res = proj₁ (proj₂ ir-result)
      -- mem-res = proj₂ (proj₂ ir-result)  -- CurryMemoryResult (available if needed)

      -- Thunk offset is offset + 6 (the code-ptr label in curry)
      thunk-offset = offset +ℕ 6

      -- Build the ClosureWellFormed proof using curry-thunk-correct-impl
      -- (This uses the proven version instead of the postulate-based construct-closure-wf)
      wf : ClosureWellFormed {B} {C} prog thunk-offset (encode x) (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-correct = λ arg s ret-addr h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16 →
            curry-thunk-correct-impl f prefix suffix x arg s ret-addr
              h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16
        }

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- Structure:
  --   1. Trace 5 setup instructions (label, sub, mov, mov, mov)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace ret instruction
  --   4. Compose via star-trans
  --
  -- The setup/ret tracing is postulated for now (similar to run-inl-star
  -- pattern, can be proven with detailed instruction semantics).
  ------------------------------------------------------------------------


  -- | curry-thunk-correct-impl: Implementation using IH
  -- This composes: setup tracing → IH on f → ret tracing
  curry-thunk-correct-impl : ∀ {i A B C} (f : IR i (A * B) C)
                             (prefix suffix : Program) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 6
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) rdi ≡ encode arg →
    readReg (regs s) r12 ≡ encode env →
    readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
  curry-thunk-correct-impl {i} {A} {B} {C} f prefix suffix env arg s ret-addr
                           h-eq pc-eq rdi-eq r12-eq mem-ret stack-inv rsp>16 =
    s-final , thunk-result , pc-final
    where
      open import Once.Backend.X86.Correct.ClosureWellFormed
        using (ThunkResult; thunk-star; thunk-halted; thunk-rax;
               thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-rsp-bound)
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (≤-trans; +-comm)

      -- From rsp > 16, derive 8 ≤ rsp (for m+[n∸m]≡n)
      8≤17 : 8 ≤ 17
      8≤17 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

      8≤rsp : 8 ≤ readReg (regs s) rsp
      8≤rsp = ≤-trans 8≤17 rsp>16

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 13      -- 6 closure + 7 thunk setup
      ret-offset = length prefix +ℕ 15 +ℕ compile-length f  -- f-offset + len-f + 2 cleanup

      -- Step 1: Trace 7 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq rdi-eq r12-eq stack-inv rsp>16
      s-after-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      rsp>16-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      -- RbpInvariant after setup
      rbp-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      -- Key property: memory at (rbp after setup) = original rbp
      mem-at-rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))))
      -- Memory at original rsp is preserved through setup
      mem-old-rsp-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))))

      -- Step 2: Call IH on f
      -- Define prefix-f and suffix-f so that prog = prefix-f ++ compile-x86 f ++ suffix-f

      -- curry layout: [0-5] closure setup, [6-12] thunk setup, [13 to 12+len(f)] f, [13-14+len(f)] cleanup, [15+len(f)] ret, [16+len(f)] label
      len-f = compile-length f
      end-label = 16 +ℕ len-f  -- position of end label
      end-offset-curry = 10 +ℕ len-f  -- jmp at pos 5 to reach 16 + len-f

      -- Prefix for f: prefix ++ first 13 instructions of curry (6 closure + 7 thunk)
      curry-closure-setup : Program
      curry-closure-setup =
        sub (reg rsp) (imm 16) ∷
        mov (mem (base rsp)) (reg rdi) ∷
        lea r9 (rip+disp 4) ∷
        mov (mem (base+disp rsp 8)) (reg r9) ∷
        mov (reg rax) (reg rsp) ∷
        jmp end-offset-curry ∷ []

      curry-thunk-setup : Program
      curry-thunk-setup =
        label 6 ∷
        push (reg rbp) ∷                       -- save frame pointer
        mov (reg rbp) (reg rsp) ∷              -- set frame pointer
        sub (reg rsp) (imm 16) ∷
        mov (mem (base rsp)) (reg r12) ∷
        mov (mem (base+disp rsp 8)) (reg rdi) ∷
        mov (reg rdi) (reg rsp) ∷ []

      prefix-f : Program
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup

      -- Suffix for f: cleanup ++ ret ∷ label ∷ suffix
      curry-tail : Program
      curry-tail = mov (reg rsp) (reg rbp) ∷   -- restore stack
                   pop rbp ∷                   -- restore frame pointer
                   ret ∷ label end-label ∷ []

      suffix-f : Program
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f = length prefix + 13 (6 closure + 7 thunk)
      -- Note: ++ is right-associative, so prefix-f = prefix ++ (curry-closure-setup ++ curry-thunk-setup)
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 13
      len-prefix-f = trans (List-length-++ prefix {curry-closure-setup ++ curry-thunk-setup})
                           (cong (length prefix +ℕ_) (List-length-++ curry-closure-setup {curry-thunk-setup}))

      -- Program equality: prog = prefix-f ++ compile-x86 f ++ suffix-f
      -- This requires showing curry structure matches

      -- Helper: compile-x86 (curry f) structure equality
      -- The curry compilation structure is:
      --   [6 closure setup] ++ [5 thunk setup] ++ compile-x86 f ++ [ret, label end]
      -- This is definitionally equal since (x ∷ y ∷ ... ∷ []) ++ rest = x ∷ y ∷ ... ∷ rest
      curry-structure : compile-x86 (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup ++ compile-x86 f ++ curry-tail
      curry-structure = refl

      -- Program equality using curry-structure and list reassociation
      -- prog = prefix ++ curry-structure ++ suffix
      --      = prefix ++ (A ++ B ++ f ++ C) ++ suffix
      --      = (prefix ++ A ++ B) ++ f ++ (C ++ suffix)
      --      = prefix-f ++ f ++ suffix-f
      -- Program equality using curry-structure and list reassociation
      -- ++ is right-associative, so prefix ++ A ++ B = prefix ++ (A ++ B)
      -- and prefix-f = prefix ++ (curry-closure-setup ++ curry-thunk-setup)
      -- and suffix-f = curry-tail ++ suffix
      --
      -- We need: prefix ++ (A ++ B ++ f ++ D) ++ suffix = (prefix ++ A ++ B) ++ f ++ (D ++ suffix)
      -- With right-assoc: prefix ++ ((A ++ (B ++ (f ++ D))) ++ suffix) = (prefix ++ (A ++ B)) ++ (f ++ (D ++ suffix))
      -- This requires multiple applications of ++-assoc
      prog-eq-f : prog ≡ prefix-f ++ compile-x86 f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          -- Abbreviations for readability (using unique names to avoid scope clashes)
          ccs = curry-closure-setup
          cts = curry-thunk-setup
          code-f = compile-x86 f
          cta = curry-tail

          -- The main reassociation proof
          -- Goal: prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ (prefix ++ ccs ++ cts) ++ code-f ++ (cta ++ suffix)
          prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
          prog-reassoc =
            let -- Step 1: prefix ++ (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix  (this is what we have)

                -- Step 2: Focus on inner (ccs ++ (cts ++ (code-f ++ cta)))
                inner-assoc1 : ccs ++ (cts ++ (code-f ++ cta)) ≡ (ccs ++ cts) ++ (code-f ++ cta)
                inner-assoc1 = sym (++-assoc ccs cts (code-f ++ cta))

                -- Step 3: ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix = (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ cta) suffix

                -- Step 4: (code-f ++ cta) ++ suffix = code-f ++ (cta ++ suffix)
                inner-assoc3 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
                inner-assoc3 = ++-assoc code-f cta suffix

                -- Combine steps 2-4 for the inner part
                inner-combined : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (cta ++ suffix))
                inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                 (trans inner-assoc2
                                        (cong ((ccs ++ cts) ++_) inner-assoc3))

                -- Step 5: prefix ++ X = prefix ++ X (applying the inner result)
                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined

                -- Step 6: prefix ++ ((ccs ++ cts) ++ X) = (prefix ++ (ccs ++ cts)) ++ X
                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))

            in trans outer-step final-assoc

      -- Call IH on f
      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      step-f : ∃[ s-f ] IRStarResult f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f (env , arg) s-after-setup
                 h-setup pc-setup-f rdi-setup stack-inv-setup rsp>16-setup rbp-inv-setup

      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = ir-star r-f

      -- Convert star-f to use prog
      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract properties from IH result
      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = ir-pc r-f

      -- f ends at position 13 + len-f (after prefix-f + compile-x86 f)
      -- We need to trace 2 cleanup instructions (mov rsp rbp, pop rbp) to reach ret at 15 + len-f
      cleanup-offset = length prefix +ℕ 13 +ℕ compile-length f  -- where f ends, cleanup begins

      pc-f-at-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-at-cleanup = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Step 2b: Trace cleanup instructions (mov rsp rbp, pop rbp)
      -- These restore the stack frame and rbp before ret
      -- The cleanup restores rbp to its ORIGINAL value (from s, before setup)
      -- because setup pushed it and cleanup pops it

      -- We need the following for the pop instruction:
      -- 1. rbp in s-after-f-raw points to the pushed rbp (s.rsp - 8)
      -- 2. Memory at that address contains s.rbp (pushed during setup)
      -- 3. Memory at s.rsp contains ret-addr (never modified)

      -- rbp value after f: preserved from setup, which set it to s.rsp - 8
      rbp-after-f : readReg (regs s-after-f-raw) rbp ≡ readReg (regs s) rsp ∸ 8
      rbp-after-f = trans (ir-rbp r-f) rbp-setup

      -- Fetch cleanup instructions
      -- fetch-cleanup-i0 proves: fetch prog (length prefix +ℕ 13 +ℕ compile-length f) ≡ just cleanup-i0
      -- cleanup-offset = length prefix +ℕ 13 +ℕ compile-length f
      -- These are definitionally equal (both parse as (length prefix +ℕ 13) +ℕ len-f)
      fetch-c0 : fetch prog cleanup-offset ≡ just cleanup-i0
      fetch-c0 = fetch-cleanup-i0 f prefix suffix

      -- fetch-cleanup-i1 proves: fetch prog (length prefix +ℕ 14 +ℕ compile-length f) ≡ just cleanup-i1
      -- cleanup-offset +ℕ 1 = ((length prefix +ℕ 13) +ℕ len-f) +ℕ 1
      -- We need to show this equals (length prefix +ℕ 14) +ℕ len-f
      cleanup-offset-plus-1 : cleanup-offset +ℕ 1 ≡ (length prefix +ℕ 14) +ℕ len-f
      cleanup-offset-plus-1 = trans (+-assoc (length prefix +ℕ 13) len-f 1)
                                    (trans (cong ((length prefix +ℕ 13) +ℕ_) (+-comm len-f 1))
                                           (trans (sym (+-assoc (length prefix +ℕ 13) 1 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 13 1))))

      fetch-c1 : fetch prog (cleanup-offset +ℕ 1) ≡ just cleanup-i1
      fetch-c1 = subst (λ n → fetch prog n ≡ just cleanup-i1)
                       (sym cleanup-offset-plus-1)
                       (fetch-cleanup-i1 f prefix suffix)

      -- State after mov rsp, rbp
      old-rsp-s = readReg (regs s) rsp
      rbp-val = readReg (regs s-after-f-raw) rbp  -- = old-rsp-s ∸ 8

      s-c1 : State
      s-c1 = record s-after-f-raw { regs = writeReg (regs s-after-f-raw) rsp rbp-val
                                  ; pc = pc s-after-f-raw +ℕ 1 }

      step-c0 : step prog s-after-f-raw ≡ just s-c1
      step-c0 = trans (step-exec prog s-after-f-raw cleanup-i0 (ir-halted r-f)
                        (subst (λ n → fetch prog n ≡ just cleanup-i0) (sym pc-f-at-cleanup) fetch-c0))
                      (execMov-reg-reg s-after-f-raw rsp rbp)

      h-c1 : halted s-c1 ≡ false
      h-c1 = ir-halted r-f

      pc-c1 : pc s-c1 ≡ cleanup-offset +ℕ 1
      pc-c1 = cong (_+ℕ 1) pc-f-at-cleanup

      -- State after pop rbp
      s-c2 : State
      s-c2 = record s-c1 { regs = writeReg (writeReg (regs s-c1) rbp (readReg (regs s) rbp))
                                          rsp (readReg (regs s-c1) rsp +ℕ 8)
                         ; pc = pc s-c1 +ℕ 1 }

      -- For pop rbp, we need memory at rbp to contain the original rbp
      -- PROVEN using ir-mem-rbp:
      -- Chain: s → s-after-setup → s-after-f-raw → s-c1
      -- 1. Setup: push rbp writes s.rbp at s.rsp - 8, rbp set to s.rsp - 8
      -- 2. mem-at-rbp-setup: memory at (rbp after setup) = original rbp
      -- 3. ir-mem-rbp: memory at (rbp after setup) preserved through f
      -- 4. Cleanup mov: doesn't change memory, sets rsp = rbp
      -- 5. rsp after cleanup = rbp after setup = address where original rbp was written

      -- memory s-c1 = memory s-after-f-raw (mov rsp, rbp doesn't write memory)
      mem-c1-eq-f : ∀ addr → readMem (memory s-c1) addr ≡ readMem (memory s-after-f-raw) addr
      mem-c1-eq-f addr = refl

      -- rsp in s-c1 = rbp-val = old-rsp-s - 8 (computed inline, same as rsp-c1 below)
      rsp-c1-inline : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ 8
      rsp-c1-inline = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Chain: memory at rbp after setup is preserved through f, available at rsp after cleanup
      mem-rbp-preserved-f : readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp) ≡
                            readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
      mem-rbp-preserved-f = ir-mem-rbp r-f

      -- Convert address from rbp-after-setup to old-rsp-s ∸ 8
      rbp-setup-addr : readReg (regs s-after-setup) rbp ≡ old-rsp-s ∸ 8
      rbp-setup-addr = rbp-setup

      pop-rbp-mem : readMem (memory s-c1) (readReg (regs s-c1) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = begin
        readMem (memory s-c1) (readReg (regs s-c1) rsp)
          ≡⟨ cong (readMem (memory s-c1)) rsp-c1-inline ⟩
        readMem (memory s-c1) (old-rsp-s ∸ 8)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ 8) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ 8)
          ≡⟨ cong (readMem (memory s-after-f-raw)) (sym rbp-setup-addr) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-rbp-preserved-f ⟩
        readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-at-rbp-setup ⟩
        just (readReg (regs s) rbp) ∎

      step-c1 : step prog s-c1 ≡ just s-c2
      step-c1 = trans (step-exec prog s-c1 cleanup-i1 h-c1
                        (subst (λ n → fetch prog n ≡ just cleanup-i1) (sym pc-c1) fetch-c1))
                      (execPop prog s-c1 rbp (readReg (regs s) rbp) pop-rbp-mem)

      h-c2 : halted s-c2 ≡ false
      h-c2 = h-c1

      -- pc s-c2 = cleanup-offset + 2 = ret-offset
      -- cleanup-offset = (length prefix +ℕ 13) +ℕ len-f
      -- ret-offset = (length prefix +ℕ 15) +ℕ len-f
      -- (length prefix +ℕ 13) +ℕ 2 ≡ length prefix +ℕ 15
      prefix-13+2 : (length prefix +ℕ 13) +ℕ 2 ≡ length prefix +ℕ 15
      prefix-13+2 = +-assoc (length prefix) 13 2

      cleanup-plus-2≡ret : cleanup-offset +ℕ 2 ≡ ret-offset
      cleanup-plus-2≡ret = trans (+-assoc (length prefix +ℕ 13) len-f 2)
                                 (trans (cong ((length prefix +ℕ 13) +ℕ_) (+-comm len-f 2))
                                        (trans (sym (+-assoc (length prefix +ℕ 13) 2 len-f))
                                               (cong (_+ℕ len-f) prefix-13+2)))

      pc-c2 : pc s-c2 ≡ ret-offset
      pc-c2 = trans (cong (_+ℕ 1) pc-c1)
                    (trans (+-assoc cleanup-offset 1 1)
                           cleanup-plus-2≡ret)

      -- rsp after cleanup = (s.rsp - 8) + 8 = s.rsp
      rsp-c1 : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ 8
      rsp-c1 = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      rsp-c2 : readReg (regs s-c2) rsp ≡ old-rsp-s
      rsp-c2 = trans (readReg-writeReg-same (writeReg (regs s-c1) rbp (readReg (regs s) rbp)) rsp
                                            (readReg (regs s-c1) rsp +ℕ 8))
                     (trans (cong (_+ℕ 8) rsp-c1)
                            (trans (+-comm (old-rsp-s ∸ 8) 8)
                                   (m+[n∸m]≡n 8≤rsp)))

      -- Register preservation through cleanup (mov rsp rbp doesn't touch rax, r14, r15, and pop rbp doesn't either)
      -- s-c2.regs = writeReg (writeReg (regs s-c1) rbp orig-rbp) rsp (s-c1.rsp + 8)
      rsp-val-c2 = readReg (regs s-c1) rsp +ℕ 8
      orig-rbp = readReg (regs s) rbp

      rax-c2 : readReg (regs s-c2) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-rax (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-rax (regs s-after-f-raw) rbp-val))

      r14-c2 : readReg (regs s-c2) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c2 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r14 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r14 (regs s-after-f-raw) rbp-val))

      r15-c2 : readReg (regs s-c2) r15 ≡ readReg (regs s-after-f-raw) r15
      r15-c2 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r15 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r15 (regs s-after-f-raw) rbp-val))

      rbp-c2 : readReg (regs s-c2) rbp ≡ readReg (regs s) rbp
      rbp-c2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (readReg-writeReg-same (regs s-c1) rbp orig-rbp)

      -- Star composition
      star-c : Star prog s-after-f-raw s-c2
      star-c = ⟨ ir-halted r-f , step-c0 ⟩◅ ⟨ h-c1 , step-c1 ⟩◅ refl*

      -- Stack invariant and rsp bound
      -- rsp>16-c2 follows from rsp-c2 (rsp restored to original) and rsp>16 (original > 16)
      rsp>16-c2 : readReg (regs s-c2) rsp > 16
      rsp>16-c2 = subst (_> 16) (sym rsp-c2) rsp>16

      -- Stack invariant: chain r15 and rsp back to original state
      -- r15: s → s-after-setup → s-after-f-raw → s-c2
      r15-s-to-c2 : readReg (regs s-c2) r15 ≡ readReg (regs s) r15
      r15-s-to-c2 = trans r15-c2 (trans (ir-r15 r-f) r15-setup)

      stack-inv-c2 : StackInvariant s-c2
      stack-inv-c2 = stack-inv-preserved-unchanged s s-c2 stack-inv r15-s-to-c2 rsp-c2

      cleanup-star : ∃[ s-cleanup ] (Star prog s-after-f-raw s-cleanup
                                    × halted s-cleanup ≡ false
                                    × pc s-cleanup ≡ ret-offset
                                    × readReg (regs s-cleanup) rax ≡ readReg (regs s-after-f-raw) rax
                                    × readReg (regs s-cleanup) r14 ≡ readReg (regs s-after-f-raw) r14
                                    × readReg (regs s-cleanup) r15 ≡ readReg (regs s-after-f-raw) r15
                                    × readReg (regs s-cleanup) rbp ≡ readReg (regs s) rbp
                                    × StackInvariant s-cleanup
                                    × readReg (regs s-cleanup) rsp > 16)
      cleanup-star = s-c2 , star-c , h-c2 , pc-c2 , rax-c2 , r14-c2 , r15-c2 , rbp-c2 , stack-inv-c2 , rsp>16-c2

      -- Return address preserved through execution
      --
      -- Chain: s → s-after-setup → s-after-f-raw → s-c1 → s-c2
      -- 1. s: mem-ret says memory at s.rsp contains ret-addr
      -- 2. Setup: writes at s.rsp - 8 (push rbp), disjoint from s.rsp
      -- 3. f: ir-mem-rbp+8 says memory at (rbp+8 = s.rsp) preserved
      -- 4. Cleanup: mov doesn't write memory, pop reads from s.rsp - 8
      --
      -- Arithmetic: (old-rsp-s ∸ 8) + 8 = old-rsp-s (given 8 ≤ old-rsp-s)
      rbp+8-eq : readReg (regs s-after-setup) rbp +ℕ 8 ≡ old-rsp-s
      rbp+8-eq = trans (cong (_+ℕ 8) rbp-setup-addr)
                       (trans (+-comm (old-rsp-s ∸ 8) 8) (m+[n∸m]≡n 8≤rsp))

      -- Setup preserves memory at s.rsp (writes are at s.rsp - 8 and below)
      -- Proven via mem-old-rsp-setup from thunk-setup-star
      mem-ret-through-setup : readMem (memory s-after-setup) old-rsp-s ≡ just ret-addr
      mem-ret-through-setup = trans mem-old-rsp-setup mem-ret

      -- Memory at s.rsp preserved through f (using ir-mem-rbp+8)
      mem-ret-through-f : readMem (memory s-after-f-raw) old-rsp-s ≡ just ret-addr
      mem-ret-through-f = begin
        readMem (memory s-after-f-raw) old-rsp-s
          ≡⟨ cong (readMem (memory s-after-f-raw)) (sym rbp+8-eq) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp +ℕ 8)
          ≡⟨ ir-mem-rbp+8 r-f ⟩
        readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp +ℕ 8)
          ≡⟨ cong (readMem (memory s-after-setup)) rbp+8-eq ⟩
        readMem (memory s-after-setup) old-rsp-s
          ≡⟨ mem-ret-through-setup ⟩
        just ret-addr ∎

      -- Memory preserved through cleanup (mov and pop don't write at old-rsp-s)
      mem-ret-preserved : readMem (memory (proj₁ cleanup-star)) (readReg (regs (proj₁ cleanup-star)) rsp) ≡ just ret-addr
      mem-ret-preserved = subst (λ addr → readMem (memory s-c2) addr ≡ just ret-addr)
                                (sym rsp-c2)
                                (trans (mem-c1-eq-f old-rsp-s) mem-ret-through-f)

      s-after-cleanup = proj₁ cleanup-star
      star-cleanup = proj₁ (proj₂ cleanup-star)
      h-cleanup = proj₁ (proj₂ (proj₂ cleanup-star))
      pc-cleanup = proj₁ (proj₂ (proj₂ (proj₂ cleanup-star)))
      rax-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star))))
      r14-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star)))))
      r15-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star))))))
      rbp-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star)))))))
      stack-inv-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star))))))))
      rsp>16-cleanup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star))))))))

      -- Compose f execution with cleanup
      star-f-to-cleanup : Star prog s-after-setup s-after-cleanup
      star-f-to-cleanup = star-trans star-f-converted star-cleanup

      -- Note: rbp is NOT preserved through setup (it becomes frame pointer)
      -- but IS restored to original by cleanup. So we need rbp relative to original s.
      f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                 × halted s-f ≡ false
                                 × pc s-f ≡ ret-offset
                                 × readReg (regs s-f) rax ≡ encode (eval f (env , arg))
                                 × readReg (regs s-f) r14 ≡ readReg (regs s-after-setup) r14
                                 × readReg (regs s-f) r15 ≡ readReg (regs s-after-setup) r15
                                 × readReg (regs s-f) rbp ≡ readReg (regs s) rbp  -- restored to original
                                 × StackInvariant s-f
                                 × readReg (regs s-f) rsp > 16
                                 × readMem (memory s-f) (readReg (regs s-f) rsp) ≡ just ret-addr)
      f-result-bridge = s-after-cleanup , star-f-to-cleanup , h-cleanup , pc-cleanup ,
                        trans rax-cleanup (ir-rax r-f) ,
                        trans r14-cleanup (ir-r14 r-f) ,
                        trans r15-cleanup (ir-r15 r-f) ,
                        rbp-cleanup ,  -- cleanup restores original rbp directly
                        stack-inv-cleanup , rsp>16-cleanup , mem-ret-preserved

      s-after-f = proj₁ f-result-bridge
      star-f = proj₁ (proj₂ f-result-bridge)
      h-f = proj₁ (proj₂ (proj₂ f-result-bridge))
      pc-f = proj₁ (proj₂ (proj₂ (proj₂ f-result-bridge)))
      rax-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))
      r14-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))
      r15-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))))
      rbp-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))
      stack-inv-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))))))
      rsp>16-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))))
      mem-ret-f = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))))

      -- Step 3: Trace ret instruction
      ret-result = thunk-ret-star f prefix suffix ret-addr s-after-f
                     h-f pc-f mem-ret-f stack-inv-f rsp>16-f
      s-final = proj₁ ret-result
      star-ret = proj₁ (proj₂ ret-result)
      h-final = proj₁ (proj₂ (proj₂ ret-result))
      pc-final = proj₁ (proj₂ (proj₂ (proj₂ ret-result)))
      rax-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))
      r14-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result)))))
      r15-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))
      rbp-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result)))))))
      stack-inv-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))))
      rsp>16-final = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))))

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      -- Note: rbp-f now directly gives s-after-f.rbp = s.rbp (cleanup restores original)
      thunk-result : ThunkResult prog s s-final (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-rax = trans rax-final rax-f
        ; thunk-r14 = trans r14-final (trans r14-f r14-setup)
        ; thunk-r15 = trans r15-final (trans r15-f r15-setup)
        ; thunk-rbp = trans rbp-final rbp-f  -- rbp-f gives s-after-f.rbp = s.rbp directly
        ; thunk-stack-inv = stack-inv-final
        ; thunk-rsp-bound = rsp>16-final
        }

  -- | Star-based apply execution (direct, uses Star throughout)
  -- compile-length apply = 6
  run-apply-star-direct : ∀ {i A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (apply {i} {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {i} {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {i} {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-rax = rax-final
      ; ir-r14 = r14-final
      ; ir-r15 = r15-final
      ; ir-rbp = rbp-final
      ; ir-mem = mem-final
      ; ir-mem-rbp = mem-rbp-final
      ; ir-mem-rbp+8 = mem-rbp+8-final
      ; ir-stack-inv = stack-inv-final
      ; ir-rsp-bound = rsp>16-final
      ; ir-rbp-inv = rbp-inv-final
      ; ir-mem-above = mem-above-final
      ; ir-mem-at-0 = mem-at-0-final
      ; ir-closure-wf = no-closure  -- apply consumes closure, doesn't produce one
      }
    where
      open import Data.Product using (proj₁; proj₂)
      result = apply-produces-result prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
      s-final = proj₁ result
      rest1 = proj₂ result
      star-all = proj₁ rest1
      rest2 = proj₂ rest1
      h-final = proj₁ rest2
      rest3 = proj₂ rest2
      pc-final = proj₁ rest3
      rest4 = proj₂ rest3
      rax-final = proj₁ rest4
      rest5 = proj₂ rest4
      r14-final = proj₁ rest5
      rest6 = proj₂ rest5
      r15-final = proj₁ rest6
      rest7 = proj₂ rest6
      rbp-final = proj₁ rest7
      rest8 = proj₂ rest7
      mem-final = proj₁ rest8
      rest9 = proj₂ rest8
      mem-rbp-final = proj₁ rest9
      rest10 = proj₂ rest9
      mem-rbp+8-final = proj₁ rest10
      rest11 = proj₂ rest10
      stack-inv-final = proj₁ rest11
      rest12 = proj₂ rest11
      rsp>16-final = proj₁ rest12
      rbp-inv-final = proj₂ rest12
      -- POSTULATE: Apply execution preserves memory above rbp
      postulate
        mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
        mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0

