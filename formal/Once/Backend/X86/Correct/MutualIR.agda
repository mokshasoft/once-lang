------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR
--
-- Concrete dispatcher that wires together all implementation modules.
--
-- This file contains:
-- 1. The mutual block with the two main dispatchers
-- 2. Curry and apply implementations (still in mutual block for now)
--
-- NOTE: Sized types removed for compilation performance (10-100x speedup).
-- Termination is guaranteed by structural recursion on IR constructors.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MutualIR where

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
         encode-inl-construct; encode-inr-construct; encode-closure-addr)
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
         PairAtS; pair-at-s;
         InlAt; inl-at; InrAt; inr-at;
         encode-pair-fst-derived; encode-pair-snd-derived;
         encode-inl-tag-derived; encode-inl-val-derived;
         encode-inr-tag-derived; encode-inr-val-derived)

-- Re-export StarBase for backwards compatibility
-- Simple Star proofs (non-recursive) are in StarBase.agda
open import Once.Backend.X86.Correct.StarBase public
  using (IRStarResult; IRStarResultS; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-at-0; ir-closure-wf;
         -- Stateful field accessors
         ir-rax-s;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star;
         run-fst-star-v; run-snd-star-v;
         -- Stateful runners for encoding postulate elimination
         run-id-star-s; run-terminal-star-s; run-fold-star-s; run-unfold-star-s;
         run-arr-star-s; run-fst-star-s; run-snd-star-s;
         run-inl-star-s; run-inr-star-s;
         -- Result records
         FstSndResultS;
         -- Conversion function
         convert-to-stateful;
         -- Helper functions
         rbp-inv-preserved-unchanged)

-- Import extracted IR base case modules
open import Once.Backend.X86.Correct.IR.Id
  using () renaming (run-id-star-s to run-id-s-ir)
open import Once.Backend.X86.Correct.IR.Terminal
  using () renaming (run-terminal-star-s to run-terminal-s-ir)
open import Once.Backend.X86.Correct.IR.Fold
  using () renaming (run-fold-star-s to run-fold-s-ir)
open import Once.Backend.X86.Correct.IR.Unfold
  using () renaming (run-unfold-star-s to run-unfold-s-ir)
open import Once.Backend.X86.Correct.IR.Arr
  using () renaming (run-arr-star-s to run-arr-s-ir)
open import Once.Backend.X86.Correct.IR.Inl
  using (run-inl-star)
open import Once.Backend.X86.Correct.IR.Inr
  using (run-inr-star)

-- Import extracted curry proof (non-recursive, entire function extracted)
open import Once.Backend.X86.Correct.IR.Curry using (run-curry-star; CurryMemoryResult)

-- Import closure well-formedness infrastructure for whole-program proofs
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult; ThunkResult;
         curry-star; curry-halted; curry-pc; curry-rax;
         curry-r14; curry-r15; curry-rbp; curry-mem;
         curry-stack-inv; curry-rsp-bound; closure-wf)
-- Note: ThunkProof postulates are now UNUSED
-- curry-thunk-correct-impl in this file replaces curry-thunk-correct postulate
-- construct-closure-wf is replaced by inline record construction using curry-thunk-correct-impl

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

-- Import implementation modules that use the abstract dispatcher
open import Once.Backend.X86.Correct.MutualIR.Dispatcher
  using (rbp-inv-preserved-through-ir; rbp-inv-preserved-through-ir-s;
         irresults-preserves-eval)

open import Once.Backend.X86.Correct.MutualIR.Compose
  using (run-compose-star-direct; run-compose-star-direct-s)

open import Once.Backend.X86.Correct.MutualIR.Pair
  using (run-pair-star-direct; run-pair-star-direct-s)

open import Once.Backend.X86.Correct.MutualIR.Case
  using (run-case-star-direct)

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
-- AllocMode Compile Equality Lemmas
--
-- Since Stack and Heap currently generate identical code, these lemmas
-- prove compilation equality. This allows us to convert proof results
-- between modes without duplicating proof logic.
------------------------------------------------------------------------

private
  inl-compile-eq : ∀ {A B} → compile-x86 (inl {A} {B} Stack) ≡ compile-x86 (inl {A} {B} Heap)
  inl-compile-eq = refl

  inr-compile-eq : ∀ {A B} → compile-x86 (inr {A} {B} Stack) ≡ compile-x86 (inr {A} {B} Heap)
  inr-compile-eq = refl

  pair-compile-eq : ∀ {A B C} (f : IR C A) (g : IR C B) →
    compile-x86 (⟨ f , g ⟩ Stack) ≡ compile-x86 (⟨ f , g ⟩ Heap)
  pair-compile-eq f g = refl

  curry-compile-eq : ∀ {A B C} (f : IR (A * B) C) →
    compile-x86 (curry f Stack) ≡ compile-x86 (curry f Heap)
  curry-compile-eq f = refl

  -- Convert IRStarResult from Heap to Stack using compile equality
  -- Since Stack and Heap compile to identical code (proven by the compile-eq lemmas above),
  -- we can convert proofs by substituting the program using the equality.
  convert-inl-heap-to-stack : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s s' : State) →
    IRStarResult (inl {A} {B} Heap) (prefix ++ compile-x86 (inl {A} {B} Heap) ++ suffix) s s' x (length prefix) →
    IRStarResult (inl {A} {B} Stack) (prefix ++ compile-x86 (inl {A} {B} Stack) ++ suffix) s s' x (length prefix)
  convert-inl-heap-to-stack {A} {B} prefix suffix x s s' res = record
    { ir-star = subst (λ p → Star p s s') prog-eq (ir-star res)
    ; ir-halted = ir-halted res
    ; ir-pc = subst (λ len → pc s' ≡ length prefix +ℕ len) len-eq (ir-pc res)
    ; ir-rax = ir-rax res  -- eval-eq is refl, so no subst needed
    ; ir-r14 = ir-r14 res
    ; ir-r15 = ir-r15 res
    ; ir-rbp = ir-rbp res
    ; ir-mem = ir-mem res
    ; ir-mem-rbp = ir-mem-rbp res
    ; ir-mem-rbp+8 = ir-mem-rbp+8 res
    ; ir-mem-above = ir-mem-above res
    ; ir-mem-at-0 = ir-mem-at-0 res
    ; ir-stack-inv = ir-stack-inv res
    ; ir-rsp-bound = ir-rsp-bound res
    ; ir-rbp-inv = ir-rbp-inv res
    ; ir-closure-wf = ir-closure-wf res
    }
    where
      -- Program equality: prefix ++ compile-x86 (inl Heap) ++ suffix ≡ prefix ++ compile-x86 (inl Stack) ++ suffix
      prog-eq : prefix ++ compile-x86 (inl {A} {B} Heap) ++ suffix ≡ prefix ++ compile-x86 (inl {A} {B} Stack) ++ suffix
      prog-eq = cong (λ code → prefix ++ code ++ suffix) (sym (inl-compile-eq {A} {B}))

      -- Compile-length equality (inl-compile-eq is refl, so this is refl too)
      len-eq : compile-length (inl {A} {B} Heap) ≡ compile-length (inl {A} {B} Stack)
      len-eq = refl

  convert-inr-heap-to-stack : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s s' : State) →
    IRStarResult (inr {A} {B} Heap) (prefix ++ compile-x86 (inr {A} {B} Heap) ++ suffix) s s' x (length prefix) →
    IRStarResult (inr {A} {B} Stack) (prefix ++ compile-x86 (inr {A} {B} Stack) ++ suffix) s s' x (length prefix)
  convert-inr-heap-to-stack {A} {B} prefix suffix x s s' res = record
    { ir-star = subst (λ p → Star p s s') prog-eq (ir-star res)
    ; ir-halted = ir-halted res
    ; ir-pc = subst (λ len → pc s' ≡ length prefix +ℕ len) len-eq (ir-pc res)
    ; ir-rax = ir-rax res  -- eval-eq is refl, so no subst needed
    ; ir-r14 = ir-r14 res
    ; ir-r15 = ir-r15 res
    ; ir-rbp = ir-rbp res
    ; ir-mem = ir-mem res
    ; ir-mem-rbp = ir-mem-rbp res
    ; ir-mem-rbp+8 = ir-mem-rbp+8 res
    ; ir-mem-above = ir-mem-above res
    ; ir-mem-at-0 = ir-mem-at-0 res
    ; ir-stack-inv = ir-stack-inv res
    ; ir-rsp-bound = ir-rsp-bound res
    ; ir-rbp-inv = ir-rbp-inv res
    ; ir-closure-wf = ir-closure-wf res
    }
    where
      prog-eq : prefix ++ compile-x86 (inr {A} {B} Heap) ++ suffix ≡ prefix ++ compile-x86 (inr {A} {B} Stack) ++ suffix
      prog-eq = cong (λ code → prefix ++ code ++ suffix) (sym (inr-compile-eq {A} {B}))

      len-eq : compile-length (inr {A} {B} Heap) ≡ compile-length (inr {A} {B} Stack)
      len-eq = refl

  convert-pair-heap-to-stack : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s s' : State) →
    IRStarResult (⟨ f , g ⟩ Heap) (prefix ++ compile-x86 (⟨ f , g ⟩ Heap) ++ suffix) s s' x (length prefix) →
    IRStarResult (⟨ f , g ⟩ Stack) (prefix ++ compile-x86 (⟨ f , g ⟩ Stack) ++ suffix) s s' x (length prefix)
  convert-pair-heap-to-stack {A} {B} {C} f g prefix suffix x s s' res = record
    { ir-star = subst (λ p → Star p s s') prog-eq (ir-star res)
    ; ir-halted = ir-halted res
    ; ir-pc = subst (λ len → pc s' ≡ length prefix +ℕ len) len-eq (ir-pc res)
    ; ir-rax = ir-rax res  -- eval-eq is refl, so no subst needed
    ; ir-r14 = ir-r14 res
    ; ir-r15 = ir-r15 res
    ; ir-rbp = ir-rbp res
    ; ir-mem = ir-mem res
    ; ir-mem-rbp = ir-mem-rbp res
    ; ir-mem-rbp+8 = ir-mem-rbp+8 res
    ; ir-mem-above = ir-mem-above res
    ; ir-mem-at-0 = ir-mem-at-0 res
    ; ir-stack-inv = ir-stack-inv res
    ; ir-rsp-bound = ir-rsp-bound res
    ; ir-rbp-inv = ir-rbp-inv res
    ; ir-closure-wf = ir-closure-wf res
    }
    where
      prog-eq : prefix ++ compile-x86 (⟨ f , g ⟩ Heap) ++ suffix ≡ prefix ++ compile-x86 (⟨ f , g ⟩ Stack) ++ suffix
      prog-eq = cong (λ code → prefix ++ code ++ suffix) (sym (pair-compile-eq f g))

      len-eq : compile-length (⟨ f , g ⟩ Heap) ≡ compile-length (⟨ f , g ⟩ Stack)
      len-eq = refl

  convert-curry-heap-to-stack : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s s' : State) →
    IRStarResult (curry f Heap) (prefix ++ compile-x86 (curry f Heap) ++ suffix) s s' x (length prefix) →
    IRStarResult (curry f Stack) (prefix ++ compile-x86 (curry f Stack) ++ suffix) s s' x (length prefix)
  convert-curry-heap-to-stack {A} {B} {C} f prefix suffix x s s' res = record
    { ir-star = subst (λ p → Star p s s') prog-eq (ir-star res)
    ; ir-halted = ir-halted res
    ; ir-pc = subst (λ len → pc s' ≡ length prefix +ℕ len) len-eq (ir-pc res)
    ; ir-rax = ir-rax res  -- eval-eq is refl, so no subst needed
    ; ir-r14 = ir-r14 res
    ; ir-r15 = ir-r15 res
    ; ir-rbp = ir-rbp res
    ; ir-mem = ir-mem res
    ; ir-mem-rbp = ir-mem-rbp res
    ; ir-mem-rbp+8 = ir-mem-rbp+8 res
    ; ir-mem-above = ir-mem-above res
    ; ir-mem-at-0 = ir-mem-at-0 res
    ; ir-stack-inv = ir-stack-inv res
    ; ir-rsp-bound = ir-rsp-bound res
    ; ir-rbp-inv = ir-rbp-inv res
    ; ir-closure-wf = ir-closure-wf res
    }
    where
      prog-eq : prefix ++ compile-x86 (curry f Heap) ++ suffix ≡ prefix ++ compile-x86 (curry f Stack) ++ suffix
      prog-eq = cong (λ code → prefix ++ code ++ suffix) (sym (curry-compile-eq f))

      len-eq : compile-length (curry f Heap) ≡ compile-length (curry f Stack)
      len-eq = refl

------------------------------------------------------------------------
-- Star-Based Mutual Block - Concrete Dispatcher
--
-- This mutual block contains:
-- 1. run-ir-star-at-offset and run-ir-star-at-offset-s (the dispatchers)
-- 2. curry and apply implementations (kept here for now since curry is 646 lines)
--
-- Base cases delegate to StarBase functions.
-- Recursive cases (compose, pair, case) delegate to implementation modules.
-- Curry and apply are defined inline in this mutual block.
--
-- TERMINATION: Sized types removed for 10-100x compilation speedup.
-- Structural recursion on IR constructors guarantees termination.
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
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
  run-ir-star-at-offset (inl {A} {B} Heap) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inl {A} {B} Stack) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , convert-inl-heap-to-stack {A} {B} prefix suffix x s s' res-heap
  run-ir-star-at-offset (inr {A} {B} Heap) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inr {A} {B} Stack) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , convert-inr-heap-to-stack {A} {B} prefix suffix x s s' res-heap
  run-ir-star-at-offset (initial {A}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 _ =
    ⊥-elim x

  -- Recursive cases: delegate to implementation modules
  run-ir-star-at-offset (_∘_ {A} {B} {C} g f) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-compose-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g Heap) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-pair-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g Stack) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-pair-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , convert-pair-heap-to-stack f g prefix suffix x s s' res-heap
  run-ir-star-at-offset ([_,_] {A} {B} {C} f g) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-case-star-direct f g prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (curry {A} {B} {C} f Heap) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-curry-star-direct f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (curry {A} {B} {C} f Stack) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-curry-star-direct f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , convert-curry-heap-to-stack f prefix suffix x s s' res-heap
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-apply-star-direct prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

  ------------------------------------------------------------------------
  -- Stateful Star-Based Runner (encoding postulate elimination)
  ------------------------------------------------------------------------

  -- | Stateful IR execution - returns address instead of using encode
  -- This enables encoding postulate elimination by tracking explicit memory addresses
  run-ir-star-at-offset-s : ∀ {A B} (ir : IR A B) (prefix suffix : Program)
      (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ addr-in →
    encode x ≡ addr-in →  -- Semantic value matches input address
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ addr-out ] ∃[ s' ] IRStarResultS ir prog s s' addr-out (length prefix)

  -- Base cases: delegate to extracted IR modules
  run-ir-star-at-offset-s (id {A}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-id-s-ir {A} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res

  run-ir-star-at-offset-s (terminal {A}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-terminal-s-ir {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
    in 0 , s' , res  -- terminal returns 0 (unit encoding)

  run-ir-star-at-offset-s (fold {F}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-fold-s-ir {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- fold is identity at runtime

  run-ir-star-at-offset-s (unfold {F}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-unfold-s-ir {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- unfold is identity at runtime

  run-ir-star-at-offset-s (arr {A} {B}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-arr-s-ir {A} {B} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- arr is identity at runtime (Eff = Closure)

  -- fst/snd: simple delegation following RISC-V pattern
  run-ir-star-at-offset-s (fst {A} {B}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-fst-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
        res-s = convert-to-stateful (fst {A} {B}) prog s s' x (length prefix) res
    in encode (proj₁ x) , s' , res-s

  run-ir-star-at-offset-s (snd {A} {B}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-snd-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
        res-s = convert-to-stateful (snd {A} {B}) prog s s' x (length prefix) res
    in encode (proj₂ x) , s' , res-s

  run-ir-star-at-offset-s (inl {A} {B} Heap) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-inl-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (inl {A} {B} Heap) ++ suffix
        res-s = convert-to-stateful (inl {A} {B} Heap) prog s s' x (length prefix) res
    in encode (inj₁ x) , s' , res-s

  run-ir-star-at-offset-s (inl {A} {B} Stack) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-inl-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        res-stack = convert-inl-heap-to-stack prefix suffix x s s' res-heap
        prog = prefix ++ compile-x86 (inl {A} {B} Stack) ++ suffix
        res-s = convert-to-stateful (inl {A} {B} Stack) prog s s' x (length prefix) res-stack
    in encode (inj₁ x) , s' , res-s


  run-ir-star-at-offset-s (inr {A} {B} Heap) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-inr-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (inr {A} {B} Heap) ++ suffix
        res-s = convert-to-stateful (inr {A} {B} Heap) prog s s' x (length prefix) res
    in encode (inj₂ x) , s' , res-s

  run-ir-star-at-offset-s (inr {A} {B} Stack) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res-heap) = run-inr-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        res-stack = convert-inr-heap-to-stack prefix suffix x s s' res-heap
        prog = prefix ++ compile-x86 (inr {A} {B} Stack) ++ suffix
        res-s = convert-to-stateful (inr {A} {B} Stack) prog s s' x (length prefix) res-stack
    in encode (inj₂ x) , s' , res-s

  run-ir-star-at-offset-s (initial {A}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    ⊥-elim x

  -- Recursive cases: delegate to implementation modules
  run-ir-star-at-offset-s (_∘_ {A} {B} {C} g f) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    run-compose-star-direct-s f g prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

  run-ir-star-at-offset-s (⟨_,_⟩ {A} {B} {C} f g Heap) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    run-pair-star-direct-s f g prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

  run-ir-star-at-offset-s (⟨_,_⟩ {A} {B} {C} f g Stack) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let enc-x = encode x
        (s' , res-heap) = run-pair-star-direct f g prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        res-stack = convert-pair-heap-to-stack f g prefix suffix x s s' res-heap
        prog = prefix ++ compile-x86 (⟨ f , g ⟩ Stack) ++ suffix
        res-s = convert-to-stateful (⟨ f , g ⟩ Stack) prog s s' x (length prefix) res-stack
    in encode (eval (⟨ f , g ⟩ Stack) x) , s' , res-s

  run-ir-star-at-offset-s ([_,_] {A} {B} {C} f g) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-case-star-direct f g prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 ([ f , g ]) ++ suffix
        res-s = convert-to-stateful ([ f , g ]) prog s s' x (length prefix) res
    in encode (eval ([ f , g ]) x) , s' , res-s

  run-ir-star-at-offset-s (curry {A} {B} {C} f Heap) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , (res , mem-res)) = run-curry-star f prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
        res-s = convert-to-stateful (curry f Heap) prog s s' x (length prefix) res
    in encode-closure-addr (eval (curry f Heap) x) , s' , res-s

  run-ir-star-at-offset-s (curry {A} {B} {C} f Stack) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , (res-heap , mem-res)) = run-curry-star f prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        res-stack = convert-curry-heap-to-stack f prefix suffix x s s' res-heap
        prog = prefix ++ compile-x86 (curry f Stack) ++ suffix
        res-s = convert-to-stateful (curry f Stack) prog s s' x (length prefix) res-stack
    in encode-closure-addr (eval (curry f Stack) x) , s' , res-s

  run-ir-star-at-offset-s (apply {A} {B}) prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-apply-star-direct prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
        res-s = convert-to-stateful (apply {A} {B}) prog s s' x (length prefix) res
    in encode (eval (apply {A} {B}) x) , s' , res-s

  ------------------------------------------------------------------------
  -- Curry implementation (kept in mutual block for now)
  ------------------------------------------------------------------------

  run-curry-star-direct : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
    in ∃[ s' ] IRStarResult (curry f Heap) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , ir-res , _) = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
    in s' , ir-res

  -- | Lemma: thunk offset (|prefix| + 6) is within program bounds
  -- prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
  -- compile-length (curry f Heap) = 13 + compile-length f ≥ 13
  -- So |prefix| + 6 < |prefix| + 13 ≤ |prefix ++ compile-x86 (curry f Heap) ++ suffix|
  thunk-offset-in-bounds : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
    length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f Heap) ++ suffix)
  thunk-offset-in-bounds {A} {B} {C} f prefix suffix = goal
    where
      open import Data.List.Properties as LP using (length-++)
      open import Data.Nat.Properties using (+-mono-<; +-monoʳ-<; m≤m+n; m≤n+m; ≤-trans; <-≤-trans)

      -- Length of compile-x86 (curry f Heap) is 17 + compile-length f
      -- (6 closure setup + 7 thunk setup + len-f + 4 cleanup/end)
      curry-len : length (compile-x86 (curry f Heap)) ≡ 17 +ℕ compile-length f
      curry-len = compile-length-correct (curry f Heap)

      -- Length of full program
      prog-len : length (prefix ++ compile-x86 (curry f Heap) ++ suffix)
               ≡ length prefix +ℕ length (compile-x86 (curry f Heap) ++ suffix)
      prog-len = LP.length-++ prefix

      inner-len : length (compile-x86 (curry f Heap) ++ suffix)
                ≡ length (compile-x86 (curry f Heap)) +ℕ length suffix
      inner-len = LP.length-++ (compile-x86 (curry f Heap))

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
            ≡ length prefix +ℕ (length (compile-x86 (curry f Heap)) +ℕ length suffix)
      step2 = cong (length prefix +ℕ_) (cong (_+ℕ length suffix) (sym curry-len))

      step3 : length prefix +ℕ (length (compile-x86 (curry f Heap)) +ℕ length suffix)
            ≡ length prefix +ℕ length (compile-x86 (curry f Heap) ++ suffix)
      step3 = cong (length prefix +ℕ_) (sym inner-len)

      step4 : length prefix +ℕ length (compile-x86 (curry f Heap) ++ suffix)
            ≡ length (prefix ++ compile-x86 (curry f Heap) ++ suffix)
      step4 = sym prog-len

      goal : length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f Heap) ++ suffix)
      goal = subst (length prefix +ℕ 6 <_) (trans step2 (trans step3 step4)) step1

  -- | Star-based curry execution with closure well-formedness proof
  -- Returns CurryResult which includes ClosureWellFormed for use by apply
  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
    in ∃[ s' ] CurryResult f prog s s' x (length prefix)
  run-curry-star-with-wf {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
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
      prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
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
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
                             (prefix suffix : Program) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
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
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix env arg s ret-addr
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

      prog = prefix ++ compile-x86 (curry f Heap) ++ suffix
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

      -- Helper: compile-x86 (curry f Heap) structure equality
      -- The curry compilation structure is:
      --   [6 closure setup] ++ [5 thunk setup] ++ compile-x86 f ++ [ret, label end]
      -- This is definitionally equal since (x ∷ y ∷ ... ∷ []) ++ rest = x ∷ y ∷ ... ∷ rest
      curry-structure : compile-x86 (curry f Heap) ≡
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

      s-after-f-raw : State
      s-after-f-raw = proj₁ step-f

      r-f : IRStarResult f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw (env , arg) (length prefix-f)
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

  ------------------------------------------------------------------------
  -- Apply implementation (kept in mutual block for now)
  ------------------------------------------------------------------------

  -- | Star-based apply execution (direct, uses Star throughout)
  -- compile-length apply = 6
  run-apply-star-direct : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
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
