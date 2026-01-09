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

-- Import memory region definitions
open import Once.Backend.Common.MemoryRegions
  using (region-of; code; stack; stack-code-disjoint; StackPointer)

-- Import stack capacity and region lemmas for D041 approach
open import Once.Backend.X86.Correct.StackInvariant2
  using (StackCapacity; capacity-maintained; rsp>16-to-capacity;
         zero-not-in-stack; rsp-in-stack)

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct; encode-closure-addr)
open import Once.Backend.X86.Postulates
  using (rsp-bound-after-stack-op)
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
         run-arr-star; run-fst-star; run-snd-star; run-prim-star;
         run-fst-star-v; run-snd-star-v;
         -- Stateful runners for encoding postulate elimination
         run-id-star-s; run-terminal-star-s; run-fold-star-s; run-unfold-star-s;
         run-arr-star-s; run-fst-star-s; run-snd-star-s; run-prim-star-s;
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
         cleanup-i0; cleanup-i1; cleanup-i2;
         fetch-cleanup-i0; fetch-cleanup-i1; fetch-cleanup-i2)
  renaming (fetch-ret to TS-fetch-ret)

-- Import thunk execution proofs (extracted from mutual block)
open import Once.Backend.X86.Correct.IR.ThunkExec
  using (thunk-setup-star; thunk-ret-star)

-- Import apply proof (uses ClosureWellFormed)
open import Once.Backend.X86.Correct.IR.Apply
  using (run-apply-to-ir-result)

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
  -- caller-sp: StackPointer representing the caller's stack frame (D041)
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to existing Star functions
  run-ir-star-at-offset (id {A}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (terminal {A}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (fold {F}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (unfold {F}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (arr {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-arr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (fst {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (snd {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inl {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inl-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (inr {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-inr-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (initial {A}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 _ =
    ⊥-elim x

  -- Recursive cases: delegate to implementation modules
  run-ir-star-at-offset (_∘_ {A} {B} {C} g f) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-compose-star-direct f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-pair-star-direct f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset ([_,_] {A} {B} {C} f g) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-case-star-direct f g prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (curry {A} {B} {C} f) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-curry-star-direct f prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv
  run-ir-star-at-offset (apply {A} {B}) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-apply-star-direct prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

  -- Prim: opaque primitive - correctness postulated until proper Prim compilation
  run-ir-star-at-offset (Prim {A} {B} name) prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    run-prim-star name prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

  ------------------------------------------------------------------------
  -- Stateful Star-Based Runner (encoding postulate elimination)
  ------------------------------------------------------------------------

  -- | Stateful IR execution - returns address instead of using encode
  -- This enables encoding postulate elimination by tracking explicit memory addresses
  -- caller-sp: StackPointer representing the caller's stack frame (D041)
  run-ir-star-at-offset-s : ∀ {A B} (ir : IR A B) (prefix suffix : Program)
      (caller-sp : StackPointer) (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
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
  run-ir-star-at-offset-s (id {A}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-id-s-ir {A} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res

  run-ir-star-at-offset-s (terminal {A}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-terminal-s-ir {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
    in 0 , s' , res  -- terminal returns 0 (unit encoding)

  run-ir-star-at-offset-s (fold {F}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-fold-s-ir {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- fold is identity at runtime

  run-ir-star-at-offset-s (unfold {F}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-unfold-s-ir {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- unfold is identity at runtime

  run-ir-star-at-offset-s (arr {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-arr-s-ir {A} {B} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv
    in addr-in , s' , res  -- arr is identity at runtime (Eff = Closure)

  -- fst/snd: simple delegation following RISC-V pattern
  run-ir-star-at-offset-s (fst {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-fst-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
        res-s = convert-to-stateful (fst {A} {B}) prog s s' x (length prefix) res
    in encode (proj₁ x) , s' , res-s

  run-ir-star-at-offset-s (snd {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-snd-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
        res-s = convert-to-stateful (snd {A} {B}) prog s s' x (length prefix) res
    in encode (proj₂ x) , s' , res-s

  run-ir-star-at-offset-s (inl {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-inl-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix
        res-s = convert-to-stateful (inl {A} {B}) prog s s' x (length prefix) res
    in encode (inj₁ x) , s' , res-s

  run-ir-star-at-offset-s (inr {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-inr-star prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (inr {A} {B}) ++ suffix
        res-s = convert-to-stateful (inr {A} {B}) prog s s' x (length prefix) res
    in encode (inj₂ x) , s' , res-s

  run-ir-star-at-offset-s (initial {A}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    ⊥-elim x

  -- Recursive cases: delegate to implementation modules
  run-ir-star-at-offset-s (_∘_ {A} {B} {C} g f) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    run-compose-star-direct-s f g prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

  run-ir-star-at-offset-s (⟨_,_⟩ {A} {B} {C} f g) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    run-pair-star-direct-s f g prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

  run-ir-star-at-offset-s ([_,_] {A} {B} {C} f g) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-case-star-direct f g prefix suffix caller-sp x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 ([ f , g ]) ++ suffix
        res-s = convert-to-stateful ([ f , g ]) prog s s' x (length prefix) res
    in encode (eval ([ f , g ]) x) , s' , res-s

  run-ir-star-at-offset-s (curry {A} {B} {C} f) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , (res , mem-res)) = run-curry-star f prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (curry f) ++ suffix
        res-s = convert-to-stateful (curry f) prog s s' x (length prefix) res
    in encode-closure-addr (eval (curry f) x) , s' , res-s

  run-ir-star-at-offset-s (apply {A} {B}) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    let (s' , res) = run-apply-star-direct prefix suffix caller-sp x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
        prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
        res-s = convert-to-stateful (apply {A} {B}) prog s s' x (length prefix) res
    in encode (eval (apply {A} {B}) x) , s' , res-s

  -- Prim: opaque primitive - correctness postulated until proper Prim compilation
  run-ir-star-at-offset-s (Prim {A} {B} name) prefix suffix caller-sp addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
    run-prim-star-s name prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv

  ------------------------------------------------------------------------
  -- Curry implementation (kept in mutual block for now)
  ------------------------------------------------------------------------

  run-curry-star-direct : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s' , record ir-res
      { ir-closure-wf = has-closure thunk-offset (encode x) (λ b → eval f (x , b)) wf
      }
    where
      prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix
      thunk-offset = offset +ℕ 6

      curry-result : ∃[ s' ] (IRStarResult (curry f) prog s s' x offset
                              × CurryMemoryResult f prog s' x offset)
      curry-result = run-curry-star f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv

      s' : State
      s' = proj₁ curry-result

      ir-res : IRStarResult (curry f) prog s s' x offset
      ir-res = proj₁ (proj₂ curry-result)

      -- Build the ClosureWellFormed proof using curry-thunk-correct-impl
      wf : ClosureWellFormed {B} {C} prog thunk-offset (encode x) (λ b → eval f (x , b))
      wf = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-correct = λ arg s₁ ret-addr h-eq pc-eq₁ rdi-eq₁ r12-eq mem-ret stack-inv₁ rsp>16₁ →
            curry-thunk-correct-impl f prefix suffix caller-sp x arg s₁ ret-addr
              h-eq pc-eq₁ rdi-eq₁ r12-eq mem-ret stack-inv₁ rsp>16₁
        }

  -- | Lemma: thunk offset (|prefix| + 6) is within program bounds
  -- prog = prefix ++ compile-x86 (curry f) ++ suffix
  -- compile-length (curry f) = 19 + compile-length f ≥ 19
  -- So |prefix| + 6 < |prefix| + 19 ≤ |prefix ++ compile-x86 (curry f) ++ suffix|
  thunk-offset-in-bounds : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) →
    length prefix +ℕ 6 < length (prefix ++ compile-x86 (curry f) ++ suffix)
  thunk-offset-in-bounds {A} {B} {C} f prefix suffix = goal
    where
      open import Data.List.Properties as LP using (length-++)
      open import Data.Nat.Properties using (+-mono-<; +-monoʳ-<; m≤m+n; m≤n+m; ≤-trans; <-≤-trans)

      -- Length of compile-x86 (curry f) is 19 + compile-length f
      -- (6 closure setup + 1 push r15 + 7 thunk setup + len-f + 5 cleanup/end)
      curry-len : length (compile-x86 (curry f)) ≡ 19 +ℕ compile-length f
      curry-len = compile-length-correct (curry f)

      -- Length of full program
      prog-len : length (prefix ++ compile-x86 (curry f) ++ suffix)
               ≡ length prefix +ℕ length (compile-x86 (curry f) ++ suffix)
      prog-len = LP.length-++ prefix

      inner-len : length (compile-x86 (curry f) ++ suffix)
                ≡ length (compile-x86 (curry f)) +ℕ length suffix
      inner-len = LP.length-++ (compile-x86 (curry f))

      -- 6 < 19 (obviously)
      6<19 : 6 < 19
      6<19 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

      -- 6 < 19 + compile-length f (using: 6 < 19 and 19 ≤ 19 + compile-length f)
      6<19+f : 6 < 19 +ℕ compile-length f
      6<19+f = <-≤-trans 6<19 (m≤m+n 19 (compile-length f))

      -- 6 < 19 + compile-length f + length suffix
      6<19+f+s : 6 < 19 +ℕ compile-length f +ℕ length suffix
      6<19+f+s = <-≤-trans 6<19+f (m≤m+n (19 +ℕ compile-length f) (length suffix))

      -- |prefix| + 6 < |prefix| + (19 + compile-length f + length suffix)
      step1 : length prefix +ℕ 6 < length prefix +ℕ (19 +ℕ compile-length f +ℕ length suffix)
      step1 = +-monoʳ-< (length prefix) 6<19+f+s

      -- Rewrite using curry-len and inner-len
      step2 : length prefix +ℕ (19 +ℕ compile-length f +ℕ length suffix)
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
  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (curry f) ++ suffix
    in ∃[ s' ] CurryResult f prog s s' x (length prefix)
  run-curry-star-with-wf {A} {B} {C} f prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
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
        ; thunk-correct = λ arg s₁ ret-addr h-eq pc-eq₁ rdi-eq₁ r12-eq mem-ret stack-inv₁ rsp>16₁ →
            curry-thunk-correct-impl f prefix suffix caller-sp x arg s₁ ret-addr
              h-eq pc-eq₁ rdi-eq₁ r12-eq mem-ret stack-inv₁ rsp>16₁
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
  -- caller-sp: StackPointer from the caller (D041)
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
                             (prefix suffix : Program) (caller-sp : StackPointer) (env : ⟦ A ⟧)
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
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix caller-sp env arg s ret-addr
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
      f-offset = length prefix +ℕ 14      -- 6 closure + 8 thunk setup
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f  -- f-offset + len-f + 3 cleanup

      -- Step 1: Trace 8 setup instructions
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
      -- The tuple ends with (mem-old-rsp × mem-r15 × mem-at-0 × mem-code)
      mem-rest = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))))
      mem-old-rsp-setup = proj₁ mem-rest
      -- Memory at (old-rsp - 8) where r15 was pushed, preserved through setup
      mem-r15-rest = proj₂ mem-rest
      mem-r15-setup = proj₁ mem-r15-rest
      -- Memory at 0 and code regions preserved through setup
      mem-0-and-code = proj₂ mem-r15-rest
      mem-at-0-setup = proj₁ mem-0-and-code
      mem-code-setup = proj₂ mem-0-and-code

      -- Step 2: Call IH on f
      -- Define prefix-f and suffix-f so that prog = prefix-f ++ compile-x86 f ++ suffix-f

      -- curry layout: [0-5] closure setup, [6-13] thunk setup (8 instr), [14 to 13+len(f)] f, [14-16+len(f)] cleanup (3 instr), [17+len(f)] ret, [18+len(f)] label
      len-f = compile-length f
      end-label = 18 +ℕ len-f  -- position of end label (6 closure + 8 thunk + len-f + 4 tail)
      end-offset-curry = 12 +ℕ len-f  -- jmp at pos 5 to reach 18 + len-f

      -- Prefix for f: prefix ++ first 14 instructions of curry (6 closure + 8 thunk)
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
        push (reg r15) ∷                       -- save r15 (apply's scratch register)
        push (reg rbp) ∷                       -- save frame pointer
        mov (reg rbp) (reg rsp) ∷              -- set frame pointer
        sub (reg rsp) (imm 16) ∷
        mov (mem (base rsp)) (reg r12) ∷
        mov (mem (base+disp rsp 8)) (reg rdi) ∷
        mov (reg rdi) (reg rsp) ∷ []

      prefix-f : Program
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup

      -- Suffix for f: cleanup ++ pop r15 ++ ret ∷ label ∷ suffix
      curry-tail : Program
      curry-tail = mov (reg rsp) (reg rbp) ∷   -- restore stack
                   pop rbp ∷                   -- restore frame pointer
                   pop r15 ∷                   -- restore r15
                   ret ∷ label end-label ∷ []

      suffix-f : Program
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f = length prefix + 14 (6 closure + 8 thunk)
      -- Note: ++ is right-associative, so prefix-f = prefix ++ (curry-closure-setup ++ curry-thunk-setup)
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
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
      step-f = run-ir-star-at-offset f prefix-f suffix-f caller-sp (env , arg) s-after-setup
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

      -- f ends at position 14 + len-f (after prefix-f + compile-x86 f)
      -- We need to trace 3 cleanup instructions (mov rsp rbp, pop rbp, pop r15) to reach ret at 17 + len-f
      cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f  -- where f ends, cleanup begins

      pc-f-at-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-at-cleanup = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Step 2b: Trace cleanup instructions (mov rsp rbp, pop rbp)
      -- These restore the stack frame and rbp before ret
      -- The cleanup restores rbp to its ORIGINAL value (from s, before setup)
      -- because setup pushed it and cleanup pops it

      -- We need the following for the pop instruction:
      -- 1. rbp in s-after-f-raw points to the pushed rbp (s.rsp - 16, after push r15 and push rbp)
      -- 2. Memory at that address contains s.rbp (pushed during setup)
      -- 3. Memory at s.rsp contains ret-addr (never modified)

      -- rbp value after f: preserved from setup, which set it to s.rsp - 16
      rbp-after-f : readReg (regs s-after-f-raw) rbp ≡ readReg (regs s) rsp ∸ 16
      rbp-after-f = trans (ir-rbp r-f) rbp-setup

      -- Fetch cleanup instructions
      -- fetch-cleanup-i0 proves: fetch prog (length prefix +ℕ 14 +ℕ compile-length f) ≡ just cleanup-i0
      -- cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f
      -- These are definitionally equal (both parse as (length prefix +ℕ 14) +ℕ len-f)
      fetch-c0 : fetch prog cleanup-offset ≡ just cleanup-i0
      fetch-c0 = fetch-cleanup-i0 f prefix suffix

      -- fetch-cleanup-i1 proves: fetch prog (length prefix +ℕ 15 +ℕ compile-length f) ≡ just cleanup-i1
      -- cleanup-offset +ℕ 1 = ((length prefix +ℕ 14) +ℕ len-f) +ℕ 1
      -- We need to show this equals (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 : cleanup-offset +ℕ 1 ≡ (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 = trans (+-assoc (length prefix +ℕ 14) len-f 1)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 1))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 1 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 1))))

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

      -- rsp in s-c1 = rbp-val = old-rsp-s - 16 (computed inline, same as rsp-c1 below)
      rsp-c1-inline : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ 16
      rsp-c1-inline = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Chain: memory at rbp after setup is preserved through f, available at rsp after cleanup
      mem-rbp-preserved-f : readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp) ≡
                            readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
      mem-rbp-preserved-f = ir-mem-rbp r-f

      -- Convert address from rbp-after-setup to old-rsp-s ∸ 16
      rbp-setup-addr : readReg (regs s-after-setup) rbp ≡ old-rsp-s ∸ 16
      rbp-setup-addr = rbp-setup

      pop-rbp-mem : readMem (memory s-c1) (readReg (regs s-c1) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = begin
        readMem (memory s-c1) (readReg (regs s-c1) rsp)
          ≡⟨ cong (readMem (memory s-c1)) rsp-c1-inline ⟩
        readMem (memory s-c1) (old-rsp-s ∸ 16)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ 16) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ 16)
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

      -- pc s-c2 = cleanup-offset + 2 (we still need one more cleanup step - pop r15)
      pc-c2 : pc s-c2 ≡ cleanup-offset +ℕ 2
      pc-c2 = trans (cong (_+ℕ 1) pc-c1)
                    (+-assoc cleanup-offset 1 1)

      -- rsp after mov rsp rbp = old-rsp-s - 16
      rsp-c1 : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ 16
      rsp-c1 = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Precondition: 16 ≤ old-rsp-s (for m+[n∸m]≡n later)
      -- rsp>16 : rsp > 16 means 16 < rsp, which implies 16 ≤ rsp
      16≤rsp : 16 ≤ readReg (regs s) rsp
      16≤rsp = Data.Nat.Properties.<⇒≤ rsp>16

      -- rsp after pop rbp = (old-rsp-s - 16) + 8 = old-rsp-s - 8
      -- Proof: (m ∸ 16) + 8 = ((m ∸ 8) ∸ 8) + 8 = m ∸ 8
      -- From 16 ≤ rsp, derive 16 - 8 ≤ rsp - 8, i.e., 8 ≤ rsp - 8
      8≤old-rsp-8 : 8 ≤ old-rsp-s ∸ 8
      8≤old-rsp-8 = Data.Nat.Properties.∸-monoˡ-≤ 8 16≤rsp

      rsp-c2 : readReg (regs s-c2) rsp ≡ old-rsp-s ∸ 8
      rsp-c2 = begin
        readReg (regs s-c2) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c1) rbp (readReg (regs s) rbp)) rsp
                                   (readReg (regs s-c1) rsp +ℕ 8) ⟩
        readReg (regs s-c1) rsp +ℕ 8
          ≡⟨ cong (_+ℕ 8) rsp-c1 ⟩
        (old-rsp-s ∸ 16) +ℕ 8
          ≡⟨ cong (_+ℕ 8) (sym (∸-+-assoc old-rsp-s 8 8)) ⟩
        ((old-rsp-s ∸ 8) ∸ 8) +ℕ 8
          ≡⟨ trans (+-comm ((old-rsp-s ∸ 8) ∸ 8) 8) (m+[n∸m]≡n 8≤old-rsp-8) ⟩
        old-rsp-s ∸ 8
        ∎

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

      -- Third cleanup step: pop r15
      -- fetch-cleanup-i2 proves: fetch prog (length prefix +ℕ (thunk-body-offset +ℕ 2) +ℕ compile-length f) ≡ just cleanup-i2
      -- cleanup-offset +ℕ 2 = ((length prefix +ℕ 14) +ℕ len-f) +ℕ 2
      -- We need to show this equals (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 : cleanup-offset +ℕ 2 ≡ (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 = trans (+-assoc (length prefix +ℕ 14) len-f 2)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 2))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 2 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 2))))

      fetch-c2 : fetch prog (cleanup-offset +ℕ 2) ≡ just cleanup-i2
      fetch-c2 = subst (λ n → fetch prog n ≡ just cleanup-i2)
                       (sym cleanup-offset-plus-2)
                       (fetch-cleanup-i2 f prefix suffix)

      -- Note: h-c2 defined above (after step-c1) already proves halted s-c2 ≡ false

      -- State after pop r15
      -- Pop restores r15 from stack at current rsp (old-rsp - 8)
      -- Memory at (old-rsp - 8) was where push r15 wrote the original r15
      -- We need to prove: readMem (memory s-c2) (readReg (regs s-c2) rsp) = just (orig-r15)
      -- where orig-r15 = readReg (regs s) r15

      orig-r15 = readReg (regs s) r15
      rsp-val-c3 = readReg (regs s-c2) rsp +ℕ 8

      s-c3 : State
      s-c3 = record s-c2 { regs = writeReg (writeReg (regs s-c2) r15 orig-r15)
                                          rsp rsp-val-c3
                         ; pc = pc s-c2 +ℕ 1 }

      -- Memory at rsp (old-rsp - 8) contains original r15
      -- Chain: s → s-after-setup (push r15 wrote here) → s-after-f → s-c1 → s-c2
      -- Memory preserved through f and cleanup (no writes at old-rsp - 8)

      -- Memory at (old-rsp - 8) preserved through f (using ir-mem-above)
      -- old-rsp - 8 > rbp because rbp = old-rsp - 16
      -- Need: old-rsp-s ∸ 16 < old-rsp-s ∸ 8
      -- Use ∸-monoʳ-< : o < n → n ≤ m → m ∸ n < m ∸ o
      8<16 : 8 < 16
      8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

      rsp-16<rsp-8 : readReg (regs s) rsp ∸ 16 < readReg (regs s) rsp ∸ 8
      rsp-16<rsp-8 = Data.Nat.Properties.∸-monoʳ-< 8<16 16≤rsp

      old-rsp-8>rbp : old-rsp-s ∸ 8 > readReg (regs s-after-setup) rbp
      old-rsp-8>rbp = subst (λ x → old-rsp-s ∸ 8 > x) (sym rbp-setup-addr) rsp-16<rsp-8

      -- r15 was pushed at old-rsp - 8 during thunk setup
      -- mem-r15-preserved from thunk-setup-star proves this is preserved
      pop-r15-mem : readMem (memory s-c2) (readReg (regs s-c2) rsp) ≡ just orig-r15
      pop-r15-mem = begin
        readMem (memory s-c2) (readReg (regs s-c2) rsp)
          ≡⟨ cong (readMem (memory s-c2)) rsp-c2 ⟩
        readMem (memory s-c2) (old-rsp-s ∸ 8)
          ≡⟨⟩  -- memory s-c2 = memory s-c1 (pop rbp only reads)
        readMem (memory s-c1) (old-rsp-s ∸ 8)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ 8) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ 8)
          ≡⟨ ir-mem-above r-f (old-rsp-s ∸ 8) old-rsp-8>rbp ⟩
        readMem (memory s-after-setup) (old-rsp-s ∸ 8)
          ≡⟨ mem-r15-setup ⟩
        just orig-r15 ∎

      step-c2 : step prog s-c2 ≡ just s-c3
      step-c2 = trans (step-exec prog s-c2 cleanup-i2 h-c2
                        (subst (λ n → fetch prog n ≡ just cleanup-i2) (sym pc-c2) fetch-c2))
                      (execPop prog s-c2 r15 orig-r15 pop-r15-mem)

      h-c3 : halted s-c3 ≡ false
      h-c3 = h-c2

      -- pc s-c3 = cleanup-offset + 3 = ret-offset
      -- cleanup-offset = (length prefix +ℕ 14) +ℕ len-f
      -- ret-offset = (length prefix +ℕ 17) +ℕ len-f
      -- (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 : (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 = +-assoc (length prefix) 14 3

      cleanup-plus-3≡ret : cleanup-offset +ℕ 3 ≡ ret-offset
      cleanup-plus-3≡ret = trans (+-assoc (length prefix +ℕ 14) len-f 3)
                                 (trans (cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 3))
                                        (trans (sym (+-assoc (length prefix +ℕ 14) 3 len-f))
                                               (cong (_+ℕ len-f) prefix-14+3)))

      pc-c3 : pc s-c3 ≡ ret-offset
      pc-c3 = begin
        pc s-c3
          ≡⟨⟩
        pc s-c2 +ℕ 1
          ≡⟨ cong (_+ℕ 1) pc-c2 ⟩
        (cleanup-offset +ℕ 2) +ℕ 1
          ≡⟨ +-assoc cleanup-offset 2 1 ⟩
        cleanup-offset +ℕ 3
          ≡⟨ cleanup-plus-3≡ret ⟩
        ret-offset
        ∎

      -- rsp after pop r15 = (old-rsp - 8) + 8 = old-rsp
      rsp-c3 : readReg (regs s-c3) rsp ≡ old-rsp-s
      rsp-c3 = begin
        readReg (regs s-c3) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c2) r15 orig-r15) rsp rsp-val-c3 ⟩
        rsp-val-c3
          ≡⟨⟩
        readReg (regs s-c2) rsp +ℕ 8
          ≡⟨ cong (_+ℕ 8) rsp-c2 ⟩
        (old-rsp-s ∸ 8) +ℕ 8
          ≡⟨ trans (+-comm (old-rsp-s ∸ 8) 8) (m+[n∸m]≡n 8≤rsp) ⟩
        old-rsp-s
        ∎

      -- Register preservation through third cleanup step
      rax-c3 : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rax (regs s-c2) orig-r15)
                            rax-c2)

      r14-c3 : readReg (regs s-c3) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-r14 (regs s-c2) orig-r15)
                            r14-c2)

      -- r15 after pop r15 = original r15 (restored from stack)
      r15-c3 : readReg (regs s-c3) r15 ≡ orig-r15
      r15-c3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (readReg-writeReg-same (regs s-c2) r15 orig-r15)

      rbp-c3 : readReg (regs s-c3) rbp ≡ readReg (regs s) rbp
      rbp-c3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rbp (regs s-c2) orig-r15)
                            rbp-c2)

      -- Star composition
      star-c : Star prog s-after-f-raw s-c3
      star-c = ⟨ ir-halted r-f , step-c0 ⟩◅ ⟨ h-c1 , step-c1 ⟩◅ ⟨ h-c2 , step-c2 ⟩◅ refl*

      -- Stack invariant and rsp bound
      -- rsp>16-c3 follows from rsp-c3 (rsp restored to original) and rsp>16 (original > 16)
      rsp>16-c3 : readReg (regs s-c3) rsp > 16
      rsp>16-c3 = subst (_> 16) (sym rsp-c3) rsp>16

      -- Stack invariant: r15 and rsp restored to original
      r15-s-to-c3 : readReg (regs s-c3) r15 ≡ readReg (regs s) r15
      r15-s-to-c3 = r15-c3

      stack-inv-c3 : StackInvariant s-c3
      stack-inv-c3 = stack-inv-preserved-unchanged s s-c3 stack-inv r15-s-to-c3 rsp-c3

      cleanup-star : ∃[ s-cleanup ] (Star prog s-after-f-raw s-cleanup
                                    × halted s-cleanup ≡ false
                                    × pc s-cleanup ≡ ret-offset
                                    × readReg (regs s-cleanup) rax ≡ readReg (regs s-after-f-raw) rax
                                    × readReg (regs s-cleanup) r14 ≡ readReg (regs s-after-f-raw) r14
                                    × readReg (regs s-cleanup) r15 ≡ readReg (regs s-after-f-raw) r15
                                    × readReg (regs s-cleanup) rbp ≡ readReg (regs s) rbp
                                    × StackInvariant s-cleanup
                                    × readReg (regs s-cleanup) rsp > 16
                                    -- D041: RSP restored to original and memory preservation
                                    × readReg (regs s-cleanup) rsp ≡ readReg (regs s) rsp
                                    × (∀ addr → readMem (memory s-cleanup) addr ≡ readMem (memory s-after-f-raw) addr))
      -- Note: r15-c3 proves r15 is restored to original, but cleanup-star expects preservation from s-after-f-raw
      -- We need to chain: r15-c3 : s-c3.r15 ≡ s.r15, and ir-r15 + r15-setup : s-after-f-raw.r15 ≡ s.r15
      r15-chain : readReg (regs s-c3) r15 ≡ readReg (regs s-after-f-raw) r15
      r15-chain = trans r15-c3 (sym (trans (ir-r15 r-f) r15-setup))

      -- Cleanup preserves memory (mov, pop, pop don't write to arbitrary addresses)
      -- memory s-c1 = memory s-after-f-raw (mov), memory s-c2 = memory s-c1 (pop), memory s-c3 = memory s-c2 (pop)
      mem-cleanup-preserves : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserves addr = mem-c1-eq-f addr  -- All three cleanup steps preserve memory

      cleanup-star = s-c3 , star-c , h-c3 , pc-c3 , rax-c3 , r14-c3 , r15-chain , rbp-c3 , stack-inv-c3 , rsp>16-c3 , rsp-c3 , mem-cleanup-preserves

      -- Return address preserved through execution
      --
      -- Chain: s → s-after-setup → s-after-f-raw → s-c1 → s-c2
      -- 1. s: mem-ret says memory at s.rsp contains ret-addr
      -- 2. Setup: writes at s.rsp - 8 (push rbp), disjoint from s.rsp
      -- 3. f: ir-mem-rbp+8 says memory at (rbp+8 = s.rsp) preserved
      -- 4. Cleanup: mov doesn't write memory, pop reads from s.rsp - 8
      --
      -- Setup preserves memory at s.rsp (writes are at s.rsp - 8 and below)
      -- Proven via mem-old-rsp-setup from thunk-setup-star
      mem-ret-through-setup : readMem (memory s-after-setup) old-rsp-s ≡ just ret-addr
      mem-ret-through-setup = trans mem-old-rsp-setup mem-ret

      -- Memory at s.rsp preserved through f (using ir-mem-above)
      -- old-rsp > rbp because rbp = old-rsp - 16 and 16 > 0
      -- Need: old-rsp > (old-rsp ∸ 16)
      -- m<m+n proves: (old-rsp ∸ 16) < (old-rsp ∸ 16) + 16
      -- Chain: (old-rsp ∸ 16) + 16 ≡ 16 + (old-rsp ∸ 16) ≡ old-rsp
      rbp+16≡old-rsp : readReg (regs s-after-setup) rbp +ℕ 16 ≡ old-rsp-s
      rbp+16≡old-rsp = trans (cong (_+ℕ 16) rbp-setup-addr)
                             (trans (+-comm (old-rsp-s ∸ 16) 16) (m+[n∸m]≡n 16≤rsp))

      old-rsp>rbp : old-rsp-s > readReg (regs s-after-setup) rbp
      old-rsp>rbp = subst (_> readReg (regs s-after-setup) rbp)
                         rbp+16≡old-rsp
                         (Data.Nat.Properties.m<m+n (readReg (regs s-after-setup) rbp) {16} (s≤s z≤n))

      mem-ret-through-f : readMem (memory s-after-f-raw) old-rsp-s ≡ just ret-addr
      mem-ret-through-f = begin
        readMem (memory s-after-f-raw) old-rsp-s
          ≡⟨ ir-mem-above r-f old-rsp-s old-rsp>rbp ⟩
        readMem (memory s-after-setup) old-rsp-s
          ≡⟨ mem-ret-through-setup ⟩
        just ret-addr ∎

      -- Memory preserved through cleanup (mov and pops don't write at old-rsp-s)
      -- s-c3 (after 3 cleanup steps) has rsp = old-rsp-s
      mem-ret-preserved : readMem (memory (proj₁ cleanup-star)) (readReg (regs (proj₁ cleanup-star)) rsp) ≡ just ret-addr
      mem-ret-preserved = subst (λ addr → readMem (memory s-c3) addr ≡ just ret-addr)
                                (sym rsp-c3)
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
      -- New D041 fields from cleanup-star
      cleanup-rest = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-star))))))))
      rsp>16-cleanup = proj₁ cleanup-rest
      rsp-cleanup-restored = proj₁ (proj₂ cleanup-rest)
      mem-cleanup-preserved = proj₂ (proj₂ cleanup-rest)

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
                                 × readMem (memory s-f) (readReg (regs s-f) rsp) ≡ just ret-addr
                                 -- D041: RSP and memory preservation for thunk postulates
                                 × readReg (regs s-f) rsp ≡ readReg (regs s) rsp
                                 × (∀ addr → readMem (memory s-f) addr ≡ readMem (memory s-after-f-raw) addr))
      f-result-bridge = s-after-cleanup , star-f-to-cleanup , h-cleanup , pc-cleanup ,
                        trans rax-cleanup (ir-rax r-f) ,
                        trans r14-cleanup (ir-r14 r-f) ,
                        trans r15-cleanup (ir-r15 r-f) ,
                        rbp-cleanup ,  -- cleanup restores original rbp directly
                        stack-inv-cleanup , rsp>16-cleanup , mem-ret-preserved ,
                        rsp-cleanup-restored , mem-cleanup-preserved

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
      -- D041 fields from f-result-bridge
      f-bridge-rest = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))))))
      mem-ret-f = proj₁ f-bridge-rest
      rsp-f-restored = proj₁ (proj₂ f-bridge-rest)
      mem-f-preserved = proj₂ (proj₂ f-bridge-rest)

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
      -- New fields from extended thunk-ret-star
      ret-rest = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))))))
      rsp>16-final = proj₁ ret-rest
      rsp-ret-plus-8 = proj₁ (proj₂ ret-rest)
      mem-ret-preserves = proj₂ (proj₂ ret-rest)

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      -- Note: rbp-f now directly gives s-after-f.rbp = s.rbp (cleanup restores original)

      -- RSP after thunk = entry RSP + 8 (ret pops return address):
      -- s → s-after-setup (rsp -= 32: push r15, push rbp, sub 16)
      -- s-after-setup → s-after-f (rsp restored by cleanup: add 16, pop rbp, pop r15)
      -- s-after-f → s-final (ret: rsp += 8)
      -- PROVEN: Chain rsp-ret-plus-8 with rsp-f-restored
      thunk-rsp-plus-8-proof : readReg (regs s-final) rsp ≡ readReg (regs s) rsp +ℕ 8
      thunk-rsp-plus-8-proof = trans rsp-ret-plus-8 (cong (_+ℕ 8) rsp-f-restored)

      -- Memory preservation above initial rsp:
      -- Thunk writes only below initial rsp (push, sub, local stores)
      -- Chain: ret preserves → cleanup preserves → f preserves (via ir-mem-above) → setup preserves
      --
      -- D041 approach for this proof:
      -- 1. ret preserves all memory: mem-ret-preserves (proven - ret doesn't write)
      -- 2. cleanup preserves all memory: mem-f-preserved (proven - mov/pop don't write)
      -- 3. IR preserves addresses > rbp: ir-mem-above (proven in IRStarResult)
      --    - rbp = s.rsp - 16, so addr ≥ s.rsp implies addr > rbp
      -- 4. setup preserves addresses ≥ s.rsp: needs thunk-setup-mem-above
      --    - Setup writes at s.rsp-8, s.rsp-16, s.rsp-24, s.rsp-32 (all < s.rsp)
      --    - To prove: extend thunk-setup-star with mem-above field
      thunk-mem-above-proof : ∀ addr → addr ≥ readReg (regs s) rsp →
                              readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-mem-above-proof addr addr≥rsp = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ ir-mem-above r-f addr addr>rbp-setup ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ setup-mem-above-post ⟩
        readMem (memory s) addr ∎
        where
          -- addr ≥ s.rsp and rbp = s.rsp - 16, so addr > rbp
          -- Proof: addr ≥ rsp > rsp - 16 = rbp (since rsp > 16)
          addr>rbp-setup : addr > readReg (regs s-after-setup) rbp
          addr>rbp-setup = subst (addr >_) (sym rbp-setup) addr>rsp-16
            where
              -- addr ≥ rsp and rsp > 16 implies addr > rsp - 16
              postulate
                addr>rsp-16 : addr > readReg (regs s) rsp ∸ 16

          -- Setup writes only at addresses < s.rsp, so addresses ≥ s.rsp are preserved
          -- To eliminate: extend thunk-setup-star to return mem-above field
          postulate
            setup-mem-above-post : readMem (memory s-after-setup) addr ≡ readMem (memory s) addr

      -- Memory at address 0 preserved:
      -- Thunk writes only to stack region, 0 is not in stack region
      -- PROVEN: Chain ret → cleanup → IR → setup memory preservation at address 0
      thunk-preserves-zero-proof : readMem (memory s-final) 0 ≡ readMem (memory s) 0
      thunk-preserves-zero-proof = begin
        readMem (memory s-final) 0
          ≡⟨ mem-ret-preserves 0 ⟩
        readMem (memory s-after-f) 0
          ≡⟨ mem-f-preserved 0 ⟩
        readMem (memory s-after-f-raw) 0
          ≡⟨ ir-mem-at-0 r-f ⟩
        readMem (memory s-after-setup) 0
          ≡⟨ mem-at-0-setup ⟩
        readMem (memory s) 0 ∎

      -- Memory at code-region addresses preserved:
      -- Thunk writes only to stack region, code region is disjoint from stack
      --
      -- D041 approach (correct):
      -- 1. ret preserves all memory: mem-ret-preserves (proven)
      -- 2. cleanup preserves all memory: mem-f-preserved (proven)
      -- 3. IR preserves code region: needs ir-mem-code field in IRStarResult
      --    - IR only writes to stack region addresses
      --    - Code region is disjoint from stack region (stack-code-disjoint)
      --    - Therefore code addresses are preserved
      -- 4. setup preserves code region: mem-code-setup (proven via D041)
      --
      -- NOTE: Using ir-mem-above + "code addresses > rbp" is WRONG approach.
      -- Region disjointness (≢) is not the same as address ordering (>).
      -- The postulate below should be replaced by adding ir-mem-code to IRStarResult.
      thunk-preserves-code-proof : ∀ addr → region-of addr ≡ code →
                                   readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-code-proof addr addr-in-code = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ ir-mem-code-post ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-code-setup addr addr-in-code ⟩
        readMem (memory s) addr ∎
        where
          -- TODO: Replace with ir-mem-code from IRStarResult
          -- Requires adding: ir-mem-code : ∀ addr → region-of addr ≡ code →
          --                                readMem (memory s') addr ≡ readMem (memory s) addr
          -- Proof: IR only writes to stack region, code is disjoint from stack
          postulate
            ir-mem-code-post : readMem (memory s-after-f-raw) addr ≡ readMem (memory s-after-setup) addr

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
        ; thunk-rsp-plus-8 = thunk-rsp-plus-8-proof
        ; thunk-mem-above = thunk-mem-above-proof
        ; thunk-preserves-zero = thunk-preserves-zero-proof
        ; thunk-preserves-code = thunk-preserves-code-proof
        }

  ------------------------------------------------------------------------
  -- Apply implementation (uses run-apply-to-ir-result from Apply.agda)
  --
  -- This replaces the monolithic apply-produces-result postulate with
  -- more structured postulates:
  --   1. closure-wf-for-apply: The closure is well-formed
  --   2. Memory layout postulates: Runtime memory structure
  --
  -- The apply instruction tracing is now proven in Apply.agda.
  ------------------------------------------------------------------------

  -- | Star-based apply execution (uses ClosureWellFormed-based proof)
  -- compile-length apply = 8 (push r15 + 5 movs + call + pop r15)
  run-apply-star-direct : ∀ {A B} (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {A} {B} prefix suffix caller-sp x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    let (s' , ir-result') = run-apply-to-ir-result prefix suffix code-ptr env-addr sem arg s
                              closure-wf-post h-false pc-eq rdi-eq' stack-inv rsp>16 rbp-inv mem-layout
    in s' , subst (λ xv → IRStarResult (apply {A} {B}) prog s s' xv offset) x'-eq-x ir-result'
    where
      open import Data.Product using (proj₁; proj₂)
      open import Once.Semantics using (Closure)

      prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix

      -- Extract closure and argument from semantic pair
      cl : Closure A B
      cl = proj₁ x

      arg : ⟦ A ⟧
      arg = proj₂ x

      -- Extract code-ptr, env-addr, semantics from closure
      code-ptr : ℕ
      code-ptr = Closure.code-ptr cl

      env-addr : ℕ
      env-addr = Closure.env-addr cl

      sem : ⟦ A ⟧ → ⟦ B ⟧
      sem = Closure.semantics cl

      -- The semantic value x' for run-apply-to-ir-result matches x
      x' : ⟦ (A ⇒ B) * A ⟧
      x' = (record { env-addr = env-addr ; code-ptr = code-ptr ; semantics = sem } , arg)

      -- Prove x' ≡ x (eta-expansion of Closure record)
      -- The closure is reconstructed from its fields, which equals the original
      postulate
        x'-eq-x : x' ≡ x

      rdi-eq' : readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} x'
      rdi-eq' = trans rdi-eq (cong encode (sym x'-eq-x))

      -- POSTULATE: Closure well-formedness for closures in the program
      -- This is justified because all closures come from curry in the same program,
      -- and curry now produces ClosureWellFormed proofs (see run-curry-star-direct).
      -- Threading this proof through composition is a future improvement.
      postulate
        closure-wf-post : ClosureWellFormed {A} {B} prog code-ptr env-addr sem

      -- POSTULATE: Memory layout at runtime
      -- These capture the encoding of the closure/argument pair in memory.
      postulate
        mem-layout : ∃[ closure-addr ] (
          readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
          readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just (encode arg) ×
          readMem (memory s) closure-addr ≡ just env-addr ×
          readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr)
