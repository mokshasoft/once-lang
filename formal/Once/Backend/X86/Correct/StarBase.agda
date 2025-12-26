------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StarBase
--
-- Simple Star-based IR execution proofs.
-- These are non-recursive (don't call run-ir-star-at-offset).
-- Extracted from MutualIR.agda to reduce compilation time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StarBase where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-arr-identity; encode-fix-unwrap; encode-fix-wrap)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; r15-unused; stack-below-r15; RbpInvariant; stack-inv-preserved-unchanged; rsp>16-preserved-unchanged)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; fst-valid; snd-valid;
         PairAtS; fst-valid-s; snd-valid-s;
         InlAtS; inl-at-s; InrAtS; inr-at-s)

open import Once.Backend.Common.Memory using (n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _∸_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; ≤-trans; m∸n≤m)
open import Data.List using (List; _∷_; []; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- IRStarResult: Result type for Star-based IR execution
------------------------------------------------------------------------

-- | Record type for Star-based IR execution result
-- Contains all properties needed for proof composition
record IRStarResult {A B : Type} (ir : IR A B) (prog : Program)
                    (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set where
  field
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-rax        : readReg (regs s') rax ≡ encode (eval ir x)
    ir-r14        : readReg (regs s') r14 ≡ readReg (regs s) r14
    ir-r15        : readReg (regs s') r15 ≡ readReg (regs s) r15
    ir-rbp        : readReg (regs s') rbp ≡ readReg (regs s) rbp
    ir-mem        : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    ir-mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    -- Memory at rbp+8 preserved (where ret-addr is stored in thunk context)
    ir-mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    ir-stack-inv  : StackInvariant s'
    ir-rsp-bound  : readReg (regs s') rsp > 16
    -- RbpInvariant preserved: rsp s' ≤ rbp s' (needed for memory disjointness)
    ir-rbp-inv    : RbpInvariant s'

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type for the recursive IR execution function
------------------------------------------------------------------------

-- | Type signature for the recursive IR execution function.
-- Recursive case handlers (compose, pair, case, curry, apply) take
-- an IRRunner as a parameter, allowing them to be defined outside
-- the mutual block. This dramatically reduces compilation time.
IRRunner : Set
IRRunner = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- RbpInvariant preservation helper
------------------------------------------------------------------------

-- | Preserve RbpInvariant when rsp and rbp are unchanged
rbp-inv-preserved-unchanged : ∀ (s s' : State) →
  RbpInvariant s →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rbp ≡ readReg (regs s) rbp →
  RbpInvariant s'
rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq = record
  { rsp≤rbp = subst₂ _≤_ (sym rsp-eq) (sym rbp-eq) (RbpInvariant.rsp≤rbp rbp-inv) }
  where
    open import Data.Nat using (_≤_)
    open import Relation.Binary.PropositionalEquality using (subst₂)

------------------------------------------------------------------------
-- Simple Star proofs (single-step, no recursion)
------------------------------------------------------------------------

-- | Star-based id execution
run-id-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A} {A} id ++ suffix
  in ∃[ s' ] IRStarResult {A} {A} id prog s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {A} {A} id ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based terminal execution
run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix
  in ∃[ s' ] IRStarResult {A} {Unit} terminal prog s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) 0
      rbp-eq = readReg-writeReg-rax-rbp (regs s) 0
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym encode-unit)
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) 0
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) 0
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based fold execution
run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix
  in ∃[ s' ] IRStarResult {F} {Fix F} fold prog s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-fix-wrap x))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based unfold execution
run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix
  in ∃[ s' ] IRStarResult {Fix F} {F} unfold prog s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-fix-unwrap x))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based arr execution
run-arr-star : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode {A ⇒ B} fn →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix
  in ∃[ s' ] IRStarResult {A ⇒ B} {Eff A B} arr prog s s' fn (length prefix)
run-arr-star {A} {B} prefix suffix fn s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-arr-at-offset {A} {B} prefix suffix fn s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-arr-identity {A} {B} fn))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based fst execution (uses encode-pair-fst axiom)
run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {A} fst prog s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Star-based snd execution (uses encode-pair-snd axiom)
run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {B} snd prog s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

------------------------------------------------------------------------
-- Postulate-free fst/snd using MemoryValid
--
-- These versions take a validity precondition (PairAt) instead of
-- using the postulated encode-pair-fst/snd axioms.
------------------------------------------------------------------------

-- | Postulate-free fst: uses PairAt validity instead of axiom
run-fst-star-v : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  PairAt a b (encode (a , b)) (memory s) →  -- Validity precondition (PROVEN by allocation)
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {A} fst prog s s' (a , b) (length prefix)
run-fst-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = fst-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Postulate-free snd: uses PairAt validity instead of axiom
run-snd-star-v : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  PairAt a b (encode (a , b)) (memory s) →  -- Validity precondition (PROVEN by allocation)
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {B} snd prog s s' (a , b) (length prefix)
run-snd-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = snd-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

------------------------------------------------------------------------
-- Stateful Star proofs: No encode dependency at all
--
-- These versions use explicit addresses and PairAtS (stateful validity).
-- The key difference from run-*-star-v:
-- 1. Values are represented by explicit addresses, not ⟦ A ⟧
-- 2. PairAtS uses addresses instead of encode
-- 3. Result is rax = addr, not rax = encode val
--
-- This breaks ALL dependency on the abstract encode function.
------------------------------------------------------------------------

-- | Stateful result record for fst/snd operations
-- Captures the key properties without encode dependency
record FstSndResultS (prog : Program) (s s' : State) (addr-result : Word) (offset : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ 1
    rax-eq     : readReg (regs s') rax ≡ addr-result
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    mem-r15    : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

open FstSndResultS public

-- | Fully stateful fst: uses PairAtS with explicit addresses (NO encode!)
run-fst-star-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-pair addr-a addr-b : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-pair →
  PairAtS addr-a addr-b addr-pair (memory s) →  -- Stateful validity (PROVEN, no postulates)
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in ∃[ s' ] FstSndResultS prog s s' addr-a (length prefix)
run-fst-star-s {A} {B} prefix suffix addr-pair addr-a addr-b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) addr-pair ≡ just addr-a
      mem-eq = fst-valid-s pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset-s {A} {B} prefix suffix addr-pair addr-a s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) addr-a
      rbp-eq = readReg-writeReg-rax-rbp (regs s) addr-a
  in s' , record
    { star = star-single h-false step-eq
    ; halted' = h'
    ; pc' = pc'
    ; rax-eq = rax-eq'
    ; r14-eq = readReg-writeReg-rax-r14 (regs s) addr-a
    ; r15-eq = readReg-writeReg-rax-r15 (regs s) addr-a
    ; rbp-eq = rbp-eq
    ; mem-r15 = refl
    ; mem-rbp = refl
    ; mem-rbp+8 = refl
    ; stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                    (readReg-writeReg-rax-r15 (regs s) addr-a)
                    rsp-eq
    ; rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

-- | Fully stateful snd: uses PairAtS with explicit addresses (NO encode!)
run-snd-star-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-pair addr-a addr-b : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-pair →
  PairAtS addr-a addr-b addr-pair (memory s) →  -- Stateful validity (PROVEN, no postulates)
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in ∃[ s' ] FstSndResultS prog s s' addr-b (length prefix)
run-snd-star-s {A} {B} prefix suffix addr-pair addr-a addr-b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (addr-pair +ℕ 8) ≡ just addr-b
      mem-eq = snd-valid-s pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset-s {A} {B} prefix suffix addr-pair addr-b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) addr-b
      rbp-eq = readReg-writeReg-rax-rbp (regs s) addr-b
  in s' , record
    { star = star-single h-false step-eq
    ; halted' = h'
    ; pc' = pc'
    ; rax-eq = rax-eq'
    ; r14-eq = readReg-writeReg-rax-r14 (regs s) addr-b
    ; r15-eq = readReg-writeReg-rax-r15 (regs s) addr-b
    ; rbp-eq = rbp-eq
    ; mem-r15 = refl
    ; mem-rbp = refl
    ; mem-rbp+8 = refl
    ; stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                    (readReg-writeReg-rax-r15 (regs s) addr-b)
                    rsp-eq
    ; rsp-bound = rsp>16-preserved-unchanged s s' rsp>16 rsp-eq
    ; rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    }

------------------------------------------------------------------------
-- Stateful Inl/Inr proofs: Produce validity as output
--
-- inl and inr ALLOCATE in memory. The stateful versions:
-- 1. Take input address instead of encode x
-- 2. Return output address (allocation address)
-- 3. Return InlAtS/InrAtS validity evidence (PROVEN from memory writes)
--
-- This is the "producer" pattern: allocation creates validity.
------------------------------------------------------------------------

-- | Stateful result record for inl/inr operations
-- Captures allocation result with validity proof
record InlResultS (prog : Program) (s s' : State)
                  (addr-in addr-out : Word) (offset : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ 4  -- inl is 4 instructions
    rax-eq     : readReg (regs s') rax ≡ addr-out
    inl-valid  : InlAtS addr-in addr-out (memory s')  -- PRODUCED validity
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

open InlResultS public using (inl-valid)

record InrResultS (prog : Program) (s s' : State)
                  (addr-in addr-out : Word) (offset : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ 4  -- inr is 4 instructions
    rax-eq     : readReg (regs s') rax ≡ addr-out
    inr-valid  : InrAtS addr-in addr-out (memory s')  -- PRODUCED validity
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

open InrResultS public using (inr-valid)

-- | Stateful inl: produces InlAtS validity (NO encode postulates!)
--
-- The key insight: instead of using encode-inl-construct to prove
-- rax = encode (inj₁ x), we directly construct InlAtS from memory writes.
--
-- Input: addr-x in rdi (the address of the value to wrap in inl)
-- Output: addr-out = rsp - 16 (the allocation address)
--         InlAtS addr-x addr-out (memory s')
run-inl-star-s : ∀ {A B : Type} (prefix suffix : Program) (addr-x : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 {A} {A + B} inl ++ suffix
      addr-out = readReg (regs s) rsp ∸ 16
  in ∃[ s' ] InlResultS prog s s' addr-x addr-out (length prefix)
run-inl-star-s {A} {B} prefix suffix addr-x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s4 , record
    { star = star-proof
    ; halted' = h4
    ; pc' = pc4
    ; rax-eq = rax-eq-inl
    ; inl-valid = inl-valid-proof
    ; r14-eq = r14-preserved
    ; r15-eq = r15-preserved
    ; rbp-eq = rbp-preserved
    ; stack-inv = stack-inv'
    ; rsp-bound = rsp>16'
    ; rbp-inv = rbp-inv'
    }
  where
    -- The program
    prog : Program
    prog = prefix ++ compile-x86 {A} {A + B} inl ++ suffix

    -- The 4 instructions of inl
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)
    i1 : Instr
    i1 = mov (mem (base rsp)) (imm 0)
    i2 : Instr
    i2 = mov (mem (base+disp rsp 8)) (reg rdi)
    i3 : Instr
    i3 = mov (reg rax) (reg rsp)

    -- Original register values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp
    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    -- State after step 2: mov [rsp], 0
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 0
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    -- Fetch lemmas
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix (i0 ∷ [])

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1
               (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix))

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix (i0 ∷ i1 ∷ [])

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix))

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix (i0 ∷ i1 ∷ i2 ∷ [])

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix)

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-imm prog s1 rsp 0)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Star proof
    star-proof : Star prog s s4
    star-proof = star-step4 h-false step1 h1 step2 h2 step3 h3 step4

    -- Track rsp through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- rax in s4 = rsp in s3 = new-rsp
    rax-s4-eq : readReg (regs s4) rax ≡ new-rsp
    rax-s4-eq = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    rax-eq-inl : readReg (regs s4) rax ≡ new-rsp
    rax-eq-inl = rax-s4-eq

    -- Track rdi through states
    rdi-s1 : readReg (regs s1) rdi ≡ addr-x
    rdi-s1 = trans (readReg-writeReg-rsp-rdi (regs s) new-rsp) rdi-eq

    rdi-s2 : readReg (regs s2) rdi ≡ addr-x
    rdi-s2 = rdi-s1

    -- Address disjointness
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- Memory at new-rsp = 0 (set in s2, preserved in s3, s4)
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 0
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) new-rsp ≡ just 0)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 0)

    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 0
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     (λ eq → addr-disjoint (sym eq))))
                       mem-tag-s2

    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 0
    mem-tag-s4 = mem-tag-s3

    -- Memory at new-rsp + 8 = addr-x (set in s3, preserved in s4)
    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just addr-x
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just addr-x
    mem-val-s4 = mem-val-s3

    -- THE KEY: Construct InlAtS validity directly from memory proofs!
    -- NO encode-inl-construct postulate needed!
    inl-valid-proof : InlAtS addr-x new-rsp (memory s4)
    inl-valid-proof = inl-at-s mem-tag-s4 mem-val-s4

    -- r14 preserved
    r14-preserved : readReg (regs s4) r14 ≡ readReg (regs s) r14
    r14-preserved = trans (readReg-writeReg-rax-r14 (regs s3) (readReg (regs s3) rsp))
                          (readReg-writeReg-rsp-r14 (regs s) new-rsp)

    -- r15 preserved
    r15-preserved : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-preserved = trans (readReg-writeReg-rax-r15 (regs s3) (readReg (regs s3) rsp))
                          (readReg-writeReg-rsp-r15 (regs s) new-rsp)

    -- rbp preserved
    rbp-preserved : readReg (regs s4) rbp ≡ readReg (regs s) rbp
    rbp-preserved = trans (readReg-writeReg-rax-rbp (regs s3) (readReg (regs s3) rsp))
                          (readReg-writeReg-rsp-rbp (regs s) new-rsp)

    -- Stack invariant preserved (using helper pattern)
    -- rsp in s4 is new-rsp (threads through s1-s4 unchanged after s1)
    rsp-s4-eq : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4-eq = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp))
                       refl

    -- r15 in s4 equals r15 in s (same as r15-preserved but explicit type)
    r15-s4-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4-eq = r15-preserved

    -- Stack invariant helper: transform from s to s4
    stack-inv-helper : StackInvariant s → StackInvariant s4
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-s4-eq r15≡0)
    stack-inv-helper (stack-below-r15 rsp≤r15) =
      stack-below-r15 (subst₂ _≤_ (sym rsp-s4-eq) (sym r15-s4-eq)
                               (≤-trans (m∸n≤m orig-rsp 16) rsp≤r15))

    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-helper stack-inv

    -- rsp > 16: follows from rsp-bound-after-stack-op giving rsp > 40, which implies rsp > 16
    open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
    open import Data.Nat using (z≤n; s≤s)

    rsp>16' : readReg (regs s4) rsp > 16
    rsp>16' = ≤-trans 17≤41 (rsp-bound-after-stack-op s4)
      where
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    -- RbpInvariant: new-rsp ≤ orig-rsp ≤ orig-rbp
    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    rbp-inv' : RbpInvariant s4
    rbp-inv' = record { rsp≤rbp = new-rsp≤rbp }
      where
        new-rsp≤orig-rsp : new-rsp ≤ orig-rsp
        new-rsp≤orig-rsp = m∸n≤m orig-rsp 16
        orig-rsp≤orig-rbp : orig-rsp ≤ orig-rbp
        orig-rsp≤orig-rbp = RbpInvariant.rsp≤rbp rbp-inv
        new-rsp≤orig-rbp : new-rsp ≤ orig-rbp
        new-rsp≤orig-rbp = ≤-trans new-rsp≤orig-rsp orig-rsp≤orig-rbp
        new-rsp≤rbp : readReg (regs s4) rsp ≤ readReg (regs s4) rbp
        new-rsp≤rbp = subst₂ _≤_ (sym rsp-s4-eq) (sym rbp-preserved) new-rsp≤orig-rbp
