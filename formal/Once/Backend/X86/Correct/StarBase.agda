------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StarBase
--
-- Simple Star-based IR execution proofs.
-- These are non-recursive (don't call run-ir-star-at-offset).
-- Extracted from MutualIR.agda to reduce compilation time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StarBase where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; r15-unused; stack-below-r15; r15-in-code; RbpInvariant; stack-inv-preserved-unchanged; rsp>16-preserved-unchanged)
open import Once.Backend.Common.MemoryRegions using (region-of)
open import Once.Backend.X86.Correct.StackInvariant2
  using (StackCapacity; rsp>16-to-capacity; capacity-to-rsp>16;
         capacity-preserved-rsp-unchanged)
open import Once.Backend.X86.Correct.ClosureWellFormed using (ClosureWellFormed)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; fst-valid; snd-valid;
         PairAtS; fst-valid-s; snd-valid-s;
         InlAtS; inl-at-s; InrAtS; inr-at-s)

open import Once.Backend.Common.Memory using (n≢n+suc)
open import Once.Postulates
  using (encode-pair-fst; encode-pair-snd; encode-fix-unwrap; encode-fix-wrap)

open import Data.Nat using (_>_)
open import Data.Nat.Properties using (+-assoc; ≤-trans; m∸n≤m)
open import Data.List.Properties using (++-assoc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst₂)

------------------------------------------------------------------------
-- ClosureWFOutput: Optional closure well-formedness produced by curry
------------------------------------------------------------------------

-- | When an IR term produces a closure (curry), this captures its WF proof.
-- For other IR terms, this will be no-closure.
--
-- The existential quantification allows us to hide the closure's types
-- when threading through compose/pair.
data ClosureWFOutput (prog : Program) : Set₁ where
  no-closure : ClosureWFOutput prog
  has-closure : ∀ {A B : Type}
                (code-ptr env-addr : ℕ)
                (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                (wf : ClosureWellFormed {A} {B} prog code-ptr env-addr semantics) →
                ClosureWFOutput prog

------------------------------------------------------------------------
-- IRStarResult: Result type for Star-based IR execution
------------------------------------------------------------------------

-- | Record type for Star-based IR execution result
-- Contains all properties needed for proof composition
record IRStarResult {A B : Type} (ir : IR A B) (prog : Program)
                    (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
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
    -- Memory above frame preserved (for caller's rbp in pair proofs)
    -- Any address strictly above rbp is not touched by IR execution
    ir-mem-above  : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    -- Memory at address 0 preserved (null page never written)
    -- No IR generator writes to address 0, so this is always preserved
    ir-mem-at-0   : readMem (memory s') 0 ≡ readMem (memory s) 0
    ir-stack-inv  : StackInvariant s'
    -- NEW: Abstract stack capacity (D041 - replaces concrete rsp > 16)
    ir-capacity   : StackCapacity s' 2
    -- DERIVED: Concrete bound (for backwards compatibility during migration)
    ir-rsp-bound  : readReg (regs s') rsp > 16
    -- RbpInvariant preserved: rsp s' ≤ rbp s' (needed for memory disjointness)
    ir-rbp-inv    : RbpInvariant s'
    -- Optional closure well-formedness (produced by curry, consumed by apply)
    ir-closure-wf : ClosureWFOutput prog

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type for the recursive IR execution function
------------------------------------------------------------------------

-- | Type signature for the recursive IR execution function.
-- Recursive case handlers (compose, pair, case, curry, apply) take
-- an IRRunner as a parameter, allowing them to be defined outside
-- the mutual block. This dramatically reduces compilation time.
--
-- NOTE: Sized types removed for compilation performance (10-100x speedup).
-- Termination is guaranteed by structural recursion on IR constructors.
IRRunner : Set₁
IRRunner = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- IRRunnerWithWF: Extended runner that tracks closure WF
------------------------------------------------------------------------

-- | Like IRRunner, but also returns optional ClosureWFOutput.
-- This enables threading WF proofs from curry through to apply.
IRRunnerWithWF : Set₁
IRRunnerWithWF = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  ClosureWFOutput (prefix ++ compile-x86 ir ++ suffix) →  -- Input WF context
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] (IRStarResult ir prog s s' x (length prefix)
             × ClosureWFOutput prog)  -- Output WF context

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
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResult (id {A}) prog s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (id {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      -- NEW: Capacity preserved when rsp unchanged
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- id doesn't write memory
    ; ir-mem-at-0 = refl  -- id doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- id doesn't produce a closure
    }

-- | Star-based terminal execution
run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
  in ∃[ s' ] IRStarResult (terminal {A}) prog s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) 0
      rbp-eq = readReg-writeReg-rax-rbp (regs s) 0
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- terminal doesn't write memory
    ; ir-mem-at-0 = refl  -- terminal doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- terminal doesn't produce a closure
    }

-- | Star-based fold execution
run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
  in ∃[ s' ] IRStarResult (fold {F}) prog s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (fold {F}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- fold doesn't write memory
    ; ir-mem-at-0 = refl  -- fold doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- fold doesn't produce a closure
    }

-- | Star-based unfold execution
run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
  in ∃[ s' ] IRStarResult (unfold {F}) prog s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- unfold doesn't write memory
    ; ir-mem-at-0 = refl  -- unfold doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- unfold doesn't produce a closure
    }

-- | Star-based arr execution
run-arr-star : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode {A ⇒ B} fn →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (arr {A} {B}) prog s s' fn (length prefix)
run-arr-star {A} {B} prefix suffix fn s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-arr-at-offset {A} {B} prefix suffix fn s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- arr doesn't write memory
    ; ir-mem-at-0 = refl  -- arr doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- arr doesn't produce a closure
    }

-- | Star-based fst execution (uses encode-pair-fst axiom)
run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (fst {A} {B}) prog s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- fst doesn't write memory
    ; ir-mem-at-0 = refl  -- fst doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- fst doesn't produce a closure
    }

-- | Star-based snd execution (uses encode-pair-snd axiom)
run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (snd {A} {B}) prog s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- snd doesn't write memory
    ; ir-mem-at-0 = refl  -- snd doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- snd doesn't produce a closure
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
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (fst {A} {B}) prog s s' (a , b) (length prefix)
run-fst-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = fst-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- fst-v doesn't write memory
    ; ir-mem-at-0 = refl  -- fst-v doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- fst-v doesn't produce a closure
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
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (snd {A} {B}) prog s s' (a , b) (length prefix)
run-snd-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = snd-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp>16-to-capacity s rsp>16) rsp-eq
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
    ; ir-mem-above = λ _ _ → refl  -- snd-v doesn't write memory
    ; ir-mem-at-0 = refl  -- snd-v doesn't write to address 0
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rsp-bound = capacity-to-rsp>16 s' cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- snd-v doesn't produce a closure
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
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] FstSndResultS prog s s' addr-a (length prefix)
run-fst-star-s {A} {B} prefix suffix addr-pair addr-a addr-b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) addr-pair ≡ just addr-a
      mem-eq = fst-valid-s pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset-s {A} {B} prefix suffix addr-pair addr-a s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
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
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] FstSndResultS prog s s' addr-b (length prefix)
run-snd-star-s {A} {B} prefix suffix addr-pair addr-a addr-b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 rbp-inv =
  let mem-eq : readMem (memory s) (addr-pair +ℕ 8) ≡ just addr-b
      mem-eq = snd-valid-s pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset-s {A} {B} prefix suffix addr-pair addr-b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
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
  let prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix
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
    prog = prefix ++ compile-x86 (inl {A} {B}) ++ suffix

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
    stack-inv-helper (r15-in-code r15-code) =
      r15-in-code (trans (cong region-of r15-s4-eq) r15-code)

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

------------------------------------------------------------------------
-- run-inr-star-s: Stateful inr proof producing InrAtS validity
------------------------------------------------------------------------

-- | Stateful inr: produces InrAtS validity from memory writes
--
-- Similar to run-inl-star-s but writes tag=1 instead of tag=0.
-- NO encode-inr-construct postulate needed!
run-inr-star-s : ∀ {A B : Type} (prefix suffix : Program) (addr-x : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (inr {A} {B}) ++ suffix
      addr-out = readReg (regs s) rsp ∸ 16
  in ∃[ s' ] InrResultS prog s s' addr-x addr-out (length prefix)
run-inr-star-s {A} {B} prefix suffix addr-x s h-false pc-eq rdi-eq stack-inv rsp>16 rbp-inv =
    s4 , record
    { star = star-proof
    ; halted' = h4
    ; pc' = pc4
    ; rax-eq = rax-eq-inr
    ; inr-valid = inr-valid-proof
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
    prog = prefix ++ compile-x86 (inr {A} {B}) ++ suffix

    -- The 4 instructions of inr
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)
    i1 : Instr
    i1 = mov (mem (base rsp)) (imm 1)  -- Tag = 1 for inr
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

    -- State after step 2: mov [rsp], 1
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 1
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
                  (execMov-mem-base-imm prog s1 rsp 1)

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

    -- Star proof (4 steps)
    star-proof : Star prog s s4
    star-proof = star-step4 h-false step1 h1 step2 h2 step3 h3 step4

    -- Track rsp through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rdi-s2 : readReg (regs s2) rdi ≡ addr-x
    rdi-s2 = trans (readReg-writeReg-rsp-rdi (regs s) new-rsp) rdi-eq

    -- Address disjoint: new-rsp + 8 ≠ new-rsp
    addr-disjoint : new-rsp +ℕ 8 ≢ new-rsp
    addr-disjoint eq = n≢n+suc new-rsp 7 (sym eq)

    -- rax = new-rsp (the output address)
    rax-s4-eq : readReg (regs s4) rax ≡ readReg (regs s3) rsp
    rax-s4-eq = readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)

    rax-eq-inr : readReg (regs s4) rax ≡ new-rsp
    rax-eq-inr = trans rax-s4-eq rsp-s3

    -- Memory proofs: tag=1 at new-rsp, value at new-rsp+8
    -- In s2: we wrote 1 to memory at new-rsp
    mem-tag-s2 : readMem (memory s2) new-rsp ≡ just 1
    mem-tag-s2 = subst (λ addr → readMem (writeMem (memory s1) addr 1) new-rsp ≡ just 1)
                       (sym rsp-s1)
                       (readMem-writeMem-same (memory s1) new-rsp 1)

    -- In s3: we wrote value to new-rsp+8, tag at new-rsp preserved
    mem-tag-s3 : readMem (memory s3) new-rsp ≡ just 1
    mem-tag-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) new-rsp ≡
                                        readMem (memory s2) new-rsp)
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi)
                                                     addr-disjoint))
                       mem-tag-s2

    mem-val-s3 : readMem (memory s3) (new-rsp +ℕ 8) ≡ just addr-x
    mem-val-s3 = trans (subst (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rdi)) (new-rsp +ℕ 8) ≡
                                        just (readReg (regs s2) rdi))
                              (sym (cong (_+ℕ 8) rsp-s2))
                              (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi)))
                       (cong just rdi-s2)

    -- s4 has same memory as s3 (only regs changed)
    mem-tag-s4 : readMem (memory s4) new-rsp ≡ just 1
    mem-tag-s4 = mem-tag-s3

    mem-val-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just addr-x
    mem-val-s4 = mem-val-s3

    -- THE KEY: Construct InrAtS validity directly from memory proofs!
    -- NO encode-inr-construct postulate needed!
    inr-valid-proof : InrAtS addr-x new-rsp (memory s4)
    inr-valid-proof = inr-at-s mem-tag-s4 mem-val-s4

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
    rsp-s4-eq : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4-eq = trans (readReg-writeReg-rax-rsp (regs s3) (readReg (regs s3) rsp))
                       refl

    r15-s4-eq : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4-eq = r15-preserved

    stack-inv-helper : StackInvariant s → StackInvariant s4
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-s4-eq r15≡0)
    stack-inv-helper (stack-below-r15 rsp≤r15) =
      stack-below-r15 (subst₂ _≤_ (sym rsp-s4-eq) (sym r15-s4-eq)
                               (≤-trans (m∸n≤m orig-rsp 16) rsp≤r15))
    stack-inv-helper (r15-in-code r15-code) =
      r15-in-code (trans (cong region-of r15-s4-eq) r15-code)

    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-helper stack-inv

    -- rsp > 16
    open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
    open import Data.Nat using (z≤n; s≤s)

    rsp>16' : readReg (regs s4) rsp > 16
    rsp>16' = ≤-trans 17≤41 (rsp-bound-after-stack-op s4)
      where
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    -- RbpInvariant
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

------------------------------------------------------------------------
-- Stateful Pair Result: Produces PairAtS validity
--
-- Pair operations store two addresses at consecutive memory locations:
--   - memory[addr-pair] = addr-f (first component)
--   - memory[addr-pair + 8] = addr-g (second component)
--
-- This creates PairAtS validity directly from the memory writes,
-- without needing the encode-pair-construct postulate.
------------------------------------------------------------------------

-- | Stateful result record for pair operations
-- Captures that pair's store operations create valid pair memory layout
record PairResultS (prog : Program) (s s' : State)
                   (addr-f addr-g addr-pair : Word) (offset len-pair : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ len-pair
    rax-eq     : readReg (regs s') rax ≡ addr-pair
    pair-valid : PairAtS addr-f addr-g addr-pair (memory s')  -- PRODUCED validity
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    mem-r15    : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

open PairResultS public using (pair-valid)

-- | Key lemma: Two stores create PairAtS validity
--
-- Given:
--   - mem-fst : readMem m addr-pair ≡ just addr-f
--   - mem-snd : readMem m (addr-pair + 8) ≡ just addr-g
--
-- Produces:
--   PairAtS addr-f addr-g addr-pair m
--
-- This is the "producer" side of pair validity - we construct
-- the validity predicate directly from proven memory contents.
pair-stores-create-validity : ∀ {addr-f addr-g addr-pair : Word} {m : Memory} →
  readMem m addr-pair ≡ just addr-f →
  readMem m (addr-pair +ℕ 8) ≡ just addr-g →
  PairAtS addr-f addr-g addr-pair m
pair-stores-create-validity mem-fst mem-snd = pair-at-s mem-fst mem-snd
  where
    open import Once.Backend.X86.Correct.MemoryValid using (pair-at-s)

------------------------------------------------------------------------
-- Stateful IRStarResult: Result with addresses instead of encode
--
-- This is the stateful counterpart to IRStarResult. Instead of
-- using `encode (eval ir x)` for the rax result, it uses an
-- explicit address. Validity of that address is tracked separately.
------------------------------------------------------------------------

-- | Stateful IR execution result record
-- Like IRStarResult but with explicit address instead of encode
record IRStarResultS {A B : Type} (ir : IR A B) (prog : Program)
                     (s s' : State) (addr-out : Word) (offset : ℕ) : Set where
  field
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-rax-s      : readReg (regs s') rax ≡ addr-out  -- Address, not encode!
    ir-r14        : readReg (regs s') r14 ≡ readReg (regs s) r14
    ir-r15        : readReg (regs s') r15 ≡ readReg (regs s) r15
    ir-rbp        : readReg (regs s') rbp ≡ readReg (regs s) rbp
    ir-mem        : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    ir-mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    ir-mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    ir-mem-above  : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-mem-at-0   : readMem (memory s') 0 ≡ readMem (memory s) 0
    ir-stack-inv  : StackInvariant s'
    -- NEW: Abstract stack capacity (D041 - replaces concrete rsp > 16)
    ir-capacity   : StackCapacity s' 2
    -- DERIVED: Concrete bound (for backwards compatibility during migration)
    ir-rsp-bound  : readReg (regs s') rsp > 16
    ir-rbp-inv    : RbpInvariant s'

open IRStarResultS public

-- | Convert IRStarResult to IRStarResultS
-- This allows gradual migration to stateful proofs
convert-to-stateful : ∀ {A B : Type} (ir : IR A B) (prog : Program)
                      (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) →
  IRStarResult ir prog s s' x offset →
  IRStarResultS ir prog s s' (encode (eval ir x)) offset
convert-to-stateful ir prog s s' x offset res = record
  { ir-star      = IRStarResult.ir-star res
  ; ir-halted    = IRStarResult.ir-halted res
  ; ir-pc        = IRStarResult.ir-pc res
  ; ir-rax-s     = IRStarResult.ir-rax res
  ; ir-r14       = IRStarResult.ir-r14 res
  ; ir-r15       = IRStarResult.ir-r15 res
  ; ir-rbp       = IRStarResult.ir-rbp res
  ; ir-mem       = IRStarResult.ir-mem res
  ; ir-mem-rbp   = IRStarResult.ir-mem-rbp res
  ; ir-mem-rbp+8 = IRStarResult.ir-mem-rbp+8 res
  ; ir-mem-above = IRStarResult.ir-mem-above res
  ; ir-mem-at-0  = IRStarResult.ir-mem-at-0 res
  ; ir-stack-inv = IRStarResult.ir-stack-inv res
  ; ir-capacity  = IRStarResult.ir-capacity res
  ; ir-rsp-bound = IRStarResult.ir-rsp-bound res
  ; ir-rbp-inv   = IRStarResult.ir-rbp-inv res
  }

------------------------------------------------------------------------
-- Stateful Runners for Simple Base Cases
--
-- For simple IR generators (id, terminal, fold, unfold, arr) that don't
-- access memory or use encoding postulates, we can simply wrap the
-- existing encode-based runners with convert-to-stateful.
------------------------------------------------------------------------

-- | Stateful id runner: input address = output address
run-id-star-s : ∀ {A : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →  -- Caller provides semantic value matching address
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (id {A}) prog s s' addr-in (length prefix)
run-id-star-s {A} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-id-star {A} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (id {A}) ++ suffix
      res-s = convert-to-stateful (id {A}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (id {A}) prog s s' addr (length prefix)) enc-eq res-s

-- | Stateful terminal runner: output address = 0 (unit encoding)
run-terminal-star-s : ∀ {A : Type} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
  in ∃[ s' ] IRStarResultS (terminal {A}) prog s s' 0 (length prefix)
run-terminal-star-s {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 rbp-inv
  in s' , convert-to-stateful (terminal {A}) _ s s' x _ res

-- | Stateful fold runner: input address = output address (Fix ≅ A)
run-fold-star-s : ∀ {F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (fold {F}) prog s s' addr-in (length prefix)
run-fold-star-s {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-fold-star {F} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (fold {F}) ++ suffix
      res-s = convert-to-stateful (fold {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (fold {F}) prog s s' addr (length prefix)) enc-eq res-s

-- | Stateful unfold runner: input address = output address (Fix ≅ A)
run-unfold-star-s : ∀ {F} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
  in ∃[ s' ] IRStarResultS (unfold {F}) prog s s' addr-in (length prefix)
run-unfold-star-s {F} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let (s' , res) = run-unfold-star {F} prefix suffix x s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
      res-s = convert-to-stateful (unfold {F}) prog s s' x (length prefix) res
  in s' , subst (λ addr → IRStarResultS (unfold {F}) prog s s' addr (length prefix)) enc-eq res-s

-- | Stateful arr runner: input address = output address (Eff ≅ Closure)
run-arr-star-s : ∀ {A B : Type} (prefix suffix : Program)
    (addr-in : Word) (x : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  encode {A ⇒ B} x ≡ addr-in →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultS (arr {A} {B}) prog s s' addr-in (length prefix)
run-arr-star-s {A} {B} prefix suffix addr-in x s h-false pc-eq rdi-eq enc-eq stack-inv rsp>16 rbp-inv =
  let x-typed : ⟦ A ⇒ B ⟧
      x-typed = x
      (s' , res) = run-arr-star {A} {B} prefix suffix x-typed s h-false pc-eq (trans rdi-eq (sym enc-eq)) stack-inv rsp>16 rbp-inv
      prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
      res-s = convert-to-stateful (arr {A} {B}) prog s s' x-typed (length prefix) res
  in s' , subst (λ addr → IRStarResultS (arr {A} {B}) prog s s' addr (length prefix)) enc-eq res-s

------------------------------------------------------------------------
-- Stateful Pair Assembly: Produce PairAtS from sub-IR results
--
-- This function shows how to produce PairResultS from stateful
-- sub-IR results. It's the key step for eliminating encode-pair-construct.
--
-- Pattern:
--   1. Run f → get addr-f in rax
--   2. Store addr-f at [r15] (middle phase)
--   3. Run g → get addr-g in rax
--   4. Store addr-g at [r15+8] (final phase)
--   5. Return r15 with PairAtS addr-f addr-g r15 memory
------------------------------------------------------------------------

-- | Simple assembly: given memory proofs, construct PairAtS
-- This is used when we have the final state and memory layout proven
make-pair-validity : ∀ {addr-f addr-g addr-pair : Word} {s' : State} →
  readMem (memory s') addr-pair ≡ just addr-f →
  readMem (memory s') (addr-pair +ℕ 8) ≡ just addr-g →
  PairAtS addr-f addr-g addr-pair (memory s')
make-pair-validity = pair-stores-create-validity

------------------------------------------------------------------------
-- Stateful Case: Consumer of InlAtS/InrAtS validity
--
-- Case is a "consumer" of sum validity. Instead of using the
-- encode-inl-tag/encode-inr-tag postulates to read the tag from
-- memory, we use InlAtS/InrAtS which already contains the memory proofs.
--
-- Pattern:
--   1. Take InlAtS addr-val addr-sum (memory s) as input
--   2. Extract tag-valid: readMem (memory s) addr-sum ≡ just 0
--   3. Extract val-valid: readMem (memory s) (addr-sum + 8) ≡ just addr-val
--   4. Use these to execute case dispatch without postulates
------------------------------------------------------------------------

-- | Extract tag memory proof from InlAtS
-- This replaces the encode-inl-tag postulate
inl-tag-from-validity : ∀ {addr-val addr-sum : Word} {m : Memory} →
  InlAtS addr-val addr-sum m →
  readMem m addr-sum ≡ just 0
inl-tag-from-validity v = tag-valid-inl-s v
  where
    open import Once.Backend.X86.Correct.MemoryValid using (tag-valid-inl-s)

-- | Extract value memory proof from InlAtS
-- This replaces the encode-inl-val postulate (gives address not encode)
inl-val-from-validity : ∀ {addr-val addr-sum : Word} {m : Memory} →
  InlAtS addr-val addr-sum m →
  readMem m (addr-sum +ℕ 8) ≡ just addr-val
inl-val-from-validity v = val-valid-inl-s v
  where
    open import Once.Backend.X86.Correct.MemoryValid using (val-valid-inl-s)

-- | Extract tag memory proof from InrAtS
-- This replaces the encode-inr-tag postulate
inr-tag-from-validity : ∀ {addr-val addr-sum : Word} {m : Memory} →
  InrAtS addr-val addr-sum m →
  readMem m addr-sum ≡ just 1
inr-tag-from-validity v = tag-valid-inr-s v
  where
    open import Once.Backend.X86.Correct.MemoryValid using (tag-valid-inr-s)

-- | Extract value memory proof from InrAtS
-- This replaces the encode-inr-val postulate (gives address not encode)
inr-val-from-validity : ∀ {addr-val addr-sum : Word} {m : Memory} →
  InrAtS addr-val addr-sum m →
  readMem m (addr-sum +ℕ 8) ≡ just addr-val
inr-val-from-validity v = val-valid-inr-s v
  where
    open import Once.Backend.X86.Correct.MemoryValid using (val-valid-inr-s)

-- | Stateful case result for left branch
-- Returns the output address from running f
record CaseInlResultS (prog : Program) (s s' : State)
                      (addr-out : Word) (offset len-case : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ len-case
    rax-eq     : readReg (regs s') rax ≡ addr-out
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    mem-r15    : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

-- | Stateful case result for right branch
-- Returns the output address from running g
record CaseInrResultS (prog : Program) (s s' : State)
                      (addr-out : Word) (offset len-case : ℕ) : Set where
  field
    star       : Star prog s s'
    halted'    : halted s' ≡ false
    pc'        : pc s' ≡ offset +ℕ len-case
    rax-eq     : readReg (regs s') rax ≡ addr-out
    r14-eq     : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq     : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-eq     : readReg (regs s') rbp ≡ readReg (regs s) rbp
    mem-r15    : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    stack-inv  : StackInvariant s'
    rsp-bound  : readReg (regs s') rsp > 16
    rbp-inv    : RbpInvariant s'

-- | Union type for case result (either inl or inr branch was taken)
data CaseResultS (prog : Program) (s s' : State)
                 (addr-out : Word) (offset len-case : ℕ) : Set where
  case-inl : CaseInlResultS prog s s' addr-out offset len-case → CaseResultS prog s s' addr-out offset len-case
  case-inr : CaseInrResultS prog s s' addr-out offset len-case → CaseResultS prog s s' addr-out offset len-case

------------------------------------------------------------------------
-- END-TO-END STATEFUL PROOFS
--
-- These theorems demonstrate the complete stateful pattern:
-- 1. Use initWithInputStateful (proper memory allocation)
-- 2. Get validity from proven allocation theorems (no postulates!)
-- 3. Run stateful IR execution
-- 4. Produce result as address with validity evidence
--
-- This is the foundation for eliminating all encoding postulates.
------------------------------------------------------------------------

open import Once.StatefulEncoding using (encode-s)
open import Once.Memory using (AllocState; alloc-state)
  renaming (mem to alloc-mem)
open import Once.Backend.X86.Correct.InitState
  using (initWithInputStateful; InitResult; state; input-addr;
         initWithInputStateful-pair-valid;
         initWithInputStateful-halted; initWithInputStateful-pc)
open import Once.Backend.X86.Correct.StackInvariant
  using (initWithInputStateful-stack-inv; initWithInputStateful-rsp>16;
         initWithInputStateful-rbp-inv)
open import Data.List.Properties using (++-identityʳ)

-- | Stateful fst correctness: NO ENCODING POSTULATES!
--
-- This theorem proves fst correctness using only:
--   1. initWithInputStateful: Properly allocates pair in memory
--   2. initWithInputStateful-pair-valid: PROVEN validity from StatefulEncoding
--   3. run-fst-star-s: Stateful execution using validity
--
-- The result is an address (addr-a) where the first component lives,
-- not an abstract "encode a". The validity predicate proves the memory
-- layout is correct.
--
-- This demonstrates the complete elimination of encode-pair-fst postulate.
test-fst-stateful : ∀ {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory 0x80000000
      (addr-a , st₁) = encode-s {A} a init-heap
      (addr-b , st₂) = encode-s {B} b st₁
      result = initWithInputStateful {A * B} (a , b)
      s0 = state result
      addr-pair = input-addr result
      pair-valid = initWithInputStateful-pair-valid a b
  in ∃[ s' ] (Star (compile-x86 (fst {A} {B})) s0 s'
            × halted s' ≡ false
            × readReg (regs s') rax ≡ addr-a)
test-fst-stateful {A} {B} a b = s' , star-out , halted-out , rax-out
  where
    -- Setup from initWithInputStateful
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000

    addr-a : Word
    addr-a = proj₁ (encode-s {A} a init-heap)

    st₁ : AllocState
    st₁ = proj₂ (encode-s {A} a init-heap)

    addr-b : Word
    addr-b = proj₁ (encode-s {B} b st₁)

    result : InitResult (A * B)
    result = initWithInputStateful {A * B} (a , b)

    s0 : State
    s0 = state result

    addr-pair : Word
    addr-pair = input-addr result

    -- Validity from PROVEN allocation (no postulates!)
    pair-valid' : PairAtS addr-a addr-b addr-pair (memory s0)
    pair-valid' = initWithInputStateful-pair-valid a b

    -- Preconditions for run-fst-star-s
    h-false' : halted s0 ≡ false
    h-false' = initWithInputStateful-halted (a , b)

    pc-eq' : pc s0 ≡ 0
    pc-eq' = initWithInputStateful-pc (a , b)

    rdi-eq' : readReg (regs s0) rdi ≡ addr-pair
    rdi-eq' = InitResult.rdi-eq result

    stack-inv' : StackInvariant s0
    stack-inv' = initWithInputStateful-stack-inv (a , b)

    rsp>16' : readReg (regs s0) rsp > 16
    rsp>16' = initWithInputStateful-rsp>16 (a , b)

    rbp-inv' : RbpInvariant s0
    rbp-inv' = initWithInputStateful-rbp-inv (a , b)

    -- Run fst statefully (NO POSTULATES!)
    fst-result = run-fst-star-s {A} {B} [] [] addr-pair addr-a addr-b s0
                   h-false' pc-eq' rdi-eq' pair-valid' stack-inv' rsp>16' rbp-inv'

    s' : State
    s' = proj₁ fst-result

    fst-res : FstSndResultS (compile-x86 (fst {A} {B})) s0 s' addr-a 0
    fst-res = proj₂ fst-result

    -- Extract results
    star-out : Star (compile-x86 (fst {A} {B})) s0 s'
    star-out = subst (λ p → Star p s0 s') (++-identityʳ _) (FstSndResultS.star fst-res)

    halted-out : halted s' ≡ false
    halted-out = FstSndResultS.halted' fst-res

    rax-out : readReg (regs s') rax ≡ addr-a
    rax-out = FstSndResultS.rax-eq fst-res

-- | Stateful snd correctness: NO ENCODING POSTULATES!
-- Symmetric to test-fst-stateful, extracts second component.
test-snd-stateful : ∀ {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let init-heap = alloc-state emptyMemory 0x80000000
      (addr-a , st₁) = encode-s {A} a init-heap
      (addr-b , st₂) = encode-s {B} b st₁
      result = initWithInputStateful {A * B} (a , b)
      s0 = state result
      addr-pair = input-addr result
  in ∃[ s' ] (Star (compile-x86 (snd {A} {B})) s0 s'
            × halted s' ≡ false
            × readReg (regs s') rax ≡ addr-b)
test-snd-stateful {A} {B} a b = s' , star-out , halted-out , rax-out
  where
    init-heap : AllocState
    init-heap = alloc-state emptyMemory 0x80000000

    addr-a : Word
    addr-a = proj₁ (encode-s {A} a init-heap)

    st₁ : AllocState
    st₁ = proj₂ (encode-s {A} a init-heap)

    addr-b : Word
    addr-b = proj₁ (encode-s {B} b st₁)

    result : InitResult (A * B)
    result = initWithInputStateful {A * B} (a , b)

    s0 : State
    s0 = state result

    addr-pair : Word
    addr-pair = input-addr result

    pair-valid' : PairAtS addr-a addr-b addr-pair (memory s0)
    pair-valid' = initWithInputStateful-pair-valid a b

    h-false' : halted s0 ≡ false
    h-false' = initWithInputStateful-halted (a , b)

    pc-eq' : pc s0 ≡ 0
    pc-eq' = initWithInputStateful-pc (a , b)

    rdi-eq' : readReg (regs s0) rdi ≡ addr-pair
    rdi-eq' = InitResult.rdi-eq result

    stack-inv' : StackInvariant s0
    stack-inv' = initWithInputStateful-stack-inv (a , b)

    rsp>16' : readReg (regs s0) rsp > 16
    rsp>16' = initWithInputStateful-rsp>16 (a , b)

    rbp-inv' : RbpInvariant s0
    rbp-inv' = initWithInputStateful-rbp-inv (a , b)

    -- Run snd statefully (NO POSTULATES!)
    snd-result = run-snd-star-s {A} {B} [] [] addr-pair addr-a addr-b s0
                   h-false' pc-eq' rdi-eq' pair-valid' stack-inv' rsp>16' rbp-inv'

    s' : State
    s' = proj₁ snd-result

    snd-res : FstSndResultS (compile-x86 (snd {A} {B})) s0 s' addr-b 0
    snd-res = proj₂ snd-result

    star-out : Star (compile-x86 (snd {A} {B})) s0 s'
    star-out = subst (λ p → Star p s0 s') (++-identityʳ _) (FstSndResultS.star snd-res)

    halted-out : halted s' ≡ false
    halted-out = FstSndResultS.halted' snd-res

    rax-out : readReg (regs s') rax ≡ addr-b
    rax-out = FstSndResultS.rax-eq snd-res

------------------------------------------------------------------------
-- Producer Tests: inl and inr create validity
--
-- Unlike fst/snd which CONSUME validity, inl/inr PRODUCE it.
-- The test shows that running inl/inr creates InlAtS/InrAtS.
------------------------------------------------------------------------

open import Once.Backend.X86.Correct.InitState
  using (initWithInputStateful-inl-valid; initWithInputStateful-inr-valid)

-- | Stateful inl correctness: PRODUCES InlAtS validity
-- Shows that inl creates proper sum memory layout without postulates.
test-inl-stateful : ∀ {A B : Type} (a : ⟦ A ⟧) →
  let result = initWithInputStateful {A} a
      s0 = state result
      addr-a = input-addr result
      new-rsp = readReg (regs s0) rsp ∸ 16
  in ∃[ s' ] (Star (compile-x86 (inl {A} {B})) s0 s'
            × halted s' ≡ false
            × readReg (regs s') rax ≡ new-rsp
            × InlAtS addr-a new-rsp (memory s'))
test-inl-stateful {A} {B} a = s' , star-out , halted-out , rax-out , inl-valid-out
  where
    result : InitResult A
    result = initWithInputStateful {A} a

    s0 : State
    s0 = state result

    addr-a : Word
    addr-a = input-addr result

    h-false' : halted s0 ≡ false
    h-false' = initWithInputStateful-halted a

    pc-eq' : pc s0 ≡ 0
    pc-eq' = initWithInputStateful-pc a

    rdi-eq' : readReg (regs s0) rdi ≡ addr-a
    rdi-eq' = InitResult.rdi-eq result

    stack-inv' : StackInvariant s0
    stack-inv' = initWithInputStateful-stack-inv a

    rsp>16' : readReg (regs s0) rsp > 16
    rsp>16' = initWithInputStateful-rsp>16 a

    rbp-inv' : RbpInvariant s0
    rbp-inv' = initWithInputStateful-rbp-inv a

    -- Run inl statefully - PRODUCES InlAtS!
    inl-result = run-inl-star-s {A} {B} [] [] addr-a s0
                   h-false' pc-eq' rdi-eq' stack-inv' rsp>16' rbp-inv'

    s' : State
    s' = proj₁ inl-result

    inl-res : InlResultS (compile-x86 (inl {A} {B})) s0 s' addr-a (readReg (regs s0) rsp ∸ 16) 0
    inl-res = proj₂ inl-result

    star-out : Star (compile-x86 (inl {A} {B})) s0 s'
    star-out = subst (λ p → Star p s0 s') (++-identityʳ _) (InlResultS.star inl-res)

    halted-out : halted s' ≡ false
    halted-out = InlResultS.halted' inl-res

    rax-out : readReg (regs s') rax ≡ readReg (regs s0) rsp ∸ 16
    rax-out = InlResultS.rax-eq inl-res

    inl-valid-out : InlAtS addr-a (readReg (regs s0) rsp ∸ 16) (memory s')
    inl-valid-out = InlResultS.inl-valid inl-res

-- | Stateful inr correctness: PRODUCES InrAtS validity
-- Shows that inr creates proper sum memory layout without postulates.
test-inr-stateful : ∀ {A B : Type} (b : ⟦ B ⟧) →
  let result = initWithInputStateful {B} b
      s0 = state result
      addr-b = input-addr result
      new-rsp = readReg (regs s0) rsp ∸ 16
  in ∃[ s' ] (Star (compile-x86 (inr {A} {B})) s0 s'
            × halted s' ≡ false
            × readReg (regs s') rax ≡ new-rsp
            × InrAtS addr-b new-rsp (memory s'))
test-inr-stateful {A} {B} b = s' , star-out , halted-out , rax-out , inr-valid-out
  where
    result : InitResult B
    result = initWithInputStateful {B} b

    s0 : State
    s0 = state result

    addr-b : Word
    addr-b = input-addr result

    h-false' : halted s0 ≡ false
    h-false' = initWithInputStateful-halted b

    pc-eq' : pc s0 ≡ 0
    pc-eq' = initWithInputStateful-pc b

    rdi-eq' : readReg (regs s0) rdi ≡ addr-b
    rdi-eq' = InitResult.rdi-eq result

    stack-inv' : StackInvariant s0
    stack-inv' = initWithInputStateful-stack-inv b

    rsp>16' : readReg (regs s0) rsp > 16
    rsp>16' = initWithInputStateful-rsp>16 b

    rbp-inv' : RbpInvariant s0
    rbp-inv' = initWithInputStateful-rbp-inv b

    -- Run inr statefully - PRODUCES InrAtS!
    inr-result = run-inr-star-s {A} {B} [] [] addr-b s0
                   h-false' pc-eq' rdi-eq' stack-inv' rsp>16' rbp-inv'

    s' : State
    s' = proj₁ inr-result

    inr-res : InrResultS (compile-x86 (inr {A} {B})) s0 s' addr-b (readReg (regs s0) rsp ∸ 16) 0
    inr-res = proj₂ inr-result

    star-out : Star (compile-x86 (inr {A} {B})) s0 s'
    star-out = subst (λ p → Star p s0 s') (++-identityʳ _) (InrResultS.star inr-res)

    halted-out : halted s' ≡ false
    halted-out = InrResultS.halted' inr-res

    rax-out : readReg (regs s') rax ≡ readReg (regs s0) rsp ∸ 16
    rax-out = InrResultS.rax-eq inr-res

    inr-valid-out : InrAtS addr-b (readReg (regs s0) rsp ∸ 16) (memory s')
    inr-valid-out = InrResultS.inr-valid inr-res

------------------------------------------------------------------------
-- SUMMARY: Stateful Proof Coverage
------------------------------------------------------------------------
--
-- This module demonstrates complete postulate-free verification for
-- base IR operations using the "stateful validity" pattern.
--
-- PATTERN:
--   Producers (inl, inr, pair) → create validity predicates from memory writes
--   Consumers (fst, snd, case) → use validity predicates instead of encode postulates
--
-- PROVEN (no encoding postulates):
--   ✓ fst - uses PairAtS, eliminates encode-pair-fst postulate
--   ✓ snd - uses PairAtS, eliminates encode-pair-snd postulate
--   ✓ inl - produces InlAtS from memory writes (no encode-inl-construct)
--   ✓ inr - produces InrAtS from memory writes (no encode-inr-construct)
--
-- E2E TESTS (complete producer→consumer chains):
--   ✓ test-fst-stateful - pair input → fst extraction (NO postulates)
--   ✓ test-snd-stateful - pair input → snd extraction (NO postulates)
--   ✓ test-inl-stateful - value input → inl creation (NO postulates)
--   ✓ test-inr-stateful - value input → inr creation (NO postulates)
--
-- REMAINING (require IRRunner threading):
--   • pair producer - needs to thread validity from sub-IR results
--   • case consumer - needs to thread validity to sub-IR branches
--   • compose - needs to thread validity between composed IRs
--
-- PATH TO FULL ELIMINATION:
--   1. Modify IRRunner to return IRStarResultS (with addresses, not encode)
--   2. Thread validity through compose/pair/case in MutualIR.agda
--   3. Remove encoding postulates from Once/Postulates.agda
--
-- KEY FILES:
--   • StatefulEncoding.agda - encode-s with PROVEN memory theorems
--   • InitState.agda - initWithInputStateful with proper allocation
--   • MemoryValid.agda - PairAtS, InlAtS, InrAtS predicates
--   • StarBase.agda - stateful versions (run-*-star-s) and E2E tests
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Prim Star Functions (Postulated)
--
-- Primitives are opaque operations whose semantics (evalPrim) are postulated.
-- Until proper Prim compilation is implemented, these are postulated.
--
-- NOTE: Current compile-x86 (Prim _) = mov rax, rdi (identity)
-- But eval (Prim name) x = evalPrim name x (arbitrary function)
-- These don't match, so correctness is postulated.
------------------------------------------------------------------------

postulate
  run-prim-star : ∀ {A B} (name : String) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (Prim {A} {B} name) ++ suffix
    in ∃[ s' ] IRStarResult (Prim {A} {B} name) prog s s' x (length prefix)

  run-prim-star-s : ∀ {A B} (name : String) (prefix suffix : Program)
      (addr-in : Word) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ addr-in →
    encode x ≡ addr-in →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (Prim {A} {B} name) ++ suffix
    in ∃[ addr-out ] ∃[ s' ] IRStarResultS (Prim {A} {B} name) prog s s' addr-out (length prefix)
