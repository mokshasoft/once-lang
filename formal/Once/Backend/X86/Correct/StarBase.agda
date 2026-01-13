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
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; r15-unused; r15-in-heap; r15-in-code; RbpInvariant; stack-inv-preserved-unchanged)
open import Once.Backend.Common.MemoryRegions using (region-of; code; heap; stack; stack-code-disjoint)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; rsp-bound-to-capacity; capacity-2-to-rsp-bound;
         capacity-preserved-rsp-unchanged; rsp-bound-preserved-unchanged; slots)
open import Once.Backend.X86.Postulates using (rsp-in-stack-after-stack-op)
open import Once.Backend.X86.Correct.ClosureWellFormed using (ClosureWellFormed)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; fst-valid; snd-valid;
         ValidAt; valid-unit; valid-pair; valid-inl; valid-inr;
         valid-closure; valid-eff; valid-fix;
         PairAtS; InlAtS; InrAtS; ClosureAtS)
open import Once.Postulates
  using (encode-pair-fst; encode-pair-snd; encode-fix-unwrap; encode-fix-wrap)

open import Data.Nat using (_>_)
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
--
-- closure-addr: Runtime heap address where the closure is stored.
--   This is needed by apply to look up the closure in memory.
--   For curry, this is the address returned in rax.
--   For pair ⟨curry f, g⟩, this is stored at pair-addr (fst).
data ClosureWFOutput (prog : Program) : Set₁ where
  no-closure : ClosureWFOutput prog
  has-closure : ∀ {A B : Type}
                (closure-addr code-ptr env-addr : ℕ)
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
    -- D041: Memory at code-region addresses preserved
    -- IR only writes to stack region, code region is disjoint from stack (stack-code-disjoint)
    -- Therefore code addresses are never written by IR execution
    ir-mem-code   : ∀ addr → region-of addr ≡ code → readMem (memory s') addr ≡ readMem (memory s) addr
    -- D041: Memory at heap-region addresses preserved
    -- IR only writes to stack region, heap region is disjoint from stack (stack-heap-disjoint)
    -- Therefore heap addresses are never written by IR execution
    ir-mem-heap   : ∀ addr → region-of addr ≡ heap → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-stack-inv  : StackInvariant s'
    -- Abstract stack capacity (D041 - replaces concrete rsp > slots 2)
    ir-capacity   : StackCapacity s' 2
    -- RbpInvariant preserved: rsp s' ≤ rbp s' (needed for memory disjointness)
    ir-rbp-inv    : RbpInvariant s'
    -- Optional closure well-formedness (produced by curry, consumed by apply)
    ir-closure-wf : ClosureWFOutput prog

open IRStarResult public

-- | Derived: concrete rsp > slots 2 bound from abstract capacity
-- This replaces the removed ir-rsp-bound field
ir-rsp-bound : ∀ {A B ir prog s s' x offset} →
  IRStarResult {A} {B} ir prog s s' x offset →
  readReg (regs s') rsp > slots 2
ir-rsp-bound res = capacity-2-to-rsp-bound _ (ir-capacity res)

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
  readReg (regs s) rsp > slots 2 →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- IRStarResultV: Validity-Based Result Type
--
-- Like IRStarResult, but uses ValidAt instead of encode equality.
-- This enables postulate-free correctness proofs.
------------------------------------------------------------------------

-- | Validity-based IR execution result
-- Replaces ir-rax : rax ≡ encode (eval ir x) with
--          ir-result-valid : ValidAt (eval ir x) rax memory
record IRStarResultV {A B : Type} (ir : IR A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    -- Execution properties (same as IRStarResult)
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir

    -- NEW: Validity-based correctness (replaces ir-rax)
    -- Says "rax points to a valid representation of eval ir x in memory"
    ir-result-valid : ValidAt (eval ir x) (readReg (regs s') rax) (memory s')

    -- Register preservation (same as IRStarResult)
    ir-r14        : readReg (regs s') r14 ≡ readReg (regs s) r14
    ir-r15        : readReg (regs s') r15 ≡ readReg (regs s) r15
    ir-rbp        : readReg (regs s') rbp ≡ readReg (regs s) rbp

    -- Memory preservation (same as IRStarResult)
    ir-mem        : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    ir-mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    ir-mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    ir-mem-above  : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-mem-at-0   : readMem (memory s') 0 ≡ readMem (memory s) 0
    ir-mem-code   : ∀ addr → region-of addr ≡ code → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-mem-heap   : ∀ addr → region-of addr ≡ heap → readMem (memory s') addr ≡ readMem (memory s) addr

    -- Invariants (same as IRStarResult)
    ir-stack-inv  : StackInvariant s'
    ir-capacity   : StackCapacity s' 2
    ir-rbp-inv    : RbpInvariant s'
    ir-closure-wf : ClosureWFOutput prog

open IRStarResultV public using ()
  renaming ( ir-star to ir-star-v; ir-halted to ir-halted-v; ir-pc to ir-pc-v
           ; ir-result-valid to ir-result-valid
           ; ir-r14 to ir-r14-v; ir-r15 to ir-r15-v; ir-rbp to ir-rbp-v
           ; ir-mem to ir-mem-v; ir-mem-rbp to ir-mem-rbp-v; ir-mem-rbp+8 to ir-mem-rbp+8-v
           ; ir-mem-above to ir-mem-above-v; ir-mem-at-0 to ir-mem-at-0-v
           ; ir-mem-code to ir-mem-code-v; ir-mem-heap to ir-mem-heap-v
           ; ir-stack-inv to ir-stack-inv-v; ir-capacity to ir-capacity-v
           ; ir-rbp-inv to ir-rbp-inv-v; ir-closure-wf to ir-closure-wf-v )

-- | Derived: concrete rsp > slots 2 bound from abstract capacity
ir-rsp-bound-v : ∀ {A B ir prog s s' x offset} →
  IRStarResultV {A} {B} ir prog s s' x offset →
  readReg (regs s') rsp > slots 2
ir-rsp-bound-v res = capacity-2-to-rsp-bound _ (IRStarResultV.ir-capacity res)

------------------------------------------------------------------------
-- IRRunnerV: Validity-Based Recursive IR Runner
------------------------------------------------------------------------

-- | Validity-based recursive IR runner
-- Like IRRunner, but takes ValidAt precondition and returns ValidAt postcondition.
-- This enables threading validity through recursive IR execution without encode.
IRRunnerV : Set₁
IRRunnerV = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State)
              (addr-in : ℕ) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  ValidAt x addr-in (memory s) →  -- Input validity (replaces encode x)
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)

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
  readReg (regs s) rsp > slots 2 →
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
  { rbp-frame = RbpInvariant.rbp-frame rbp-inv
  ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
  ; frame-bound = subst (sp-addr (RbpInvariant.rbp-frame rbp-inv) ≥_) (sym rsp-eq)
                        (RbpInvariant.frame-bound rbp-inv)
  }
  where
    open import Data.Nat using (_≤_; _≥_)
    open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- Simple Star proofs (single-step, no recursion)
------------------------------------------------------------------------

-- | Star-based id execution
run-id-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResult (id {A}) prog s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (id {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      -- NEW: Capacity preserved when rsp unchanged
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- id doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- id doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- id doesn't produce a closure
    }

-- | Star-based terminal execution
run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
  in ∃[ s' ] IRStarResult (terminal {A}) prog s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) 0
      rbp-eq = readReg-writeReg-rax-rbp (regs s) 0
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- terminal doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- terminal doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- terminal doesn't produce a closure
    }

-- | Star-based fold execution
run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
  in ∃[ s' ] IRStarResult (fold {F}) prog s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (fold {F}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- fold doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- fold doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- fold doesn't produce a closure
    }

-- | Star-based unfold execution
run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
  in ∃[ s' ] IRStarResult (unfold {F}) prog s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- unfold doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- unfold doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- unfold doesn't produce a closure
    }

-- | Star-based arr execution
run-arr-star : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode {A ⇒ B} fn →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (arr {A} {B}) prog s s' fn (length prefix)
run-arr-star {A} {B} prefix suffix fn s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-arr-at-offset {A} {B} prefix suffix fn s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- arr doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- arr doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- arr doesn't produce a closure
    }

-- | Star-based fst execution (uses encode-pair-fst axiom)
run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (fst {A} {B}) prog s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- fst doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- fst doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- fst doesn't produce a closure
    }

-- | Star-based snd execution (uses encode-pair-snd axiom)
run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (snd {A} {B}) prog s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp-sufficient rbp-inv =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- snd doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- snd doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
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
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (fst {A} {B}) prog s s' (a , b) (length prefix)
run-fst-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp-sufficient rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = fst-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- fst-v doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- fst-v doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
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
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (snd {A} {B}) prog s s' (a , b) (length prefix)
run-snd-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp-sufficient rbp-inv =
  let mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = snd-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
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
    ; ir-mem-code = λ _ _ → refl  -- snd-v doesn't write memory
    ; ir-mem-heap = λ _ _ → refl  -- snd-v doesn't write memory
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure  -- snd-v doesn't produce a closure
    }


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
    readReg (regs s) rsp > slots 2 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (Prim {A} {B} name) ++ suffix
    in ∃[ s' ] IRStarResult (Prim {A} {B} name) prog s s' x (length prefix)

------------------------------------------------------------------------
-- Validity-Based Star Proofs (Phase 4: Simple Producers)
--
-- These return IRStarResultV with ValidAt, eliminating encode postulates.
-- Clean interface: ValidAt x rdi m replaces rdi ≡ encode x
-- No explicit address parameters - rdi is implicitly the input address.
------------------------------------------------------------------------

-- | Validity-based id execution
-- Input validity at rdi → output validity at rax (same address, id copies rdi to rax)
run-id-star-vv : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →  -- Clean: validity at rdi
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResultV (id {A}) prog s s' x (length prefix)
run-id-star-vv {A} prefix suffix x s h-false pc-eq input-valid stack-inv rsp-sufficient rbp-inv =
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
      s' : State
      s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                    ; pc = pc s +ℕ 1 }
      fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)
      step-eq : step prog s ≡ just s'
      step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                      (execMov-reg-reg s rax rdi)
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
      -- Key: rax s' = rdi s, memory unchanged
      rax-eq : readReg (regs s') rax ≡ readReg (regs s) rdi
      rax-eq = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)
      result-valid : ValidAt x (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt x a (memory s')) (sym rax-eq) input-valid
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h-false
    ; ir-pc = cong (_+ℕ 1) pc-eq
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-at-0 = refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based terminal execution
-- Result is tt at address 0, so valid-unit (no input validity needed)
run-terminal-star-vv : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
  in ∃[ s' ] IRStarResultV (terminal {A}) prog s s' x (length prefix)
run-terminal-star-vv {A} prefix suffix x s h-false pc-eq stack-inv rsp-sufficient rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) 0
      rbp-eq = readReg-writeReg-rax-rbp (regs s) 0
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
      -- rax s' = 0, eval terminal x = tt, so ValidAt tt 0 m = valid-unit
      result-valid : ValidAt {Unit} tt (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt {Unit} tt a (memory s')) (sym rax-eq') valid-unit
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) 0
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) 0
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-at-0 = refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based fold execution
-- Input x : ⟦ F ⟧ valid at rdi → output (wrap x) : Fix F valid at rax
run-fold-star-vv : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →  -- Clean: validity at rdi
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
  in ∃[ s' ] IRStarResultV (fold {F}) prog s s' x (length prefix)
run-fold-star-vv {F} prefix suffix x s h-false pc-eq input-valid stack-inv rsp-sufficient rbp-inv =
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
      s' : State
      s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                    ; pc = pc s +ℕ 1 }
      fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)
      step-eq : step prog s ≡ just s'
      step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                      (execMov-reg-reg s rax rdi)
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 (rsp-bound-to-capacity 2 s (rsp-in-stack-after-stack-op s) rsp-sufficient) rsp-eq
      -- Key: rax s' = rdi s, memory unchanged
      rax-eq : readReg (regs s') rax ≡ readReg (regs s) rdi
      rax-eq = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)
      result-valid : ValidAt (wrap x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt (wrap x) a (memory s')) (sym rax-eq) (valid-fix input-valid)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h-false
    ; ir-pc = cong (_+ℕ 1) pc-eq
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-at-0 = refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }
