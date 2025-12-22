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
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single)
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAt; fst-valid; snd-valid)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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
    ir-stack-inv  : StackInvariant s'
    ir-rsp-bound  : readReg (regs s') rsp > 16

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
-- Simple Star proofs (single-step, no recursion)
------------------------------------------------------------------------

-- | Star-based id execution
run-id-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A} {A} id ++ suffix
  in ∃[ s' ] IRStarResult {A} {A} id prog s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let (s' , step-eq , h' , pc' , rax-eq') = run-id-at-offset {A} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {A} {A} id ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Star-based terminal execution
run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix
  in ∃[ s' ] IRStarResult {A} {Unit} terminal prog s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv rsp>16 =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 {A} {Unit} terminal ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym encode-unit)
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) 0
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) 0
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) 0
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       (readReg-writeReg-rax-rsp (regs s) 0)
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) 0)
    }

-- | Star-based fold execution
run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix
  in ∃[ s' ] IRStarResult {F} {Fix F} fold prog s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let (s' , step-eq , h' , pc' , rax-eq') = run-fold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {F} {Fix F} fold ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-fix-wrap x))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Star-based unfold execution
run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix
  in ∃[ s' ] IRStarResult {Fix F} {F} unfold prog s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let (s' , step-eq , h' , pc' , rax-eq') = run-unfold-at-offset {F} prefix suffix x s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {Fix F} {F} unfold ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-fix-unwrap x))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Star-based arr execution
run-arr-star : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode {A ⇒ B} fn →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix
  in ∃[ s' ] IRStarResult {A ⇒ B} {Eff A B} arr prog s s' fn (length prefix)
run-arr-star {A} {B} prefix suffix fn s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let (s' , step-eq , h' , pc' , rax-eq') = run-arr-at-offset {A} {B} prefix suffix fn s h-false pc-eq rdi-eq
      prog = prefix ++ compile-x86 {A ⇒ B} {Eff A B} arr ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = trans rax-eq' (sym (encode-arr-identity {A} {B} fn))
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Star-based fst execution (uses encode-pair-fst axiom)
run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {A} fst prog s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Star-based snd execution (uses encode-pair-snd axiom)
run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {B} snd prog s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  let a = proj₁ x
      b = proj₂ x
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
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
  let prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {A} fst prog s s' (a , b) (length prefix)
run-fst-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 =
  let mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = fst-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-fst-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {A} fst ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }

-- | Postulate-free snd: uses PairAt validity instead of axiom
run-snd-star-v : ∀ {A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode (a , b) →
  PairAt a b (encode (a , b)) (memory s) →  -- Validity precondition (PROVEN by allocation)
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {B} snd prog s s' (a , b) (length prefix)
run-snd-star-v {A} {B} prefix suffix a b s h-false pc-eq rdi-eq pair-valid stack-inv rsp>16 =
  let mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = snd-valid pair-valid
      (s' , step-eq , h' , pc' , rax-eq') = run-snd-at-offset {A} {B} prefix suffix a b s h-false pc-eq rdi-eq mem-eq
      prog = prefix ++ compile-x86 {A * B} {B} snd ++ suffix
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-rax = rax-eq'
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
    ; ir-mem = refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    ; ir-rsp-bound = rsp>16-preserved-unchanged s s' rsp>16
                       (readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi))
    }
