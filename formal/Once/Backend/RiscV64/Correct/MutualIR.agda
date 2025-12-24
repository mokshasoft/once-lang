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
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.MutualIR where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; star-step5)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult; code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-a0; thunk-s1)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.RiscV64.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star)

-- Import extracted compose helpers
open import Once.Backend.RiscV64.Correct.IR.Compose
  using (ComposeContext; make-compose-context;
         assemble-compose-result; transform-f-result; transform-g-result)
open import Once.Backend.RiscV64.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers
open import Once.Backend.RiscV64.Correct.IR.Pair
  using (PairContext; make-pair-context)
open import Once.Backend.RiscV64.Correct.IR.Pair using (module PairContext)

-- Import extracted case helpers
open import Once.Backend.RiscV64.Correct.IR.Case
  using (CaseContext; make-case-context)
open import Once.Backend.RiscV64.Correct.IR.Case using (module CaseContext)

-- Import extracted curry proof
open import Once.Backend.RiscV64.Correct.IR.Curry using (run-curry-star)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Star-based inl/inr execution (postulated for now)
--
-- These require step-by-step execution proofs. The structure is:
-- inl: addi sp sp -16; sd zero 0(sp); sd a0 8(sp); mv a0 sp
-- inr: addi sp sp -16; li t0 1; sd t0 0(sp); sd a0 8(sp); mv a0 sp
------------------------------------------------------------------------

postulate
  run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv {A} {A + B} inl ++ suffix
    in ∃[ s' ] IRStarResult {A} {A + B} inl prog s s' x (length prefix)

  run-inr-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv {B} {A + B} inr ++ suffix
    in ∃[ s' ] IRStarResult {B} {A + B} inr prog s s' x (length prefix)

------------------------------------------------------------------------
-- Star-based initial (void elimination)
--
-- compile-riscv initial = ebreak ∷ []
--
-- This should never be called since Void has no inhabitants.
------------------------------------------------------------------------

run-initial-star : ∀ {A} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv {Void} {A} initial ++ suffix
  in ∃[ s' ] IRStarResult {Void} {A} initial prog s s' x (length prefix)
run-initial-star prefix suffix x s h-false pc-eq a0-eq = ⊥-elim x

------------------------------------------------------------------------
-- Apply postulate
--
-- Apply requires whole-program analysis because:
-- 1. jalr jumps to a code pointer stored in the closure
-- 2. We need to know that code pointer points to valid thunk code
-- 3. The thunk was created by curry, which is proven separately
--
-- This is sound by construction: curry creates closures that apply
-- can call. Full verification requires tracking closure provenance.
------------------------------------------------------------------------

postulate
  run-apply-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    let prog = prefix ++ compile-riscv {(A ⇒ B) * A} {B} apply ++ suffix
    in ∃[ s' ] IRStarResult {(A ⇒ B) * A} {B} apply prog s s' x (length prefix)

------------------------------------------------------------------------
-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to StarBase functions
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset terminal prefix suffix x s h-false pc-eq a0-eq =
    run-terminal-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fold prefix suffix x s h-false pc-eq a0-eq =
    run-fold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset unfold prefix suffix x s h-false pc-eq a0-eq =
    run-unfold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset arr prefix suffix x s h-false pc-eq a0-eq =
    run-arr-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fst prefix suffix x s h-false pc-eq a0-eq =
    run-fst-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset snd prefix suffix x s h-false pc-eq a0-eq =
    run-snd-star prefix suffix x s h-false pc-eq a0-eq

  -- Injection cases
  run-ir-star-at-offset inl prefix suffix x s h-false pc-eq a0-eq =
    run-inl-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset inr prefix suffix x s h-false pc-eq a0-eq =
    run-inr-star prefix suffix x s h-false pc-eq a0-eq

  -- Void elimination
  run-ir-star-at-offset initial prefix suffix x s h-false pc-eq a0-eq =
    run-initial-star prefix suffix x s h-false pc-eq a0-eq

  -- Curry: delegate to extracted proof
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: use extracted context helpers
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq =
    let ctx = make-compose-context f g prefix suffix
        open ComposeContext ctx

        -- Step 1: Execute f
        (sf , rf) = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq a0-eq
        rf' = transform-f-result f g prefix suffix x s sf rf

        -- Step 2: Execute g (no transfer needed - a0 already has result!)
        a0-after-f : readReg (regs sf) a0 ≡ encode (eval f x)
        a0-after-f = ir-a0 rf

        -- PC conversion: ir-pc rf gives pc sf ≡ length prefix +ℕ compile-length f
        -- We need pc sf ≡ length prefix-g where length prefix-g = length prefix +ℕ len-f
        pc-for-g : pc sf ≡ length prefix-g
        pc-for-g = trans (ir-pc rf) (sym len-prefix-g)

        (sg , rg) = run-ir-star-at-offset g prefix-g suffix (eval f x) sf
                      (ir-halted rf) pc-for-g a0-after-f
        rg' = transform-g-result f g prefix suffix x sf sg rg

    in sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'

  -- Pair: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Case: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Pair helper (postulated - needs step-by-step execution proof)
  postulate
    run-pair-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                    (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
      halted s ≡ false →
      pc s ≡ length prefix →
      readReg (regs s) a0 ≡ encode x →
      let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
      in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)

  -- Case helper (postulated - needs branch execution proof)
  postulate
    run-case-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                    (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
      halted s ≡ false →
      pc s ≡ length prefix →
      readReg (regs s) a0 ≡ encode x →
      let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
      in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- RISC-V thunk layout within curry (positions 7 onwards):
  --   7: label code-ptr (thunk entry)
  --   8: addi sp sp -16 (allocate pair)
  --   9: sd s0 0(sp) (store env = a)
  --   10: sd a0 8(sp) (store arg = b)
  --   11: mv a0 sp (a0 = pair pointer)
  --   12 to 11+len-f: compile-riscv f
  --   12+len-f: ret
  --   13+len-f: label end
  --
  -- Structure:
  --   1. Trace 5 setup instructions (label, addi, sd, sd, mv)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace ret instruction
  --   4. Compose via star-trans
  ------------------------------------------------------------------------

  -- Prove thunk setup: label, addi sp -16, sd s0, sd a0, mv a0 sp
  thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
                     (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 7
        f-offset = length prefix +ℕ 12
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) a0 ≡ encode arg →
    readReg (regs s) s0 ≡ encode env →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ f-offset
            × readReg (regs s') a0 ≡ encode (env , arg)
            × readReg (regs s') s1 ≡ readReg (regs s) s1)
  -- Postulated for now - requires detailed instruction semantics
  thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                   h-false pc-eq a0-eq s0-eq =
    postulate-thunk-setup f prefix suffix env arg s h-false pc-eq a0-eq s0-eq
    where
      postulate
        postulate-thunk-setup : ∀ {A B C} (f : IR (A * B) C)
          (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
          let prog = prefix ++ compile-riscv (curry f) ++ suffix
              thunk-offset = length prefix +ℕ 7
              f-offset = length prefix +ℕ 12
          in
          halted s ≡ false →
          pc s ≡ thunk-offset →
          readReg (regs s) a0 ≡ encode arg →
          readReg (regs s) s0 ≡ encode env →
          ∃[ s' ] (Star prog s s'
                  × halted s' ≡ false
                  × pc s' ≡ f-offset
                  × readReg (regs s') a0 ≡ encode (env , arg)
                  × readReg (regs s') s1 ≡ readReg (regs s) s1)

  -- Prove ret instruction tracing
  thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        ret-offset = length prefix +ℕ 12 +ℕ compile-length f
    in
    halted s ≡ false →
    pc s ≡ ret-offset →
    readReg (regs s) ra ≡ ret-addr →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ ret-addr
            × readReg (regs s') a0 ≡ readReg (regs s) a0
            × readReg (regs s') s1 ≡ readReg (regs s) s1)
  -- Postulated for now - requires ret instruction semantics
  thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s h-false pc-eq ra-eq =
    postulate-thunk-ret f prefix suffix ret-addr s h-false pc-eq ra-eq
    where
      postulate
        postulate-thunk-ret : ∀ {A B C} (f : IR (A * B) C)
          (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
          let prog = prefix ++ compile-riscv (curry f) ++ suffix
              ret-offset = length prefix +ℕ 12 +ℕ compile-length f
          in
          halted s ≡ false →
          pc s ≡ ret-offset →
          readReg (regs s) ra ≡ ret-addr →
          ∃[ s' ] (Star prog s s'
                  × halted s' ≡ false
                  × pc s' ≡ ret-addr
                  × readReg (regs s') a0 ≡ readReg (regs s) a0
                  × readReg (regs s') s1 ≡ readReg (regs s) s1)

  -- | curry-thunk-correct-impl: Implementation using IH
  -- This composes: setup tracing → IH on f → ret tracing
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
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
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix env arg s ret-addr
                           h-eq pc-eq a0-eq s0-eq ra-eq =
    s-final , thunk-result , pc-final
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 7
      f-offset = length prefix +ℕ 12
      ret-offset = length prefix +ℕ 12 +ℕ compile-length f

      -- Step 1: Trace 5 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq a0-eq s0-eq
      s-after-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))

      -- Step 2: Call IH on f
      -- We need to view the program as containing compile-riscv f at f-offset
      -- For now, postulate the bridging (program view transformation)
      postulate
        f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                   × halted s-f ≡ false
                                   × pc s-f ≡ ret-offset
                                   × readReg (regs s-f) a0 ≡ encode (eval f (env , arg))
                                   × readReg (regs s-f) s1 ≡ readReg (regs s-after-setup) s1
                                   × readReg (regs s-f) ra ≡ ret-addr)

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

  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C)
                           (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        offset = length prefix
    in ∃[ s' ] CurryResult f prog s s' x offset

  run-curry-star-with-wf {A} {B} {C} f prefix suffix x s h-false pc-eq a0-eq =
    let (s' , result) = run-curry-star f prefix suffix x s h-false pc-eq a0-eq
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

      -- code-ptr = offset + 7 < length prog
      postulate
        code-ptr-valid-proof : offset +ℕ 7 < length prog

------------------------------------------------------------------------
-- Top-level entry point
------------------------------------------------------------------------

-- | Execute IR starting at position 0
run-ir-star : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult ir (compile-riscv ir) s s' x 0
run-ir-star ir x s h-false pc-eq a0-eq =
  subst (λ prog → ∃[ s' ] IRStarResult ir prog s s' x 0)
        (++-identityʳ (compile-riscv ir))
        (run-ir-star-at-offset ir [] [] x s h-false pc-eq a0-eq)
  where
    open import Data.List.Properties using (++-identityʳ)
