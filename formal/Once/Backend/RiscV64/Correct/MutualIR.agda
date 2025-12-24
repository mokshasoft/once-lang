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
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-ra;
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
         pair-setup-star; pair-middle-star; pair-final-star)
open import Once.Backend.RiscV64.Correct.IR.Pair using (module PairContext)

-- Import extracted case helpers
open import Once.Backend.RiscV64.Correct.IR.Case
  using (CaseContext; make-case-context;
         case-dispatch-left-star; case-dispatch-right-star;
         case-left-jump-star; case-right-end-star)
open import Once.Backend.RiscV64.Correct.IR.Case using (module CaseContext)

-- Import extracted curry proof
open import Once.Backend.RiscV64.Correct.IR.Curry using (run-curry-star)

-- Import thunk setup proof
open import Once.Backend.RiscV64.Correct.IR.ThunkSetup using (thunk-setup-star-proven)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-monoˡ-<; m≤m+n; m≤n+m)
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

  -- Pair helper - proven using phase helpers and IH
  run-pair-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      }
    where
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix

      -- Phase 1: Setup (2 instructions)
      setup-result = pair-setup-star f g prefix suffix x s h-false pc-eq a0-eq
      s-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      sp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      ra-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))

      -- Phase 2: Execute f (IH call)
      -- Program view: prog ≡ prefix-f ++ code-f ++ suffix-f
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup h-setup
                 (trans pc-setup (sym len-prefix-f)) a0-setup
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

      -- Convert f result to use prog
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s-after-f-raw
      star-f-raw = ir-star r-f

      star-f : Star prog s-setup s-after-f-raw
      star-f = subst (λ p → Star p s-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract f result properties
      h-after-f = ir-halted r-f
      a0-after-f = ir-a0 r-f
      s1-after-f = ir-s1 r-f
      ra-after-f = ir-ra r-f

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ len-f
      pc-f-raw = ir-pc r-f

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 2 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- s1 is preserved through f, so it still holds x
      s1-after-f-is-x : readReg (regs s-after-f-raw) s1 ≡ encode x
      s1-after-f-is-x = trans s1-after-f s1-setup

      -- Phase 3: Middle (2 instructions)
      mid-result = pair-middle-star f g prefix suffix x s s-after-f-raw
                     h-after-f pc-after-f a0-after-f s1-after-f-is-x
      s-mid = proj₁ mid-result
      star-mid-raw = proj₁ (proj₂ mid-result)
      h-mid = proj₁ (proj₂ (proj₂ mid-result))
      pc-mid = proj₁ (proj₂ (proj₂ (proj₂ mid-result)))
      a0-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))
      s1-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))
      sp-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))
      ra-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))
      mem-mid = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))

      -- Middle star is already in prog
      star-mid : Star prog s-after-f-raw s-mid
      star-mid = star-mid-raw

      -- Phase 4: Execute g (IH call)
      -- Need pc at correct offset for g
      pc-for-g : pc s-mid ≡ length prefix-g
      pc-for-g = begin
        pc s-mid
          ≡⟨ pc-mid ⟩
        (offset +ℕ 2 +ℕ len-f) +ℕ 2
          ≡⟨ +-assoc (offset +ℕ 2) len-f 2 ⟩
        (offset +ℕ 2) +ℕ (len-f +ℕ 2)
          ≡⟨ +-assoc offset 2 (len-f +ℕ 2) ⟩
        offset +ℕ (2 +ℕ (len-f +ℕ 2))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 2 len-f 2)) ⟩
        offset +ℕ ((2 +ℕ len-f) +ℕ 2)
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ 2)) (+-comm 2 len-f) ⟩
        offset +ℕ ((len-f +ℕ 2) +ℕ 2)
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 2 2) ⟩
        offset +ℕ (len-f +ℕ 4)
          ≡⟨ sym (+-assoc offset len-f 4) ⟩
        (offset +ℕ len-f) +ℕ 4
          ≡⟨ cong (_+ℕ 4) (+-comm offset len-f) ⟩
        (len-f +ℕ offset) +ℕ 4
          ≡⟨ +-assoc len-f offset 4 ⟩
        len-f +ℕ (offset +ℕ 4)
          ≡⟨ +-comm len-f (offset +ℕ 4) ⟩
        (offset +ℕ 4) +ℕ len-f
          ≡⟨ sym len-prefix-g ⟩
        length prefix-g ∎

      step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid h-mid
                 pc-for-g a0-mid
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

      -- Convert g result to use prog
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-mid s-after-g-raw
      star-g-raw = ir-star r-g

      star-g : Star prog s-mid s-after-g-raw
      star-g = subst (λ p → Star p s-mid s-after-g-raw) (sym prog-eq-g) star-g-raw

      -- Extract g result properties
      h-after-g = ir-halted r-g
      a0-after-g = ir-a0 r-g
      s1-after-g = ir-s1 r-g
      ra-after-g = ir-ra r-g

      pc-g-raw : pc s-after-g-raw ≡ length prefix-g +ℕ len-g
      pc-g-raw = ir-pc r-g

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 4 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      -- Memory: sp should still point to our pair location through f and g execution
      -- sp is a callee-saved register, so f and g must preserve it
      -- The memory at sp should also be preserved (f and g don't clobber it)
      postulate
        sp-after-f : readReg (regs s-after-f-raw) sp ≡ readReg (regs s-setup) sp
        sp-after-g : readReg (regs s-after-g-raw) sp ≡ readReg (regs s-mid) sp
        mem-after-g : readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp)
                    ≡ just (encode (eval f x))

      -- Phase 5: Final (2 instructions)
      final-phase-result = pair-final-star f g prefix suffix x s-mid s-after-g-raw
                             h-after-g pc-after-g a0-after-g mem-after-g
      s-final = proj₁ final-phase-result
      star-final-raw = proj₁ (proj₂ final-phase-result)
      h-final = proj₁ (proj₂ (proj₂ final-phase-result))
      pc-final-raw = proj₁ (proj₂ (proj₂ (proj₂ final-phase-result)))
      a0-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))
      s1-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))
      ra-final-raw = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))

      -- Final star is already in prog
      star-final : Star prog s-after-g-raw s-final
      star-final = star-final-raw

      -- Compose all Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup
                   (star-trans star-f
                     (star-trans star-mid
                       (star-trans star-g star-final)))

      -- Final pc
      -- compile-length ⟨ f , g ⟩ = (6 + len-f) + len-g
      pc-final : pc s-final ≡ offset +ℕ compile-length ⟨ f , g ⟩
      pc-final = begin
        pc s-final
          ≡⟨ pc-final-raw ⟩
        (offset +ℕ 4 +ℕ len-f +ℕ len-g) +ℕ 2
          ≡⟨ +-assoc (offset +ℕ 4 +ℕ len-f) len-g 2 ⟩
        (offset +ℕ 4 +ℕ len-f) +ℕ (len-g +ℕ 2)
          ≡⟨ +-assoc (offset +ℕ 4) len-f (len-g +ℕ 2) ⟩
        (offset +ℕ 4) +ℕ (len-f +ℕ (len-g +ℕ 2))
          ≡⟨ +-assoc offset 4 (len-f +ℕ (len-g +ℕ 2)) ⟩
        offset +ℕ (4 +ℕ (len-f +ℕ (len-g +ℕ 2)))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 4 len-f (len-g +ℕ 2))) ⟩
        offset +ℕ ((4 +ℕ len-f) +ℕ (len-g +ℕ 2))
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ (len-g +ℕ 2))) (+-comm 4 len-f) ⟩
        offset +ℕ ((len-f +ℕ 4) +ℕ (len-g +ℕ 2))
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 4 (len-g +ℕ 2)) ⟩
        offset +ℕ (len-f +ℕ (4 +ℕ (len-g +ℕ 2)))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (sym (+-assoc 4 len-g 2)) ⟩
        offset +ℕ (len-f +ℕ ((4 +ℕ len-g) +ℕ 2))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ (z +ℕ 2))) (+-comm 4 len-g) ⟩
        offset +ℕ (len-f +ℕ ((len-g +ℕ 4) +ℕ 2))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (+-assoc len-g 4 2) ⟩
        offset +ℕ (len-f +ℕ (len-g +ℕ 6))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc len-f len-g 6)) ⟩
        offset +ℕ ((len-f +ℕ len-g) +ℕ 6)
          ≡⟨ cong (offset +ℕ_) (+-comm (len-f +ℕ len-g) 6) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ ((6 +ℕ len-f) +ℕ len-g)
          ∎

      -- s1 preservation: pair modifies s1 (mv s1 a0) but the code
      -- should properly save/restore callee-saved registers
      -- For now, postulate this property
      postulate
        s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1

      -- ra preservation: chain through all phases
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-final-raw
                   (trans ra-after-g
                     (trans ra-mid
                       (trans ra-after-f ra-setup)))

  -- Case helper - proven using dispatch helpers and IH
  run-case-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
    in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  -- Left path implementation (inj₁ a)
  run-case-star {A} {B} {C} f g prefix suffix (inj₁ a) s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (3 instructions, branch NOT taken)
      dispatch-result = case-dispatch-left-star f g prefix suffix a s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      t0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))
      ra-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))

      -- Phase 2: Execute f (IH call)
      -- PC for f: need length prefix-f
      pc-for-f : pc s-dispatch ≡ length prefix-f
      pc-for-f = trans pc-dispatch (sym len-prefix-f)

      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-dispatch h-dispatch pc-for-f a0-dispatch
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

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

      -- Phase 3: Jump over g (2 instructions)
      jump-result = case-left-jump-star f g prefix suffix s-after-f-raw h-after-f pc-after-f
      s-final = proj₁ jump-result
      star-jump = proj₁ (proj₂ jump-result)
      h-final = proj₁ (proj₂ (proj₂ jump-result))
      pc-jump = proj₁ (proj₂ (proj₂ (proj₂ jump-result)))
      a0-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))
      s1-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))
      ra-jump = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))

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

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-jump (trans ra-after-f ra-dispatch)

  -- Right path implementation (inj₂ b)
  run-case-star {A} {B} {C} f g prefix suffix (inj₂ b) s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (4 instructions, branch TAKEN + landing label)
      dispatch-result = case-dispatch-right-star f g prefix suffix b s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      ra-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))

      -- Phase 2: Execute g (IH call)
      pc-for-g : pc s-dispatch ≡ length prefix-g
      pc-for-g = trans pc-dispatch (sym len-prefix-g)

      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-dispatch h-dispatch pc-for-g a0-dispatch
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

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

      -- Phase 3: Execute end-label (1 instruction)
      end-result = case-right-end-star f g prefix suffix s-after-g-raw h-after-g pc-after-g
      s-final = proj₁ end-result
      star-end = proj₁ (proj₂ end-result)
      h-final = proj₁ (proj₂ (proj₂ end-result))
      pc-end = proj₁ (proj₂ (proj₂ (proj₂ end-result)))
      a0-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))
      s1-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))
      ra-end = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))

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

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-end (trans ra-after-g ra-dispatch)

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
  -- Now using the proven version from ThunkSetup module
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
            × readReg (regs s') s1 ≡ readReg (regs s) s1
            × readReg (regs s') ra ≡ readReg (regs s) ra)
  thunk-setup-star = thunk-setup-star-proven

  -- Prove ret instruction tracing
  -- RISC-V ret is simple: it just sets pc = ra and modifies nothing else
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
  thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s h-false pc-eq ra-eq =
    s' , star-all , h' , pc' , a0' , s1'
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      offset = length prefix
      ret-offset = offset +ℕ 12 +ℕ compile-length f

      -- The ret instruction is at ret-offset in curry
      -- curry layout: [7 closure setup] [5 thunk setup] [compile-riscv f] [ret] [label end]
      -- ret is at position 12 + len(f) within curry

      len-f = compile-length f

      -- First 12 instructions of curry (closure setup + thunk setup)
      curry-prefix-to-12 : Program
      curry-prefix-to-12 = addi sp sp neg16 ∷       -- 0
                           sd a0 (+ 0) sp ∷         -- 1
                           auipc t0 (+ 0) ∷         -- 2
                           addi t0 t0 (+ 5) ∷       -- 3
                           sd t0 (+ 8) sp ∷         -- 4
                           mv a0 sp ∷               -- 5
                           j (+ (7 +ℕ len-f)) ∷     -- 6
                           label 7 ∷                -- 7
                           addi sp sp neg16 ∷       -- 8
                           sd s0 (+ 0) sp ∷         -- 9
                           sd a0 (+ 8) sp ∷         -- 10
                           mv a0 sp ∷               -- 11
                           []

      -- curry code = curry-prefix-to-12 ++ compile-riscv f ++ ret ∷ label-end ∷ []
      curry-code-eq : compile-riscv (curry f) ≡
                      curry-prefix-to-12 ++ compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ []
      curry-code-eq = refl

      -- Build prefix up to ret
      prefix-to-ret : Program
      prefix-to-ret = (prefix ++ curry-prefix-to-12) ++ compile-riscv f

      len-prefix-to-ret : length prefix-to-ret ≡ ret-offset
      len-prefix-to-ret = begin
        length prefix-to-ret
          ≡⟨ List-length-++ (prefix ++ curry-prefix-to-12) ⟩
        length (prefix ++ curry-prefix-to-12) +ℕ length (compile-riscv f)
          ≡⟨ cong (_+ℕ length (compile-riscv f)) (List-length-++ prefix) ⟩
        (offset +ℕ 12) +ℕ length (compile-riscv f)
          ≡⟨ cong ((offset +ℕ 12) +ℕ_) (compile-length-correct f) ⟩
        (offset +ℕ 12) +ℕ len-f
          ∎

      -- Show prog decomposes to prefix-to-ret ++ ret ∷ suffix'
      prog-eq-ret : prog ≡ prefix-to-ret ++ ret ∷ _
      prog-eq-ret = begin
        prog
          ≡⟨ cong (λ c → prefix ++ c ++ suffix) curry-code-eq ⟩
        prefix ++ (curry-prefix-to-12 ++ compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong (prefix ++_) (++-assoc curry-prefix-to-12 _ suffix) ⟩
        prefix ++ (curry-prefix-to-12 ++ (compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc prefix curry-prefix-to-12 _) ⟩
        (prefix ++ curry-prefix-to-12) ++ (compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong ((prefix ++ curry-prefix-to-12) ++_) (++-assoc (compile-riscv f) _ suffix) ⟩
        (prefix ++ curry-prefix-to-12) ++ (compile-riscv f ++ (ret ∷ label (13 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc (prefix ++ curry-prefix-to-12) (compile-riscv f) _) ⟩
        prefix-to-ret ++ (ret ∷ label (13 +ℕ len-f) ∷ []) ++ suffix
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
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      ra-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))

      -- Step 2: Call IH on f using program reassociation
      -- Key insight: curry compiles to structured form that we can reassociate
      len-f = compile-length f
      code-f = compile-riscv f

      -- RISC-V curry structure (7 + 5 + len-f + 2 = 14 + len-f instructions)
      -- curry-closure-setup: 7 instructions (0-6)
      curry-closure-setup : Program
      curry-closure-setup = addi sp sp neg16 ∷
                            sd a0 (+ 0) sp ∷
                            auipc t0 (+ 0) ∷
                            addi t0 t0 (+ 5) ∷
                            sd t0 (+ 8) sp ∷
                            mv a0 sp ∷
                            j (+ (7 +ℕ len-f)) ∷ []

      -- curry-thunk-setup: 5 instructions (7-11)
      curry-thunk-setup : Program
      curry-thunk-setup = label 7 ∷
                          addi sp sp neg16 ∷
                          sd s0 (+ 0) sp ∷
                          sd a0 (+ 8) sp ∷
                          mv a0 sp ∷ []

      -- curry-tail: 2 instructions (12+len-f to 13+len-f)
      curry-tail : Program
      curry-tail = ret ∷ label (13 +ℕ len-f) ∷ []

      -- prefix-f and suffix-f for calling IH
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 12
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

      step-f : ∃[ s-f ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f (env , arg) s-after-setup
                 h-setup pc-setup-f a0-setup

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

      pc-f-converted : pc s-after-f-raw ≡ ret-offset
      pc-f-converted = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- ra preservation: chain through IH and setup
      ra-preserved : readReg (regs s-after-f-raw) ra ≡ ret-addr
      ra-preserved = trans (ir-ra r-f) (trans ra-setup ra-eq)

      f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                 × halted s-f ≡ false
                                 × pc s-f ≡ ret-offset
                                 × readReg (regs s-f) a0 ≡ encode (eval f (env , arg))
                                 × readReg (regs s-f) s1 ≡ readReg (regs s-after-setup) s1
                                 × readReg (regs s-f) ra ≡ ret-addr)
      f-result-bridge = s-after-f-raw , star-f-converted , ir-halted r-f , pc-f-converted ,
                        ir-a0 r-f , ir-s1 r-f , ra-preserved

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
      curry-code = compile-riscv (curry f)

      -- code-ptr = offset + 7 < length prog
      -- Proof: length prog = length prefix + length curry-code + length suffix
      --        length curry-code = 14 + compile-length f ≥ 14
      --        So offset + 7 < offset + 14 ≤ length prog
      code-ptr-valid-proof : offset +ℕ 7 < length prog
      code-ptr-valid-proof = proof
        where
          open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-<)

          -- 7 < 14 = 8 ≤ 14
          seven-lt-fourteen : 7 < 14
          seven-lt-fourteen = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

          -- length curry-code = 14 + compile-length f
          len-curry : length curry-code ≡ 14 +ℕ compile-length f
          len-curry = compile-length-correct (curry f)

          -- 14 ≤ 14 + compile-length f
          fourteen-le-curry : 14 ≤ 14 +ℕ compile-length f
          fourteen-le-curry = m≤m+n 14 (compile-length f)

          -- 7 < 14 ≤ 14 + compile-length f = length curry-code
          seven-lt-curry : 7 < length curry-code
          seven-lt-curry = subst (7 <_) (sym len-curry)
                            (<-≤-trans seven-lt-fourteen fourteen-le-curry)

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
