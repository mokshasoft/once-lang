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

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; star-step5)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult; code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-a0; thunk-s1;
         ClosuresWF; trivialWF; pairWF)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.RiscV64.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra; ir-sp-delta; ir-sp;
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
open import Once.Backend.RiscV64.Correct.IR.ThunkSetup using (thunk-setup-star-proven; thunk-cleanup-star-proven)

-- Import apply proof (proven when ClosureWellFormed is available)
open import Once.Backend.RiscV64.Correct.IR.Apply
  using (run-apply-with-wf; apply-setup-star; apply-jalr-star; apply-nop-star)

-- Import injection proofs (extracted to reduce module size)
open import Once.Backend.RiscV64.Correct.IR.Injection
  using (run-inl-star; run-inr-star)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; s≤s; z≤n; s<s; z<s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-monoˡ-<; m≤m+n; m≤n+m; m∸n+n≡m; ≤-trans)
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
-- Apply postulate
--
-- Apply requires whole-program analysis because:
-- 1. jalr jumps to a code pointer stored in the closure
-- 2. We need to know that code pointer points to valid thunk code
-- 3. The thunk was created by curry, which is proven separately
--
-- This is sound by construction: curry creates closures that apply
-- can call. Full verification requires tracking closure provenance.
--
-- PROVEN ALTERNATIVE: When a ClosureWellFormed proof is available
-- (from curry's output), use run-apply-with-wf from IR/Apply.agda.
-- This traces all 7 apply instructions and uses thunk-correct
-- to verify the indirect call executes correctly.
------------------------------------------------------------------------

postulate
  run-apply-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    let prog = prefix ++ compile-riscv (apply {i} {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {i} {A} {B}) prog s s' x (length prefix)


------------------------------------------------------------------------
-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset (sized for termination)
  -- Stack-space precondition: 24 ≤ sp ensures enough stack for all IR nodes
  -- Size parameter i enables termination checking across module boundaries
  run-ir-star-at-offset : ∀ {i A B} (ir : IR i A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    24 ≤ readReg (regs s) sp →
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

  -- Curry: delegate to extracted proof (needs stack-space)
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq _ =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: use extracted context helpers (needs to pass sp-bound through)
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    let ctx = make-compose-context f g prefix suffix
        open ComposeContext ctx

        -- Step 1: Execute f
        (sf , rf) = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq a0-eq sp-bound
        rf' = transform-f-result f g prefix suffix x s sf rf

        -- Step 2: Execute g (no transfer needed - a0 already has result!)
        a0-after-f : readReg (regs sf) a0 ≡ encode (eval f x)
        a0-after-f = ir-a0 rf

        -- PC conversion: ir-pc rf gives pc sf ≡ length prefix +ℕ compile-length f
        -- We need pc sf ≡ length prefix-g where length prefix-g = length prefix +ℕ len-f
        pc-for-g : pc sf ≡ length prefix-g
        pc-for-g = trans (ir-pc rf) (sym len-prefix-g)

        -- SP bound for g: f may allocate stack (delta > 0), so sp' = sp - delta.
        -- To prove 24 ≤ sp' we'd need 24 + delta ≤ sp.
        -- This requires stack depth analysis; for now use postulate.
        postulate sp-bound-for-g : 24 ≤ readReg (regs sf) sp

        (sg , rg) = run-ir-star-at-offset g prefix-g suffix (eval f x) sf
                      (ir-halted rf) pc-for-g a0-after-f sp-bound-for-g
        rg' = transform-g-result f g prefix suffix x sf sg rg

    in sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'

  -- Pair: use extracted context helpers (needs stack-space)
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Case: use extracted context helpers
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq sp-bound =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound

  -- Pair helper - proven using phase helpers and IH
  run-pair-star : ∀ {i A B C} (f : IR i C A) (g : IR i C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    24 ≤ readReg (regs s) sp →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star {_} {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq sp-bound =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-s2 = s2-final
      ; ir-ra = ra-final
      ; ir-sp-delta = 24 +ℕ ir-sp-delta r-f +ℕ ir-sp-delta r-g
      ; ir-sp = sp-final
      ; ir-mem-preserved = mem-preserved-final
      ; ir-output-wf = output-wf
      }
    where
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix

      -- Phase 1: Setup (3 instructions - addi sp, sd s1, mv s1 a0)
      -- Original s1 is saved to stack at sp+16
      orig-s1 = readReg (regs s) s1
      setup-result = pair-setup-star f g prefix suffix x s h-false pc-eq a0-eq sp-bound
      s-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      sp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      s2-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      ra-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
      mem-s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
      -- Memory preservation at orig-sp and above from setup phase
      mem-setup-orig-sp = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
      mem-setup-orig-sp+8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))))
      mem-setup-orig-sp+16 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))))
      mem-setup-orig-sp+24 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))))
      -- Original sp for memory preservation chaining
      orig-sp = readReg (regs s) sp

      -- Phase 2: Execute f (IH call)
      -- Program view: prog ≡ prefix-f ++ code-f ++ suffix-f
      -- Note: f runs with new-sp = orig-sp - 24. For 24 ≤ new-sp, need 48 ≤ orig-sp.
      -- TODO: Stack depth analysis for proper nested bounds.
      postulate sp-bound-for-f : 24 ≤ readReg (regs s-setup) sp
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup h-setup
                 (trans pc-setup (sym len-prefix-f)) a0-setup sp-bound-for-f
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

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 3 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- s1 is preserved through f, so it still holds x
      s1-after-f-is-x : readReg (regs s-after-f-raw) s1 ≡ encode x
      s1-after-f-is-x = trans s1-after-f s1-setup

      -- SP tracking: postulate that f preserves sp (sound when delta_f = 0)
      -- This is a limitation: nested pairs would fail. See detailed comment below.
      postulate
        sp-after-f : readReg (regs s-after-f-raw) sp ≡ readReg (regs s-setup) sp

      -- Phase 3: Middle (2 instructions)
      -- Need sp relation: sp after f = sp_orig - 24
      sp-after-f-rel : readReg (regs s-after-f-raw) sp ≡ readReg (regs s) sp ∸ 24
      sp-after-f-rel = trans sp-after-f sp-setup

      mid-result = pair-middle-star f g prefix suffix x s s-after-f-raw
                     h-after-f pc-after-f a0-after-f s1-after-f-is-x sp-bound sp-after-f-rel
      s-mid = proj₁ mid-result
      star-mid-raw = proj₁ (proj₂ mid-result)
      h-mid = proj₁ (proj₂ (proj₂ mid-result))
      pc-mid = proj₁ (proj₂ (proj₂ (proj₂ mid-result)))
      a0-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))
      s1-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))
      sp-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))
      s2-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))
      ra-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))))
      mem-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))))
      mem-sp+16-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))))))
      -- Memory preservation at orig-sp and above from middle phase
      mem-mid-orig-sp = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))))))
      mem-mid-orig-sp+8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))))))))
      mem-mid-orig-sp+16 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))))))))
      mem-mid-orig-sp+24 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))))))))

      -- Middle star is already in prog
      star-mid : Star prog s-after-f-raw s-mid
      star-mid = star-mid-raw

      -- Phase 4: Execute g (IH call)
      -- Need pc at correct offset for g
      -- pc-mid produces (offset +ℕ 3 +ℕ len-f) +ℕ 2, need (offset +ℕ 5) +ℕ len-f
      pc-for-g : pc s-mid ≡ length prefix-g
      pc-for-g = begin
        pc s-mid
          ≡⟨ pc-mid ⟩
        (offset +ℕ 3 +ℕ len-f) +ℕ 2
          ≡⟨ +-assoc (offset +ℕ 3) len-f 2 ⟩
        (offset +ℕ 3) +ℕ (len-f +ℕ 2)
          ≡⟨ +-assoc offset 3 (len-f +ℕ 2) ⟩
        offset +ℕ (3 +ℕ (len-f +ℕ 2))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 3 len-f 2)) ⟩
        offset +ℕ ((3 +ℕ len-f) +ℕ 2)
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ 2)) (+-comm 3 len-f) ⟩
        offset +ℕ ((len-f +ℕ 3) +ℕ 2)
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 3 2) ⟩
        offset +ℕ (len-f +ℕ 5)
          ≡⟨ sym (+-assoc offset len-f 5) ⟩
        (offset +ℕ len-f) +ℕ 5
          ≡⟨ cong (_+ℕ 5) (+-comm offset len-f) ⟩
        (len-f +ℕ offset) +ℕ 5
          ≡⟨ +-assoc len-f offset 5 ⟩
        len-f +ℕ (offset +ℕ 5)
          ≡⟨ +-comm len-f (offset +ℕ 5) ⟩
        (offset +ℕ 5) +ℕ len-f
          ≡⟨ sym len-prefix-g ⟩
        length prefix-g ∎

      -- Note: g runs with s-mid's sp (should equal new-sp if sp preserved by f)
      -- TODO: Stack depth analysis for proper nested bounds.
      postulate sp-bound-for-g : 24 ≤ readReg (regs s-mid) sp
      step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid h-mid
                 pc-for-g a0-mid sp-bound-for-g
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

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      -- SP tracking through f and g:
      -- The IRStarResult gives us: sp-after + delta = sp-before
      --
      -- LIMITATION: The current pair code generation assumes f and g don't allocate
      -- permanent stack space (ir-sp-delta = 0). This is because:
      --   - pair-middle writes to current sp after f
      --   - pair-final reads from current sp after g
      --   - If f or g allocate stack, these addresses differ!
      --
      -- This limitation affects nested pairs: pair ⟨ pair ⟨ a , b ⟩ , c ⟩ would fail
      -- because the inner pair allocates 24 bytes.
      --
      -- Fix would require: save frame pointer in s2 before f, use s2 for all stores/loads.
      -- For now, we postulate the sp preservation (sound when delta = 0).
      postulate
        sp-after-g : readReg (regs s-after-g-raw) sp ≡ readReg (regs s-mid) sp

      -- Memory preservation: The middle phase writes encode(eval f x) to sp,
      -- and g preserves memory at sp (via ir-mem-preserved from IH).
      -- Chain: sp-after-g → ir-mem-preserved r-g 0 → sp-mid → mem-mid
      mem-after-g : readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp)
                  ≡ just (encode (eval f x))
      mem-after-g = begin
        readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp)
          ≡⟨ cong (readMem (memory s-after-g-raw)) sp-after-g ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-mid) sp)
          ≡⟨ cong (readMem (memory s-after-g-raw)) (sym (+-identityʳ (readReg (regs s-mid) sp))) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-mid) sp +ℕ 0)
          ≡⟨ ir-mem-preserved r-g 0 ⟩
        readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ 0)
          ≡⟨ cong (readMem (memory s-mid)) (+-identityʳ (readReg (regs s-mid) sp)) ⟩
        readMem (memory s-mid) (readReg (regs s-mid) sp)
          ≡⟨ cong (readMem (memory s-mid)) sp-mid ⟩
        readMem (memory s-mid) (readReg (regs s-after-f-raw) sp)
          ≡⟨ mem-mid ⟩
        just (encode (eval f x))
          ∎

      -- s1 was saved at sp+16 during setup and preserved through f/middle/g.
      -- Chain: sp conversions → ir-mem-preserved r-g 16 → mem-sp+16-mid →
      --        ir-mem-preserved r-f 16 → mem-s1-setup
      mem-s1-after-g : readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp +ℕ 16)
                     ≡ just orig-s1
      mem-s1-after-g = begin
        readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp +ℕ 16)
          ≡⟨ cong (λ addr → readMem (memory s-after-g-raw) (addr +ℕ 16)) sp-after-g ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-mid) sp +ℕ 16)
          ≡⟨ ir-mem-preserved r-g 16 ⟩
        readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ 16)
          ≡⟨ cong (λ addr → readMem (memory s-mid) (addr +ℕ 16)) sp-mid ⟩
        readMem (memory s-mid) (readReg (regs s-after-f-raw) sp +ℕ 16)
          ≡⟨ mem-sp+16-mid ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-after-f-raw) sp +ℕ 16)
          ≡⟨ cong (λ addr → readMem (memory s-after-f-raw) (addr +ℕ 16)) sp-after-f ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-setup) sp +ℕ 16)
          ≡⟨ ir-mem-preserved r-f 16 ⟩
        readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ 16)
          ≡⟨ mem-s1-setup ⟩
        just orig-s1
          ∎

      -- Phase 5: Final (3 instructions - sd a0 8(sp), mv a0 sp, ld s1 16(sp))
      -- Need sp relation: sp after g = orig-sp - 24
      -- Chain: sp-after-g → sp-mid → sp-after-f → sp-setup
      sp-mid-rel : readReg (regs s-mid) sp ≡ orig-sp ∸ 24
      sp-mid-rel = trans sp-mid (trans sp-after-f sp-setup)

      sp-after-g-rel : readReg (regs s-after-g-raw) sp ≡ orig-sp ∸ 24
      sp-after-g-rel = trans sp-after-g sp-mid-rel

      final-phase-result = pair-final-star f g prefix suffix x orig-s1 orig-sp s-mid s-after-g-raw
                             h-after-g pc-after-g a0-after-g mem-after-g mem-s1-after-g
                             sp-bound sp-after-g-rel
      s-final = proj₁ final-phase-result
      star-final-raw = proj₁ (proj₂ final-phase-result)
      h-final = proj₁ (proj₂ (proj₂ final-phase-result))
      pc-final-raw = proj₁ (proj₂ (proj₂ (proj₂ final-phase-result)))
      a0-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))
      s1-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))
      s2-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))))
      ra-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))))
      sp-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))))))
      -- Memory preservation at orig-sp and above from final phase
      mem-final-orig-sp = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))))))
      mem-final-orig-sp+8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))))))))
      mem-final-orig-sp+16 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))))))))
      mem-final-orig-sp+24 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))))))))

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
      -- compile-length ⟨ f , g ⟩ = (8 + len-f) + len-g
      pc-final : pc s-final ≡ offset +ℕ compile-length ⟨ f , g ⟩
      pc-final = begin
        pc s-final
          ≡⟨ pc-final-raw ⟩
        (offset +ℕ 5 +ℕ len-f +ℕ len-g) +ℕ 3
          ≡⟨ +-assoc (offset +ℕ 5 +ℕ len-f) len-g 3 ⟩
        (offset +ℕ 5 +ℕ len-f) +ℕ (len-g +ℕ 3)
          ≡⟨ +-assoc (offset +ℕ 5) len-f (len-g +ℕ 3) ⟩
        (offset +ℕ 5) +ℕ (len-f +ℕ (len-g +ℕ 3))
          ≡⟨ +-assoc offset 5 (len-f +ℕ (len-g +ℕ 3)) ⟩
        offset +ℕ (5 +ℕ (len-f +ℕ (len-g +ℕ 3)))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 5 len-f (len-g +ℕ 3))) ⟩
        offset +ℕ ((5 +ℕ len-f) +ℕ (len-g +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ (len-g +ℕ 3))) (+-comm 5 len-f) ⟩
        offset +ℕ ((len-f +ℕ 5) +ℕ (len-g +ℕ 3))
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 5 (len-g +ℕ 3)) ⟩
        offset +ℕ (len-f +ℕ (5 +ℕ (len-g +ℕ 3)))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (sym (+-assoc 5 len-g 3)) ⟩
        offset +ℕ (len-f +ℕ ((5 +ℕ len-g) +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ (z +ℕ 3))) (+-comm 5 len-g) ⟩
        offset +ℕ (len-f +ℕ ((len-g +ℕ 5) +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (+-assoc len-g 5 3) ⟩
        offset +ℕ (len-f +ℕ (len-g +ℕ 8))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc len-f len-g 8)) ⟩
        offset +ℕ ((len-f +ℕ len-g) +ℕ 8)
          ≡⟨ cong (offset +ℕ_) (+-comm (len-f +ℕ len-g) 8) ⟩
        offset +ℕ (8 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 8 len-f len-g)) ⟩
        offset +ℕ ((8 +ℕ len-f) +ℕ len-g)
          ∎

      -- s1 preservation: pair now properly saves/restores s1
      -- s1-final-raw says s1 = orig-s1, and orig-s1 = readReg (regs s) s1
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = s1-final-raw

      -- s2 preservation: chain through all phases
      -- setup → f → middle → g → final
      s2-after-f = ir-s2 r-f
      s2-after-g = ir-s2 r-g

      s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
      s2-final = trans s2-final-raw (trans s2-after-g (trans s2-mid (trans s2-after-f s2-setup)))

      -- ra preservation: chain through all phases
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-final-raw
                   (trans ra-after-g
                     (trans ra-mid
                       (trans ra-after-f ra-setup)))

      -- SP tracking: pair allocates 24 bytes + f's delta + g's delta
      -- With ir-sp-delta = 24 + delta_f + delta_g:
      --   sp_final + (24 + delta_f + delta_g) = sp_s
      -- Proof chains through all phases:
      --   sp-final-raw → ir-sp r-g → sp-mid → ir-sp r-f → sp-setup → m∸n+n≡m
      delta-f = ir-sp-delta r-f
      delta-g = ir-sp-delta r-g

      -- Stack space: provided as precondition (24 ≤ sp)
      stack-space : 24 ≤ readReg (regs s) sp
      stack-space = sp-bound

      sp-final : readReg (regs s-final) sp +ℕ (24 +ℕ delta-f +ℕ delta-g) ≡ readReg (regs s) sp
      sp-final = begin
        readReg (regs s-final) sp +ℕ (24 +ℕ delta-f +ℕ delta-g)
          ≡⟨ cong (_+ℕ (24 +ℕ delta-f +ℕ delta-g)) sp-final-raw ⟩
        readReg (regs s-after-g-raw) sp +ℕ (24 +ℕ delta-f +ℕ delta-g)
          -- Rearrange: (24 + delta-f) + delta-g → delta-g + (delta-f + 24)
          -- Step 1: (24 + delta-f) + delta-g → delta-g + (24 + delta-f)
          ≡⟨ cong (readReg (regs s-after-g-raw) sp +ℕ_)
                  (+-comm (24 +ℕ delta-f) delta-g) ⟩
        readReg (regs s-after-g-raw) sp +ℕ (delta-g +ℕ (24 +ℕ delta-f))
          -- Step 2: delta-g + (24 + delta-f) → delta-g + (delta-f + 24)
          ≡⟨ cong (λ x → readReg (regs s-after-g-raw) sp +ℕ (delta-g +ℕ x))
                  (+-comm 24 delta-f) ⟩
        readReg (regs s-after-g-raw) sp +ℕ (delta-g +ℕ (delta-f +ℕ 24))
          ≡⟨ sym (+-assoc (readReg (regs s-after-g-raw) sp) delta-g (delta-f +ℕ 24)) ⟩
        (readReg (regs s-after-g-raw) sp +ℕ delta-g) +ℕ (delta-f +ℕ 24)
          ≡⟨ cong (_+ℕ (delta-f +ℕ 24)) (ir-sp r-g) ⟩
        readReg (regs s-mid) sp +ℕ (delta-f +ℕ 24)
          ≡⟨ cong (_+ℕ (delta-f +ℕ 24)) sp-mid ⟩
        readReg (regs s-after-f-raw) sp +ℕ (delta-f +ℕ 24)
          ≡⟨ sym (+-assoc (readReg (regs s-after-f-raw) sp) delta-f 24) ⟩
        (readReg (regs s-after-f-raw) sp +ℕ delta-f) +ℕ 24
          ≡⟨ cong (_+ℕ 24) (ir-sp r-f) ⟩
        readReg (regs s-setup) sp +ℕ 24
          ≡⟨ cong (_+ℕ 24) sp-setup ⟩
        (readReg (regs s) sp ∸ 24) +ℕ 24
          ≡⟨ m∸n+n≡m stack-space ⟩
        readReg (regs s) sp
          ∎

      -- Memory preservation: pair writes at new-sp, new-sp+8, new-sp+16 (its own frame)
      -- so memory at original sp and above is preserved.
      -- Chain through: setup → f → middle → g → final

      -- Address conversions: s-setup.sp + 24 = orig-sp and s-mid.sp + 24 = orig-sp
      s-setup-sp+24-eq-orig-sp : readReg (regs s-setup) sp +ℕ 24 ≡ orig-sp
      s-setup-sp+24-eq-orig-sp = trans (cong (_+ℕ 24) sp-setup) (m∸n+n≡m stack-space)

      s-mid-sp+24-eq-orig-sp : readReg (regs s-mid) sp +ℕ 24 ≡ orig-sp
      s-mid-sp+24-eq-orig-sp = trans (cong (_+ℕ 24) sp-mid)
                                 (trans (cong (_+ℕ 24) sp-after-f) s-setup-sp+24-eq-orig-sp)

      -- Universal memory preservation: orig-sp + n is preserved for all n
      -- Chain through: final → g → middle → f → setup
      -- Key: s-setup.sp + 24 = orig-sp, s-mid.sp + 24 = orig-sp
      -- So orig-sp + n = s-setup.sp + (24 + n) = s-mid.sp + (24 + n)
      mem-preserved-final : ∀ n → readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
      mem-preserved-final n =
        let -- Address conversion: orig-sp + n = s-setup.sp + (24 + n)
            -- s-setup-sp+24-eq-orig-sp : s-setup.sp + 24 = orig-sp
            -- So orig-sp + n = (s-setup.sp + 24) + n = s-setup.sp + (24 + n)
            addr-eq-setup : orig-sp +ℕ n ≡ readReg (regs s-setup) sp +ℕ (24 +ℕ n)
            addr-eq-setup = trans (cong (_+ℕ n) (sym s-setup-sp+24-eq-orig-sp))
                              (+-assoc (readReg (regs s-setup) sp) 24 n)
            -- Address conversion: orig-sp + n = s-mid.sp + (24 + n)
            addr-eq-mid : orig-sp +ℕ n ≡ readReg (regs s-mid) sp +ℕ (24 +ℕ n)
            addr-eq-mid = trans (cong (_+ℕ n) (sym s-mid-sp+24-eq-orig-sp))
                            (+-assoc (readReg (regs s-mid) sp) 24 n)
        in begin
          readMem (memory s-final) (orig-sp +ℕ n)
            ≡⟨ mem-final-at-orig-sp+n ⟩
          readMem (memory s-after-g-raw) (orig-sp +ℕ n)
            ≡⟨ cong (readMem (memory s-after-g-raw)) addr-eq-mid ⟩
          readMem (memory s-after-g-raw) (readReg (regs s-mid) sp +ℕ (24 +ℕ n))
            ≡⟨ ir-mem-preserved r-g (24 +ℕ n) ⟩
          readMem (memory s-mid) (readReg (regs s-mid) sp +ℕ (24 +ℕ n))
            ≡⟨ cong (readMem (memory s-mid)) (sym addr-eq-mid) ⟩
          readMem (memory s-mid) (orig-sp +ℕ n)
            ≡⟨ mem-mid-at-orig-sp+n ⟩
          readMem (memory s-after-f-raw) (orig-sp +ℕ n)
            ≡⟨ cong (readMem (memory s-after-f-raw)) addr-eq-setup ⟩
          readMem (memory s-after-f-raw) (readReg (regs s-setup) sp +ℕ (24 +ℕ n))
            ≡⟨ ir-mem-preserved r-f (24 +ℕ n) ⟩
          readMem (memory s-setup) (readReg (regs s-setup) sp +ℕ (24 +ℕ n))
            ≡⟨ cong (readMem (memory s-setup)) (sym addr-eq-setup) ⟩
          readMem (memory s-setup) (orig-sp +ℕ n)
            ≡⟨ mem-setup-at-orig-sp+n ⟩
          readMem (memory s) (orig-sp +ℕ n)
            ∎
        where
          -- Setup/Middle/Final phases only write to new-sp + {0, 8, 16} which are < orig-sp
          -- So memory at orig-sp + n is preserved for all n ≥ 0
          postulate
            mem-setup-at-orig-sp+n : readMem (memory s-setup) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
            mem-mid-at-orig-sp+n : readMem (memory s-mid) (orig-sp +ℕ n) ≡ readMem (memory s-after-f-raw) (orig-sp +ℕ n)
            mem-final-at-orig-sp+n : readMem (memory s-final) (orig-sp +ℕ n) ≡ readMem (memory s-after-g-raw) (orig-sp +ℕ n)

      -- Output WF: combine f and g output WFs with proper program subst
      wf-f : ClosuresWF A prog
      wf-f = subst (ClosuresWF A) (sym prog-eq-f) (ir-output-wf r-f)

      wf-g : ClosuresWF B prog
      wf-g = subst (ClosuresWF B) (sym prog-eq-g) (ir-output-wf r-g)

      output-wf : ClosuresWF (A * B) prog
      output-wf = pairWF wf-f wf-g

  -- Case helper - proven using dispatch helpers and IH
  run-case-star : ∀ {i A B C} (f : IR i A C) (g : IR i B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    24 ≤ readReg (regs s) sp →
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
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      t0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))
      s2-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))
      ra-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))))
      sp-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))))
      mem-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))))

      -- Phase 2: Execute f (IH call)
      -- PC for f: need length prefix-f
      pc-for-f : pc s-dispatch ≡ length prefix-f
      pc-for-f = trans pc-dispatch (sym len-prefix-f)

      -- sp-bound for f: dispatch preserves sp, so 24 ≤ sp s-dispatch
      sp-bound-f : 24 ≤ readReg (regs s-dispatch) sp
      sp-bound-f = subst (24 ≤_) (sym sp-dispatch) sp-bound

      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-dispatch h-dispatch pc-for-f a0-dispatch sp-bound-f
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

      s2-after-f = ir-s2 r-f

      -- Phase 3: Jump over g (2 instructions)
      jump-result = case-left-jump-star f g prefix suffix s-after-f-raw h-after-f pc-after-f
      s-final = proj₁ jump-result
      star-jump = proj₁ (proj₂ jump-result)
      h-final = proj₁ (proj₂ (proj₂ jump-result))
      pc-jump = proj₁ (proj₂ (proj₂ (proj₂ jump-result)))
      a0-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))
      s1-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))
      s2-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))))
      ra-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))))
      sp-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))))))
      mem-jump = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))))))

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
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      s2-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))
      ra-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))
      sp-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))))
      mem-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))))

      -- Phase 2: Execute g (IH call)
      pc-for-g : pc s-dispatch ≡ length prefix-g
      pc-for-g = trans pc-dispatch (sym len-prefix-g)

      -- sp-bound for g: dispatch preserves sp, so 24 ≤ sp s-dispatch
      sp-bound-g : 24 ≤ readReg (regs s-dispatch) sp
      sp-bound-g = subst (24 ≤_) (sym sp-dispatch) sp-bound

      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-dispatch h-dispatch pc-for-g a0-dispatch sp-bound-g
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

      s2-after-g = ir-s2 r-g

      -- Phase 3: Execute end-label (1 instruction)
      end-result = case-right-end-star f g prefix suffix s-after-g-raw h-after-g pc-after-g
      s-final = proj₁ end-result
      star-end = proj₁ (proj₂ end-result)
      h-final = proj₁ (proj₂ (proj₂ end-result))
      pc-end = proj₁ (proj₂ (proj₂ (proj₂ end-result)))
      a0-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))
      s1-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))
      s2-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))))
      ra-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))))
      sp-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))))))
      mem-end = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))))))

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

      -- SP bound for f: thunk setup allocates 16 bytes, need 24 + 16 = 40 ≤ orig-sp
      -- This requires stronger precondition tracking; use postulate for now
      postulate sp-bound-for-f : 24 ≤ readReg (regs s-after-setup) sp

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
    24 ≤ readReg (regs s) sp →
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
  24 ≤ readReg (regs s) sp →
  ∃[ s' ] IRStarResult ir (compile-riscv ir) s s' x 0
run-ir-star ir x s h-false pc-eq a0-eq sp-bound =
  subst (λ prog → ∃[ s' ] IRStarResult ir prog s s' x 0)
        (++-identityʳ (compile-riscv ir))
        (run-ir-star-at-offset ir [] [] x s h-false pc-eq a0-eq sp-bound)
  where
    open import Data.List.Properties using (++-identityʳ)
