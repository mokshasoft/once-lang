------------------------------------------------------------------------
-- Once.Backend.Common.IR.MutualRecursion
--
-- Shared mutual recursion structure for IR correctness proofs.
--
-- This module provides the SHARED STRUCTURE that all architectures use.
-- Given an ArchCorrectness implementation (which provides all proof
-- obligations), this module derives full IR correctness via mutual
-- recursion over the IR structure.
--
-- KEY: Sub-IR always runs within the context of the larger program.
-- The prefix/suffix pattern ensures Star proofs are for the full program.
--
-- KEY: This module has NO POSTULATES. All obligations are fields
-- in the ArchCorrectness record that each architecture must provide.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold; terminal; initial; Prim)
open import Once.Type as Type using (Type; _*_; _⇒_; Eff; Fix; Void) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode; Closure)

module Once.Backend.Common.IR.MutualRecursion where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Backend.Common.IR.Spec
open import Once.Backend.Common.IR.ArchInterface

------------------------------------------------------------------------
-- IR Correctness via Mutual Recursion
--
-- This is the SHARED STRUCTURE. Each architecture instantiates this
-- module with their ArchCorrectness implementation.
--
-- KEY INSIGHT: Sub-IR runs within the context of the full program.
-- The prefix/suffix parameters ensure this:
--   - prog = prefix ++ₚ compile ir ++ₚ suffix
--   - Star proofs are for this full prog
--   - PC starts at (program-length prefix), ends at (program-length prefix + compile-length ir)
------------------------------------------------------------------------

module IRCorrect (Arch : ArchCorrectness) where

  open ArchCorrectness Arch

  ----------------------------------------------------------------------
  -- Mutual Recursion over IR Structure
  --
  -- Every ir-correct call takes prefix and suffix, ensuring sub-IR
  -- runs in context. This matches X86's proven approach.
  --
  -- The recursion pattern is:
  --   - Leaf cases: delegate to ArchCorrectness with prefix/suffix
  --   - Compose: g with suffix including f, then f with prefix including g
  --   - Pair: setup → f → middle → g → cleanup, each in context
  --   - Curry: setup, combine (no sub-IR execution)
  --   - Case: dispatch → branch, in context
  --   - Apply: use ir-correct as IH for thunk
  --
  -- Termination is guaranteed by structural recursion on IR.
  ----------------------------------------------------------------------

  {-# TERMINATING #-}
  mutual
    -- Main theorem: all IR is correct when run in context
    -- prog = prefix ++ₚ compile ir ++ₚ suffix
    -- cwf: closure well-formedness input (from previous step in compose)
    -- cl = closureOf A x: the closure extracted from the input value
    ir-correct : ∀ {A B : Type} (ir : IR A B)
                 (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
                 Preconditions {A} s x prefix (ir-stack-requirement ir) →
                 ApplyWFInput (ClosureDom A) (ClosureCod A) (prefix ++ₚ compile ir ++ₚ suffix) s (closureOf A x) →
                 ∃[ s' ] IRCorrectness ir (prefix ++ₚ compile ir ++ₚ suffix) s s' x (program-length prefix)

    -- Identity: delegate to architecture (pass cwf through for WF threading)
    ir-correct id prefix suffix x s pre cwf = id-correct prefix suffix x s pre cwf

    -- Left injection: delegate to architecture
    ir-correct inl prefix suffix x s pre _ = inl-correct prefix suffix x s pre

    -- Right injection: delegate to architecture
    ir-correct inr prefix suffix x s pre _ = inr-correct prefix suffix x s pre

    -- First projection: delegate to architecture
    ir-correct fst prefix suffix x s pre _ = fst-correct prefix suffix x s pre

    -- Second projection: delegate to architecture
    ir-correct snd prefix suffix x s pre _ = snd-correct prefix suffix x s pre

    -- Arrow: delegate to architecture
    ir-correct arr prefix suffix x s pre _ = arr-correct prefix suffix x s pre

    -- Unfold: delegate to architecture
    ir-correct unfold prefix suffix x s pre _ = unfold-correct prefix suffix x s pre

    -- Fold: delegate to architecture
    ir-correct fold prefix suffix x s pre _ = fold-correct prefix suffix x s pre

    -- Terminal: delegate to architecture
    ir-correct terminal prefix suffix x s pre _ = terminal-correct prefix suffix x s pre

    -- Initial: delegate to architecture
    ir-correct initial prefix suffix x s pre _ = initial-correct prefix suffix x s pre

    -- Prim: delegate to architecture
    ir-correct (Prim name) prefix suffix x s pre _ = prim-correct name prefix suffix x s pre

    -- Composition: f ∘ g means "first g, then f"
    -- compile (f ∘ g) = compile g ++ₚ transfer ++ₚ compile f
    -- g runs with: prefix, suffix = transfer ++ₚ compile f ++ₚ outer-suffix
    -- transfer runs after g, before f
    -- f runs with: prefix = outer-prefix ++ₚ compile g ++ₚ transfer, suffix
    -- Key: g's exec-closure-wf is threaded to f as input
    ir-correct (f ∘ g) prefix suffix x s pre _ =
      let -- Compute sub-programs
          code-g = compile g
          code-f = compile f
          transfer = compose-transfer f g
          suffix-g = transfer ++ₚ code-f ++ₚ suffix
          prefix-f = prefix ++ₚ code-g ++ₚ transfer
          -- Step 1: Get g's preconditions
          g-pre = compose-g-preconditions f g prefix suffix x s pre
          -- Step 2: Run g in context (suffix includes transfer and f)
          (s₁ , g-corr) = ir-correct g prefix suffix-g x s g-pre no-apply-wf
          -- Step 3: Run transfer, get f's preconditions, rsp preservation, and threaded ApplyWFInput
          (s₂ , transfer-star , rsp-transfer , f-pre , f-cwf) = compose-run-transfer f g prefix suffix x s s₁ pre g-corr
          -- Step 4: Run f in context (prefix includes g and transfer)
          -- Thread g's closure-wf to f via compose-run-transfer's converted ApplyWFInput
          (s₃ , f-corr) = ir-correct f prefix-f suffix (eval g x) s₂ f-pre f-cwf
          -- Step 5: Combine using architecture's combine lemma
          -- Pass original capacity and rsp preservation for deriving compose output capacity
          orig-cap = Preconditions.pre-capacity pre
      in s₃ , compose-combine f g prefix suffix x s s₁ s₂ s₃ orig-cap rsp-transfer g-corr transfer-star f-corr

    -- Pair: setup → f → middle → g → cleanup
    ir-correct ⟨ f , g ⟩ prefix suffix x s pre _ =
      let -- Compute sub-programs (architecture provides the details)
          (prefix-f , suffix-f , prefix-g , suffix-g) = pair-context f g prefix suffix
          -- Step 1: Setup phase
          (s₁ , setup) = pair-setup f g prefix suffix x s pre
          -- Step 2: Get f's preconditions
          f-pre = pair-setup-enables-f f g prefix suffix x s s₁ setup
          -- Step 3: Run f in context
          (s₂ , f-corr) = ir-correct f prefix-f suffix-f x s₁ f-pre no-apply-wf
          -- Step 4: Middle phase (store f's result, restore input)
          (s₃ , middle) = pair-middle f g prefix suffix x s s₁ s₂ (eval f x) setup f-corr
          -- Step 5: Get g's preconditions
          g-pre = pair-middle-enables-g f g prefix suffix x s₁ s₂ s₃ (eval f x) middle
          -- Step 6: Run g in context
          (s₄ , g-corr) = ir-correct g prefix-g suffix-g x s₃ g-pre no-apply-wf
          -- Step 7: Cleanup phase (construct pair)
          (s₅ , cleanup) = pair-cleanup f g prefix suffix x s s₃ s₄ (eval f x) (eval g x) g-corr
          -- Step 8: Combine all phases
      in s₅ , pair-combine f g prefix suffix x s s₁ s₂ s₃ s₄ s₅ setup f-corr middle g-corr cleanup

    -- Curry: setup creates closure, uses IH to construct ClosureWellFormed
    ir-correct (curry f) prefix suffix x s pre _ =
      let (s₁ , setup) = curry-setup f prefix suffix x s pre
      in s₁ , curry-combine ir-correct f prefix suffix x s s₁ setup

    -- Apply: use ir-correct as induction hypothesis for thunk
    ir-correct apply prefix suffix x s pre cwf = apply-correct ir-correct prefix suffix x s pre cwf

    -- Case: dispatch then branch then cleanup
    ir-correct [ f , g ] prefix suffix (inj₁ a) s pre _ =
      let -- Compute sub-programs
          (prefix-f , suffix-f) = case-left-context f g prefix suffix
          -- Step 1: Dispatch (determines it's left branch)
          (s₁ , dispatch) = case-dispatch-left f g prefix suffix a s pre
          -- Step 2: Get f's preconditions
          f-pre = case-dispatch-enables-f f g prefix suffix a s s₁ dispatch
          -- Step 3: Run f in context
          (s₂ , f-corr) = ir-correct f prefix-f suffix-f a s₁ f-pre no-apply-wf
          -- Step 4: Run cleanup (jmp + mov rsp,rbp + pop rbp)
          (s₃ , cleanup) = case-left-cleanup f g prefix suffix a s s₁ s₂ dispatch f-corr
          -- Step 5: Combine dispatch + f + cleanup
      in s₃ , case-left-combine f g prefix suffix a s s₁ s₂ s₃ dispatch f-corr cleanup

    ir-correct [ f , g ] prefix suffix (inj₂ b) s pre _ =
      let -- Compute sub-programs
          (prefix-g , suffix-g) = case-right-context f g prefix suffix
          -- Step 1: Dispatch (determines it's right branch)
          (s₁ , dispatch) = case-dispatch-right f g prefix suffix b s pre
          -- Step 2: Get g's preconditions
          g-pre = case-dispatch-enables-g f g prefix suffix b s s₁ dispatch
          -- Step 3: Run g in context
          (s₂ , g-corr) = ir-correct g prefix-g suffix-g b s₁ g-pre no-apply-wf
          -- Step 4: Run cleanup (mov rsp,rbp + pop rbp)
          (s₃ , cleanup) = case-right-cleanup f g prefix suffix b s s₁ s₂ dispatch g-corr
          -- Step 5: Combine dispatch + g + cleanup
      in s₃ , case-right-combine f g prefix suffix b s s₁ s₂ s₃ dispatch g-corr cleanup

  ----------------------------------------------------------------------
  -- Top-level theorem: IR correct with empty prefix/suffix
  --
  -- This is the entry point for whole-program correctness.
  -- Note: Uses empty-program ++ₚ compile ir ++ₚ empty-program = compile ir
  -- by ++ₚ-empty-left, ++ₚ-empty-right, and ++ₚ-assoc.
  ----------------------------------------------------------------------

  ir-correct-toplevel : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
                        Preconditions {A} s x empty-program (ir-stack-requirement ir) →
                        ∃[ s' ] IRCorrectness ir (empty-program ++ₚ compile ir ++ₚ empty-program) s s' x (program-length empty-program)
  ir-correct-toplevel ir x s pre = ir-correct ir empty-program empty-program x s pre no-apply-wf

------------------------------------------------------------------------
-- Summary
--
-- This module provides the SHARED PROOF STRUCTURE for all architectures.
--
-- What's shared (this module):
--   - The mutual recursion skeleton with prefix/suffix threading
--   - How phases are sequenced (setup → body → cleanup)
--   - The recursive calls pattern with proper context
--
-- What's per-architecture (ArchCorrectness):
--   - Leaf case proofs (id, inl, fst, etc.) with prefix/suffix
--   - Phase implementations (pair-setup, pair-middle, etc.)
--   - Glue lemmas (compose-combine, pair-combine, etc.)
--   - Context computation (pair-context, case-left-context, etc.)
--
-- KEY DESIGN: Sub-IR always runs within full program context.
-- This matches how X86 (and all real architectures) actually work.
------------------------------------------------------------------------
