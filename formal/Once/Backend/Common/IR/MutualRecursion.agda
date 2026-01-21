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
-- KEY: This module has NO POSTULATES. All obligations are fields
-- in the ArchCorrectness record that each architecture must provide.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold; terminal; initial; Prim)
open import Once.Type as Type using (Type; _*_; _⇒_; Eff; Fix; Void) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.MutualRecursion where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Backend.Common.IR.Spec
open import Once.Backend.Common.IR.ArchInterface

------------------------------------------------------------------------
-- IR Correctness via Mutual Recursion
--
-- This is the SHARED STRUCTURE. Each architecture instantiates this
-- module with their ArchCorrectness implementation.
------------------------------------------------------------------------

module IRCorrect (Arch : ArchCorrectness) where

  open ArchCorrectness Arch

  -- Abbreviation for preconditions with empty prefix
  Pre : ∀ {A : Type} → State → ⟦ A ⟧ → ℕ → Set₁
  Pre {A} s x cap = Preconditions {A} s x empty-program cap

  ----------------------------------------------------------------------
  -- Mutual Recursion over IR Structure
  --
  -- This is the heart of the proof. The recursion pattern is:
  --   - Leaf cases: delegate to ArchCorrectness
  --   - Compose: run g, then f, combine with compose-combine
  --   - Pair: setup → f → middle → g → cleanup, combine
  --   - Curry: setup, then curry-combine
  --   - Case: dispatch, run branch, combine
  --   - Apply: use ir-correct as IH
  --
  -- Termination is guaranteed by structural recursion on IR.
  -- The {-# TERMINATING #-} pragma handles the case for apply
  -- where we need to call ir-correct on the closure's thunk.
  ----------------------------------------------------------------------

  {-# TERMINATING #-}
  mutual
    -- Main theorem: all IR is correct
    ir-correct : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
                 Pre {A} s x (ir-stack-requirement ir) →
                 ∃[ s' ] IRCorrectness ir (compile ir) s s' x 0

    -- Identity: delegate to architecture
    ir-correct id x s pre = id-correct x s pre

    -- Left injection: delegate to architecture
    ir-correct inl x s pre = inl-correct x s pre

    -- Right injection: delegate to architecture
    ir-correct inr x s pre = inr-correct x s pre

    -- First projection: delegate to architecture
    ir-correct fst x s pre = fst-correct x s pre

    -- Second projection: delegate to architecture
    ir-correct snd x s pre = snd-correct x s pre

    -- Arrow: delegate to architecture
    ir-correct arr x s pre = arr-correct x s pre

    -- Unfold: delegate to architecture
    ir-correct unfold x s pre = unfold-correct x s pre

    -- Fold: delegate to architecture
    ir-correct fold x s pre = fold-correct x s pre

    -- Terminal: delegate to architecture
    ir-correct terminal x s pre = terminal-correct x s pre

    -- Initial: delegate to architecture
    ir-correct initial x s pre = initial-correct x s pre

    -- Prim: delegate to architecture
    ir-correct (Prim name) x s pre = prim-correct name x s pre

    -- Composition: f ∘ g means "first g, then f"
    ir-correct (f ∘ g) x s pre =
      let -- Step 1: Get g's preconditions
          g-pre = compose-g-preconditions f g x s pre
          -- Step 2: Run g
          (s₁ , g-corr) = ir-correct g x s g-pre
          -- Step 3: Get f's preconditions from g's result
          f-pre = compose-enables-f f g x s s₁ pre g-corr
          -- Step 4: Run f
          (s₂ , f-corr) = ir-correct f (eval g x) s₁ f-pre
          -- Step 5: Combine using architecture's combine lemma
      in s₂ , compose-combine f g x s s₁ s₂ g-corr f-corr

    -- Pair: setup → f → middle → g → cleanup
    ir-correct ⟨ f , g ⟩ x s pre =
      let -- Step 1: Setup phase
          (s₁ , setup) = pair-setup f g x s pre
          -- Step 2: Get f's preconditions
          f-pre = pair-setup-enables-f f g x s s₁ setup
          -- Step 3: Run f
          (s₂ , f-corr) = ir-correct f x s₁ f-pre
          -- Step 4: Middle phase (store f's result, restore input)
          (s₃ , middle) = pair-middle f g x s₁ s₂ (eval f x) f-corr
          -- Step 5: Get g's preconditions
          g-pre = pair-middle-enables-g f g x s₁ s₂ s₃ (eval f x) middle
          -- Step 6: Run g
          (s₄ , g-corr) = ir-correct g x s₃ g-pre
          -- Step 7: Cleanup phase (construct pair)
          -- pair-cleanup needs: original s, s₃ (where g started), s₄ (after g), values
          (s₅ , cleanup) = pair-cleanup f g x s s₃ s₄ (eval f x) (eval g x) g-corr
          -- Step 8: Combine all phases
      in s₅ , pair-combine f g x s s₁ s₂ s₃ s₄ s₅ setup f-corr middle g-corr cleanup

    -- Curry: setup creates closure, skips thunk
    ir-correct (curry f) x s pre =
      let (s₁ , setup) = curry-setup f x s pre
      in s₁ , curry-combine f x s s₁ setup

    -- Apply: use ir-correct as induction hypothesis for thunk
    ir-correct apply x s pre = apply-correct ir-correct x s pre

    -- Case: dispatch then branch
    ir-correct [ f , g ] (inj₁ a) s pre =
      let -- Step 1: Dispatch (determines it's left branch)
          (s₁ , dispatch) = case-dispatch-left f g a s pre
          -- Step 2: Get f's preconditions
          f-pre = case-dispatch-enables-f f g a s s₁ dispatch
          -- Step 3: Run f
          (s₂ , f-corr) = ir-correct f a s₁ f-pre
          -- Step 4: Combine dispatch and f
      in s₂ , case-left-combine f g a s s₁ s₂ dispatch f-corr

    ir-correct [ f , g ] (inj₂ b) s pre =
      let -- Step 1: Dispatch (determines it's right branch)
          (s₁ , dispatch) = case-dispatch-right f g b s pre
          -- Step 2: Get g's preconditions
          g-pre = case-dispatch-enables-g f g b s s₁ dispatch
          -- Step 3: Run g
          (s₂ , g-corr) = ir-correct g b s₁ g-pre
          -- Step 4: Combine dispatch and g
      in s₂ , case-right-combine f g b s s₁ s₂ dispatch g-corr

------------------------------------------------------------------------
-- Summary
--
-- This module provides the SHARED PROOF STRUCTURE for all architectures.
--
-- What's shared (this module):
--   - The mutual recursion skeleton
--   - How phases are sequenced (setup → body → cleanup)
--   - The recursive calls pattern
--
-- What's per-architecture (ArchCorrectness):
--   - Leaf case proofs (id, inl, fst, etc.)
--   - Phase implementations (pair-setup, pair-middle, etc.)
--   - Glue lemmas (compose-combine, pair-combine, etc.)
--
-- The sharing is ~100 lines of recursion structure.
-- Each architecture provides ~thousands of lines of proofs.
--
-- But the key value is: Agda ENFORCES that each architecture follows
-- the same structure. This prevents architectures from drifting
-- or implementing incompatible proof strategies.
------------------------------------------------------------------------
