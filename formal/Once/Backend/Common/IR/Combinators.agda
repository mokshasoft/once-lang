------------------------------------------------------------------------
-- Once.Backend.Common.IR.Combinators
--
-- Proof combinators for assembling phase results into full correctness.
--
-- These combinators capture the STRUCTURE of how phase proofs combine.
-- The CONTENT of each phase is architecture-specific, but the way
-- phases are sequenced and their results combined is universal.
--
-- Key combinators:
--   - pair-combine: setup + f + middle + g + cleanup → pair correct
--   - curry-combine: setup → curry correct
--   - case-combine-left/right: dispatch + branch → case correct
--   - compose-combine: f-correct + g-correct → compose correct
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold)
open import Once.Type using (Type; _*_; _⇒_; Eff) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.Combinators where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Backend.Common.IR.Spec

------------------------------------------------------------------------
-- Combinator Module
--
-- Parameterized by all the interfaces, provides combinators that
-- show how phase results combine into full correctness.
------------------------------------------------------------------------

module Combinators
    (M : MachineInterface)
    (Inv : InvariantInterface M)
    (Val : ValidityInterface M Inv)
    (CG : CodeGenInterface M) where

  open MachineInterface M
  open InvariantInterface Inv
  open ValidityInterface Val
  open CodeGenInterface CG
  open IRSpecs M Inv Val CG

  ------------------------------------------------------------------------
  -- Star Transitivity (abstract interface)
  --
  -- We need to chain Star relations. Each architecture provides this.
  ------------------------------------------------------------------------

  -- Postulate star transitivity (each architecture proves this)
  postulate
    star-trans : ∀ {prog : Program} {s₁ s₂ s₃ : State} →
      Star {M} prog s₁ s₂ →
      Star {M} prog s₂ s₃ →
      Star {M} prog s₁ s₃

  ------------------------------------------------------------------------
  -- Compose Combinator
  --
  -- For (f ∘ g), first execute g, then execute f.
  -- The result of g becomes the input for f.
  ------------------------------------------------------------------------

  -- Note: In our IR notation, (f ∘ g) means "first g, then f"
  -- This is standard categorical composition: (f ∘ g)(x) = f(g(x))

  -- Compose correctness follows from:
  --   1. g is correct with input x
  --   2. f is correct with input (eval g x)
  --   3. Star sequences compose via transitivity

  -- The actual combination is straightforward: chain the stars,
  -- the final output validity comes from f's correctness.

  ------------------------------------------------------------------------
  -- Pair Combinator
  --
  -- For ⟨ f , g ⟩, execute: setup → f → middle → g → cleanup
  -- The combinator shows how these five pieces fit together.
  ------------------------------------------------------------------------

  -- Given:
  --   setup-post: SetupPost s s₁ x
  --   f-correct: IRCorrectness f prog s₁ s₂ x offset₁
  --   middle-post: MiddlePost s₁ s₂ s₃ x (eval f x)
  --   g-correct: IRCorrectness g prog s₃ s₄ x offset₂
  --   cleanup-post: CleanupPost s s₁ s₃ s₄ s₅ x (eval f x) (eval g x)
  --
  -- Produce: IRCorrectness ⟨ f , g ⟩ prog s s₅ x offset

  -- The key insight: cleanup-post provides the ValidAt for the pair,
  -- which is exactly what IRCorrectness needs for output validity.

  ------------------------------------------------------------------------
  -- Curry Combinator
  --
  -- For curry f, only setup is needed (creates closure, skips thunk).
  -- The thunk is executed via apply, not here.
  ------------------------------------------------------------------------

  -- Given:
  --   setup-post: CurrySpecs.SetupPost f s s₁ x
  --
  -- Produce: IRCorrectness (curry f) prog s s₁ x offset

  -- This is the simplest combinator: setup directly provides
  -- the closure validity required by IRCorrectness.

  ------------------------------------------------------------------------
  -- Case Combinators (Left and Right)
  --
  -- For [ f , g ], dispatch determines which branch, then execute.
  ------------------------------------------------------------------------

  -- Left case: input is inj₁ a
  -- Given:
  --   dispatch-left: DispatchLeftPost f g s s₁ a
  --   f-correct: IRCorrectness f prog s₁ s₂ a offset
  --
  -- Produce: IRCorrectness [ f , g ] prog s s₂ (inj₁ a) offset

  -- Right case: input is inj₂ b
  -- Given:
  --   dispatch-right: DispatchRightPost f g s s₁ b
  --   g-correct: IRCorrectness g prog s₁ s₂ b offset
  --
  -- Produce: IRCorrectness [ f , g ] prog s s₂ (inj₂ b) offset

  -- Note: eval [ f , g ] (inj₁ a) = eval f a
  --       eval [ f , g ] (inj₂ b) = eval g b
  -- So the branch correctness directly gives the case correctness.

  ------------------------------------------------------------------------
  -- Identity Combinator (trivial)
  --
  -- Id doesn't need phases - the architecture proves it directly.
  -- But we note: eval id x = x, so ValidAt x addr mem
  -- is exactly what we need.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Summary: The Combination Pattern
  --
  -- For each composite IR constructor:
  --
  -- 1. Execute phases in order, threading state
  -- 2. Use star-trans to chain execution relations
  -- 3. Extract the final ValidAt from the cleanup phase
  -- 4. Extract preserved registers/memory from phases
  -- 5. Package into IRCorrectness record
  --
  -- The architecture provides the CONTENT of each phase.
  -- The combinators provide the STRUCTURE of how they fit.
  ------------------------------------------------------------------------

------------------------------------------------------------------------
-- Why This Module is Mostly Commentary
--
-- In practice, the "combinators" are implemented as part of the
-- mutual recursion in MutualRecursion.agda. The actual combination
-- is just record construction from phase results.
--
-- This module documents the PATTERN that mutual recursion follows.
-- The actual implementation uses the records directly:
--
--   ir-correct (pair ⟨f,g⟩) x s pre =
--     let (s₁ , setup) = pair-setup-correct f g x s pre
--         (s₂ , f-correct) = ir-correct f x s₁ (from-setup setup)
--         (s₃ , middle) = pair-middle-correct f g x s s₁ s₂ (eval f x)
--         (s₄ , g-correct) = ir-correct g x s₃ (from-middle middle)
--         (s₅ , cleanup) = pair-cleanup-correct f g x s s₁ s₃ s₄ (eval f x) (eval g x)
--     in s₅ , record
--         { exec-star = star-trans (star-trans (star-trans (star-trans
--             setup.star f-correct.exec-star) middle.star) g-correct.exec-star) cleanup.star
--         ; exec-output-valid = cleanup.cleanup-output-valid
--         ; ... }
--
-- The pattern is always the same; only the phases differ.
------------------------------------------------------------------------
