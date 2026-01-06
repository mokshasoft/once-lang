------------------------------------------------------------------------
-- Once.IR
--
-- The Intermediate Representation of Once programs.
-- These are the morphisms of a Cartesian Closed Category.
--
-- The ~12 generators form a complete basis for all pure Once programs.
--
-- Uses sized types to enable modular termination proofs.
-- Size parameter tracks structural depth for termination checking.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.IRS where

open import Size
open import Once.Type

-- | IR: Morphisms in a Cartesian Closed Category (sized)
--
-- IR i A B represents a morphism from A to B with size bound i.
-- The size parameter enables modular termination proofs:
--   - Base cases (id, fst, etc.) work at any size ↑ i
--   - Recursive cases (_∘_, ⟨_,_⟩, etc.) require sub-IR at size i
--
-- This allows extracting recursive helpers to separate modules while
-- maintaining termination proofs via Size< constraints.
--
-- The generators are:
--   Category structure:     id, _∘_
--   Products:              fst, snd, ⟨_,_⟩
--   Coproducts:            inl, inr, [_,_]
--   Terminal/Initial:      terminal, initial
--   Exponential:           curry, apply
--   Recursive types:       fold, unfold
--
data IR : Size → Type → Type → Set where
  -- Category structure
  id      : ∀ {i A} → IR (↑ i) A A
  _∘_     : ∀ {i A B C} → IR i B C → IR i A B → IR (↑ i) A C

  -- Product (A × B)
  fst     : ∀ {i A B} → IR (↑ i) (A * B) A
  snd     : ∀ {i A B} → IR (↑ i) (A * B) B
  ⟨_,_⟩   : ∀ {i A B C} → IR i C A → IR i C B → IR (↑ i) C (A * B)

  -- Coproduct (A + B)
  inl     : ∀ {i A B} → IR (↑ i) A (A + B)
  inr     : ∀ {i A B} → IR (↑ i) B (A + B)
  [_,_]   : ∀ {i A B C} → IR i A C → IR i B C → IR (↑ i) (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {i A} → IR (↑ i) A Unit

  -- Initial object (Void)
  initial : ∀ {i A} → IR (↑ i) Void A

  -- Exponential (A ⇒ B)
  curry   : ∀ {i A B C} → IR i (A * B) C → IR (↑ i) A (B ⇒ C)
  apply   : ∀ {i A B} → IR (↑ i) ((A ⇒ B) * A) B

  -- Recursive types (Fixed point isomorphism)
  -- Fix F ≅ F (Fix F), witnessed by fold/unfold
  fold    : ∀ {i F} → IR (↑ i) F (Fix F)      -- F (Fix F) → Fix F (constructor)
  unfold  : ∀ {i F} → IR (↑ i) (Fix F) F      -- Fix F → F (Fix F) (destructor)

  -- Effect lifting (D032)
  -- arr lifts pure functions to effectful morphisms
  -- arr : (A ⇒ B) → Eff A B
  -- At runtime, this is essentially identity - Eff A B has same representation as A ⇒ B
  arr     : ∀ {i A B} → IR (↑ i) (A ⇒ B) (Eff A B)

-- | Size-polymorphic IR (for backwards compatibility)
-- Most code can use IR∞ which works at any size
IR∞ : Type → Type → Set
IR∞ A B = ∀ {i} → IR i A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩
infixr 3 [_,_]
