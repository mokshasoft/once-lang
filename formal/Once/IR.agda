------------------------------------------------------------------------
-- Once.IR
--
-- The Intermediate Representation of Once programs.
-- These are the morphisms of a Cartesian Closed Category.
--
-- The ~12 generators form a complete basis for all pure Once programs.
------------------------------------------------------------------------

module Once.IR where

open import Once.Type

-- | IR: Morphisms in a Cartesian Closed Category
--
-- IR A B represents a morphism from A to B.
-- These are the primitive building blocks (generators) from which
-- all Once programs are composed.
--
-- The generators are:
--   Category structure:     id, _∘_
--   Products:              fst, snd, ⟨_,_⟩
--   Coproducts:            inl, inr, [_,_]
--   Terminal/Initial:      terminal, initial
--   Exponential:           curry, apply
--   Recursive types:       fold, unfold
--
data IR : Type → Type → Set where
  -- Category structure
  id      : ∀ {A} → IR A A
  _∘_     : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A × B)
  fst     : ∀ {A B} → IR (A * B) A
  snd     : ∀ {A B} → IR (A * B) B
  ⟨_,_⟩   : ∀ {A B C} → IR C A → IR C B → IR C (A * B)

  -- Coproduct (A + B)
  inl     : ∀ {A B} → IR A (A + B)
  inr     : ∀ {A B} → IR B (A + B)
  [_,_]   : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒ B)
  curry   : ∀ {A B C} → IR (A * B) C → IR A (B ⇒ C)
  apply   : ∀ {A B} → IR ((A ⇒ B) * A) B

  -- Recursive types (Fixed point isomorphism)
  -- Fix F ≅ F (Fix F), witnessed by fold/unfold
  fold    : ∀ {F} → IR F (Fix F)      -- F (Fix F) → Fix F (constructor)
  unfold  : ∀ {F} → IR (Fix F) F      -- Fix F → F (Fix F) (destructor)

infixr 9 _∘_
infixr 4 ⟨_,_⟩
infixr 3 [_,_]
