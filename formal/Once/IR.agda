------------------------------------------------------------------------
-- Once.IR
--
-- The Intermediate Representation of Once programs.
-- These are the morphisms of a Cartesian Closed Category.
--
-- The ~12 generators form a complete basis for all pure Once programs.
--
-- Relies on Agda's default termination checker for structural recursion.
-- See Once.Backend.X86.Correct.MutualIR.Termination for orthogonal termination proof.
------------------------------------------------------------------------

module Once.IR where

open import Once.Type

-- | AllocMode: Strategy for allocating compound values
--
-- Stack: Safe to allocate on the stack (does not escape)
-- Heap:  Must allocate on the heap (may escape)
--
-- Initially, all allocations use Heap mode for backwards compatibility.
-- Level 1 escape analysis will identify safe Stack allocations.
data AllocMode : Set where
  Stack : AllocMode
  Heap  : AllocMode

-- | IR: Morphisms in a Cartesian Closed Category
--
-- IR A B represents a morphism from A to B.
-- Termination is guaranteed by structural recursion on IR constructors.
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
  ⟨_,_⟩   : ∀ {A B C} → IR C A → IR C B → AllocMode → IR C (A * B)

  -- Coproduct (A + B)
  inl     : ∀ {A B} → AllocMode → IR A (A + B)
  inr     : ∀ {A B} → AllocMode → IR B (A + B)
  [_,_]   : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒ B)
  curry   : ∀ {A B C} → IR (A * B) C → AllocMode → IR A (B ⇒ C)
  apply   : ∀ {A B} → IR ((A ⇒ B) * A) B

  -- Recursive types (Fixed point isomorphism)
  -- Fix F ≅ F (Fix F), witnessed by fold/unfold
  fold    : ∀ {F} → IR F (Fix F)      -- F (Fix F) → Fix F (constructor)
  unfold  : ∀ {F} → IR (Fix F) F      -- Fix F → F (Fix F) (destructor)

  -- Effect lifting (D032)
  -- arr lifts pure functions to effectful morphisms
  -- arr : (A ⇒ B) → Eff A B
  -- At runtime, this is essentially identity - Eff A B has same representation as A ⇒ B
  arr     : ∀ {A B} → IR (A ⇒ B) (Eff A B)

-- | IR∞ is now just an alias for IR (kept for backwards compatibility)
IR∞ : Type → Type → Set
IR∞ = IR

infixr 9 _∘_
infixr 4 ⟨_,_⟩
infixr 3 [_,_]
