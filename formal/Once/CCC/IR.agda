------------------------------------------------------------------------
-- Once.CCC.IR
--
-- The core IR based on Cartesian Closed Categories.
--
-- This is THE IR for Once - the categorical foundation that everything
-- else compiles to. Surface syntax is sugar on top.
--
-- Structure:
--   - Category: id, _∘_
--   - Products: ⟨_,_⟩, fst, snd
--   - Coproducts: inl, inr, case
--   - Terminal/Initial: terminal, initial
--   - Exponentials: curry, apply
--   - Recursive types: fold, unfold
--   - Effects: arr
--   - Primitives: Prim (opaque external operations)
--   - Memory: free-heap (explicit deallocation)
------------------------------------------------------------------------

module Once.CCC.IR where

open import Data.String using (String)

-- Import and re-export Type
open import Once.Type public

-- HeapRef for free-heap
open import Once.CCC.Machine.SMCore using (HeapRef)

------------------------------------------------------------------------
-- Allocation Mode
--
-- Specifies stack vs heap allocation for compound values.
-- Used by escape analysis and code generation.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Allocate inline on stack (non-escaping)
  Heap  : AllocMode  -- Allocate on heap (escaping)

------------------------------------------------------------------------
-- IR Language
--
-- CCC-based intermediate representation.
------------------------------------------------------------------------

data IR : Type → Type → Set where
  -- Category structure
  id : ∀ {A} → IR A A
  _∘_ : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A * B)
  ⟨_,_⟩ : ∀ {A B C} → IR A B → IR A C → AllocMode → IR A (B * C)
  fst : ∀ {A B} → IR (A * B) A
  snd : ∀ {A B} → IR (A * B) B

  -- Coproduct (A + B)
  inl : ∀ {A B} → AllocMode → IR A (A + B)
  inr : ∀ {A B} → AllocMode → IR B (A + B)
  case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒[ q ] B)
  curry : ∀ {A B C q} → IR (A * B) C → AllocMode → IR A (B ⇒[ q ] C)
  apply : ∀ {A B q} → IR ((A ⇒[ q ] B) * A) B

  -- Effect lifting
  arr : ∀ {A B q} → IR (A ⇒[ q ] B) (Eff A B)

  -- Recursive types (Fix F)
  fold : ∀ {F} → AllocMode → IR F (Fix F)
  unfold : ∀ {F} → IR (Fix F) F

  -- Explicit heap deallocation
  -- Added by escape analysis when heap values can be freed.
  free-heap : HeapRef → IR Unit Unit

  -- Primitive operations (opaque)
  Prim : ∀ {A B} → String → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩
