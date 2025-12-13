------------------------------------------------------------------------
-- Once.Surface.IR
--
-- Surface Intermediate Representation for Once programs.
-- Extends Core IR with constructs that are desugared before optimization.
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

module Once.Surface.IR where

open import Once.Type

open import Data.String using (String)

-- | Surface IR: Extends Core IR with surface-level constructs
--
-- SurfaceIR A B represents a morphism from A to B that may contain
-- surface-level constructs (Let, Prim) that will be desugared to
-- pure categorical Core IR before optimization.
--
-- Surface-only constructs:
--   Let   : Let binding (desugars to composition + pairing)
--   Prim  : Primitive operation (opaque to optimizer)
--
data SurfaceIR : Type → Type → Set where
  -- Category structure (same as Core IR)
  id      : ∀ {A} → SurfaceIR A A
  _∘_     : ∀ {A B C} → SurfaceIR B C → SurfaceIR A B → SurfaceIR A C

  -- Product (A × B)
  fst     : ∀ {A B} → SurfaceIR (A * B) A
  snd     : ∀ {A B} → SurfaceIR (A * B) B
  ⟨_,_⟩   : ∀ {A B C} → SurfaceIR C A → SurfaceIR C B → SurfaceIR C (A * B)

  -- Coproduct (A + B)
  inl     : ∀ {A B} → SurfaceIR A (A + B)
  inr     : ∀ {A B} → SurfaceIR B (A + B)
  [_,_]   : ∀ {A B C} → SurfaceIR A C → SurfaceIR B C → SurfaceIR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → SurfaceIR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → SurfaceIR Void A

  -- Exponential (A ⇒ B)
  curry   : ∀ {A B C} → SurfaceIR (A * B) C → SurfaceIR A (B ⇒ C)
  apply   : ∀ {A B} → SurfaceIR ((A ⇒ B) * A) B

  -- Recursive types (Fixed point isomorphism)
  fold    : ∀ {F} → SurfaceIR F (Fix F)
  unfold  : ∀ {F} → SurfaceIR (Fix F) F

  -- Effect lifting (D032)
  arr     : ∀ {A B} → SurfaceIR (A ⇒ B) (Eff A B)

  --------------------------------------------------------------------------
  -- Surface-only constructs (desugared before optimization)
  --------------------------------------------------------------------------

  -- | Let binding: let x = e1 in e2
  --
  -- De Bruijn style: the body receives (original-input, bound-value).
  -- - e1 : A → B computes the bound value
  -- - e2 : A * B → C is the body, uses fst for original input, snd for bound
  --
  -- Desugars to: e2 ∘ ⟨ id , e1 ⟩
  --
  -- Example: let x = f in g x x
  --   becomes: Let f (g ∘ ⟨ snd , snd ⟩)
  --   desugars to: (g ∘ ⟨ snd , snd ⟩) ∘ ⟨ id , f ⟩
  --
  Let     : ∀ {A B C} → SurfaceIR A B → SurfaceIR (A * B) C → SurfaceIR A C

  -- | Primitive operation
  --
  -- Primitives are opaque operations provided by the runtime/platform.
  -- They cannot be optimized or decomposed into categorical generators.
  --
  -- Examples: syscalls, arithmetic, string operations
  --
  Prim    : ∀ {A B} → String → SurfaceIR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩
infixr 3 [_,_]
