------------------------------------------------------------------------
-- Once.IR
--
-- The Intermediate Representation of Once programs.
-- These are the morphisms of a Cartesian Closed Category.
--
-- The IR is parameterized by a ContractInterface, allowing each backend
-- to provide its own contract type for primitives.
--
-- The ~12 generators form a complete basis for all pure Once programs.
--
-- Relies on Agda's default termination checker for structural recursion.
-- See Once.Backend.X86.Correct.MutualIR.Termination for orthogonal termination proof.
------------------------------------------------------------------------

module Once.IR where

open import Once.Type
open import Once.SemanticBase using (⟦_⟧)
open import Once.Backend.ContractInterface
open import Data.String using (String)
open import Data.Unit using (⊤)

------------------------------------------------------------------------
-- Parameterized IR Module
------------------------------------------------------------------------

-- | The IR is parameterized by instruction type and ContractInterface.
-- This allows each backend to provide its own contract type.
--
module IRDef {Instr : Set} (CI : ContractInterface Instr) where
  open ContractInterface CI

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
  --   Primitives:            Prim (with explicit semantics and contract)
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

    -- Effect lifting (D032)
    -- arr lifts pure functions to effectful morphisms
    -- arr : (A ⇒ B) → Eff A B
    -- At runtime, this is essentially identity - Eff A B has same representation as A ⇒ B
    arr     : ∀ {A B} → IR (A ⇒ B) (Eff A B)

    -- Primitive operations
    --
    -- Primitives are external operations provided by the runtime/platform.
    -- Each primitive carries:
    --   - name: Human-readable identifier (for debugging)
    --   - sem: The semantic function defining the operation's behavior
    --   - contract: Backend-specific compilation and correctness proof
    --
    -- The contract type is provided by the ContractInterface parameter.
    -- This enables:
    --   - eval (Prim _ sem _) x = sem x  (no evalPrim postulate!)
    --   - compile (Prim _ _ c) = contract-assembly c
    --   - correctness uses contract's proof (no run-prim-star postulate!)
    --
    Prim    : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → Contract sem → IR A B

  -- | IR∞ is now just an alias for IR (kept for backwards compatibility)
  IR∞ : Type → Type → Set
  IR∞ = IR

  infixr 9 _∘_
  infixr 4 ⟨_,_⟩
  infixr 3 [_,_]

------------------------------------------------------------------------
-- Default Instantiation (for pure semantics)
------------------------------------------------------------------------

-- | For modules that only need semantics (not compilation),
-- we provide a default instantiation with TrivialContract.
-- Uses ⊤ as a dummy instruction type (TrivialInterface produces empty programs).
--
open IRDef (TrivialInterface {⊤}) public

------------------------------------------------------------------------
-- Re-exports
------------------------------------------------------------------------

-- Export ContractInterface for backends
open import Once.Backend.ContractInterface public
  using (ContractInterface; TrivialInterface; TrivialContract; trivial)
