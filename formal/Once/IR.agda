------------------------------------------------------------------------
-- Once.IR
--
-- The Categorical Combinator Calculus (CCC) Intermediate Representation.
-- Parameterized by ⟦_⟧ (type interpretation).
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   IR is parameterized by ⟦_⟧ for Prim semantics.
--   Contract is machine-independent (not parameterized).
--   Prim embeds semantics directly in the IR constructor.
--
-- Usage:
--   open import Once.SemanticBaseMachine MI using (⟦_⟧)
--   open import Once.IR ⟦_⟧
--   open IRDef MyContractInterface
------------------------------------------------------------------------

open import Once.Type

module Once.IR (⟦_⟧ : Type → Set) where

open import Once.Contract
open import Data.String using (String)

------------------------------------------------------------------------
-- IR Definition (parameterized by ContractInterface)
------------------------------------------------------------------------

module IRDef (CI : ContractInterface) where
  open ContractInterface CI

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

    -- Recursive types
    fold    : ∀ {F} → IR F (Fix F)
    unfold  : ∀ {F} → IR (Fix F) F

    -- Effect lifting
    arr     : ∀ {A B} → IR (A ⇒ B) (Eff A B)

    -- Primitive operations with explicit semantics
    -- name: identifier for debugging/emission
    -- sem: the semantic function (embedded in IR)
    -- contract: compiled assembly (correctness proven separately via PrimProof)
    Prim    : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → Contract A B → IR A B

  IR∞ : Type → Type → Set
  IR∞ = IR

  infixr 9 _∘_
  infixr 4 ⟨_,_⟩
  infixr 3 [_,_]
