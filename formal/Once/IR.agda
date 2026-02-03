------------------------------------------------------------------------
-- Once.IR
--
-- The Categorical Combinator Calculus (CCC) Intermediate Representation.
-- Machine-independent: does not depend on ⟦_⟧ or MachineInterface.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   IR is parameterized only by ContractInterface (for Prim).
--   ContractInterface provides assembly, not semantics.
--   This keeps IR completely machine-independent.
--   Semantics are provided separately in Once.Semantics.
------------------------------------------------------------------------

module Once.IR where

open import Once.Type
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

    -- Primitive operations (opaque to CCC)
    -- name: identifier for debugging/emission
    -- contract: compiled assembly from domain compiler
    Prim    : ∀ {A B} → (name : String) → Contract A B → IR A B

  IR∞ : Type → Type → Set
  IR∞ = IR

  infixr 9 _∘_
  infixr 4 ⟨_,_⟩
  infixr 3 [_,_]
