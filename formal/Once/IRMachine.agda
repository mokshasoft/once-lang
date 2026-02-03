------------------------------------------------------------------------
-- Once.IRMachine
--
-- IR parameterized by ⟦_⟧ (type interpretation).
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- IMPORTANT: This module is parameterized by ⟦_⟧ directly, NOT by
-- MachineInterface. This avoids Agda's module instantiation issues.
--
-- Usage:
--   -- In the parent module, import SemanticBaseMachine ONCE:
--   open import Once.SemanticBaseMachine MI using (⟦_⟧; Closure; ...)
--   -- Then pass ⟦_⟧ to this module:
--   open import Once.IRMachine ⟦_⟧
--   open import Once.Backend.ContractInterfaceMachine ⟦_⟧
--   open IRDef MyContractInterface
------------------------------------------------------------------------

open import Once.Type

module Once.IRMachine (⟦_⟧ : Type → Set) where

open import Once.Backend.ContractInterfaceMachine ⟦_⟧
open import Data.String using (String)

------------------------------------------------------------------------
-- Parameterized IR Module
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
    Prim    : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) → Contract {A} {B} sem → IR A B

  IR∞ : Type → Type → Set
  IR∞ = IR

  infixr 9 _∘_
  infixr 4 ⟨_,_⟩
  infixr 3 [_,_]

-- NOTE: No default instantiation. Modules must explicitly provide
-- a ContractInterface with real contracts. TrivialContract has been
-- removed (see OCP-0003).
