------------------------------------------------------------------------
-- Once.Backend.ContractInterfaceMachine
--
-- Contract interface parameterized by ⟦_⟧ (type interpretation).
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- IMPORTANT: This module is parameterized by ⟦_⟧ directly, NOT by
-- MachineInterface. This avoids Agda's module instantiation issues
-- where multiple imports of SemanticBaseMachine MI create separate
-- copies of ⟦_⟧ that Agda can't unify.
--
-- Usage:
--   -- In the parent module, import SemanticBaseMachine ONCE:
--   open import Once.SemanticBaseMachine MI using (⟦_⟧)
--   -- Then pass ⟦_⟧ to this module:
--   open import Once.Backend.ContractInterfaceMachine ⟦_⟧
------------------------------------------------------------------------

open import Once.Type using (Type)

module Once.Backend.ContractInterfaceMachine (⟦_⟧ : Type → Set) where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.String using (String)

------------------------------------------------------------------------
-- Contract Interface
------------------------------------------------------------------------

record ContractInterface : Set₁ where
  field
    Contract : ∀ {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set
    contract-length : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract {A} {B} sem → ℕ
    contract-assembly : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} → Contract {A} {B} sem → List String

-- Note: We don't 'open ContractInterface public' here to avoid
-- ambiguous projections when modules open their own ContractInterface CI.

-- NOTE: TrivialContract has been intentionally removed.
-- See OCP-0003 for rationale: TrivialContract required a postulate
-- asserting a falsehood (empty programs are non-empty).
-- Modules must use real contracts that provide actual assembly.
