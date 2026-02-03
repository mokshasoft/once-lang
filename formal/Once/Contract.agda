------------------------------------------------------------------------
-- Once.Contract
--
-- Contract interface for primitive operations.
-- Machine-independent: only defines assembly, not semantics.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   Contract is parameterized by types only, not by ⟦_⟧ or semantics.
--   This keeps IR machine-independent.
--   Semantics are provided separately via ContractSemantics.
------------------------------------------------------------------------

module Once.Contract where

open import Once.Type using (Type)
open import Data.Nat using (ℕ; _≥_)
open import Data.List using (List; length)
open import Data.String using (String)

------------------------------------------------------------------------
-- Contract Interface (machine-independent)
------------------------------------------------------------------------

record ContractInterface : Set₁ where
  field
    -- | The contract type, parameterized only by types (not semantics)
    Contract : (A B : Type) → Set

    -- | The compiled assembly (opaque - CCC doesn't parse this)
    contract-assembly : ∀ {A B : Type} → Contract A B → List String

    -- | Contracts must produce non-empty programs
    contract-nonempty : ∀ {A B : Type} → (c : Contract A B) → length (contract-assembly c) ≥ 1

  -- | Length of the compiled assembly (derived)
  contract-length : ∀ {A B : Type} → Contract A B → ℕ
  contract-length c = length (contract-assembly c)

------------------------------------------------------------------------
-- Contract Semantics (machine-dependent, provided separately)
------------------------------------------------------------------------

-- | Semantic interpretation of contracts
--
-- This is separate from ContractInterface to keep IR machine-independent.
-- Modules that need to evaluate IR (like Semantics) use both.
--
record ContractSemantics (CI : ContractInterface) (⟦_⟧ : Type → Set) : Set₁ where
  open ContractInterface CI
  field
    -- | Evaluate a contract on a value
    contract-eval : ∀ {A B : Type} → Contract A B → ⟦ A ⟧ → ⟦ B ⟧
