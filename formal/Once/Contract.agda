------------------------------------------------------------------------
-- Once.Contract
--
-- Contract interface for primitive operations.
-- Machine-independent: only defines assembly structure.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- KEY DESIGN:
--   Contract is parameterized by types only.
--   Semantics is embedded in Prim constructor (not here).
--   This keeps Contract machine-independent.
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
    -- | The contract type, parameterized only by types
    Contract : (A B : Type) → Set

    -- | The compiled assembly (opaque - CCC doesn't parse this)
    contract-assembly : ∀ {A B : Type} → Contract A B → List String

    -- | Contracts must produce non-empty programs
    contract-nonempty : ∀ {A B : Type} → (c : Contract A B) → length (contract-assembly c) ≥ 1

  -- | Length of the compiled assembly (derived)
  contract-length : ∀ {A B : Type} → Contract A B → ℕ
  contract-length c = length (contract-assembly c)

-- Note: ContractSemantics has been removed.
-- Semantics is now embedded directly in the Prim constructor.
-- See Once.IR for the new Prim signature.
