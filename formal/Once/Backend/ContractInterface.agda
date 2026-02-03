------------------------------------------------------------------------
-- Once.Backend.ContractInterface
--
-- Abstract interface that all backend contract types must implement.
--
-- This enables the IR to be parameterized by backend contracts while
-- keeping the core IR definition backend-agnostic.
--
-- Each backend (X86, AArch64, RiscV64) provides its own contract type
-- that satisfies this interface.
--
-- The interface is parameterized by the instruction type (Instr) so that
-- contract-program can return actual instructions for code generation.
------------------------------------------------------------------------

module Once.Backend.ContractInterface where

open import Once.Type using (Type)
open import Once.SemanticBase using (⟦_⟧)

open import Data.Nat using (ℕ; _≥_; suc; zero)
open import Data.List using (List; length)
open import Data.String using (String)

------------------------------------------------------------------------
-- Contract Interface
------------------------------------------------------------------------

-- | What every backend's contract type must provide
--
-- Parameterized by:
--   Instr : The backend's instruction type (e.g., X86.Instr, AArch64.Instr)
--
-- A contract bundles:
--   1. Assembly code (actual instructions for code generation)
--   2. Length information (for PC calculations)
--
-- The correctness proofs are backend-specific and not part of this
-- interface - they're used internally by each backend's correctness module.
--
record ContractInterface (Instr : Set) : Set₁ where
  field
    -- | The contract type, parameterized by semantic function
    Contract : ∀ {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set

    -- | The compiled assembly (actual instructions)
    -- CodeGen emits these directly for Prim nodes
    contract-program : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                       Contract sem → List Instr

    -- | Contracts must produce non-empty programs
    -- This ensures compile-length ir > 0 for all IR terms
    contract-nonempty : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                        (c : Contract sem) → length (contract-program c) ≥ 1

  -- | Length of the compiled assembly (derived from contract-program)
  contract-length : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                    Contract sem → ℕ
  contract-length c = length (contract-program c)

------------------------------------------------------------------------
-- Trivial Contract (for pure semantics without backend)
------------------------------------------------------------------------

-- | A trivial contract that carries no information
-- Used when we only care about semantics, not compilation
--
record TrivialContract {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  constructor trivial

-- | The trivial interface - for pure semantics without execution
-- Parameterized by any instruction type
-- Note: contract-nonempty is postulated since TrivialInterface is never executed.
-- When execution is needed, use a real backend interface like X86ContractInterface.
TrivialInterface : ∀ {Instr : Set} → ContractInterface Instr
TrivialInterface {Instr} = record
  { Contract = TrivialContract
  ; contract-program = λ _ → []
  ; contract-nonempty = trivial-nonempty
  }
  where
    open import Data.List using ([])
    -- Postulated: TrivialInterface is only for semantics, not execution
    postulate trivial-nonempty : ∀ {A B} {sem : ⟦ A ⟧ → ⟦ B ⟧} → (c : TrivialContract sem) → length {A = Instr} [] ≥ 1
