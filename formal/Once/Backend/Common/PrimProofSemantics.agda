------------------------------------------------------------------------
-- Once.Backend.Common.PrimProofSemantics
--
-- Architecture-independent interface for primitive proof providers.
--
-- This module defines the contract for what domain compilers must
-- provide to prove their primitives correct. The actual proof
-- structure depends on the target architecture's execution model.
--
-- KEY INSIGHT: The concept of "proof provider" is architecture-independent:
--   "For any primitive with semantics sem and contract c,
--    provide a proof that executing c's assembly is correct"
--
-- What "correct" means (invariants, result types) is architecture-specific,
-- but the interface structure is common.
--
-- Architecture instantiation must provide:
--   - PrimProof type (what constitutes a valid proof)
--   - PrimProofProvider type (function mapping contracts to proofs)
--
-- See: Once.Backend.X86.Correct.StarBase for X86-64 implementation
------------------------------------------------------------------------

module Once.Backend.Common.PrimProofSemantics where

open import Once.Type using (Type)
open import Once.Backend.Common.PrimContract using (PrimContract)

------------------------------------------------------------------------
-- PrimProofSemantics Interface
--
-- Defines the contract for proof providers. Each architecture
-- instantiates this with its specific proof and execution types.
------------------------------------------------------------------------

record PrimProofSemantics (⦦_⦧ : Type → Set) : Set₂ where
  field
    --------------------------------------------------------------------
    -- PrimProof Type
    --
    -- The type of a correctness proof for a single primitive.
    -- This captures what it means for a primitive's execution to be
    -- correct on the target architecture.
    --
    -- Architecture instantiations define this based on their:
    --   - Machine state type
    --   - Execution trace type (Star)
    --   - Invariants (stack, registers, memory)
    --   - Result validity predicates
    --------------------------------------------------------------------

    PrimProof : ∀ {A B : Type} → (⦦ A ⦧ → ⦦ B ⦧) → PrimContract A B → Set₁

    --------------------------------------------------------------------
    -- PrimProofProvider Type
    --
    -- A proof provider maps each primitive to its correctness proof.
    -- Domain compilers (Arith, etc.) implement this by proving each
    -- of their primitives correct.
    --
    -- This is what WholeProgram receives to execute Prim instructions.
    --------------------------------------------------------------------

    PrimProofProvider : Set₁

    --------------------------------------------------------------------
    -- Provider Specification
    --
    -- A proof provider must provide a proof for any primitive.
    -- This connects PrimProofProvider to PrimProof.
    --------------------------------------------------------------------

    provider-gives-proof : PrimProofProvider →
      ∀ {A B : Type} (sem : ⦦ A ⦧ → ⦦ B ⦧) (c : PrimContract A B) →
      PrimProof sem c

open PrimProofSemantics public
