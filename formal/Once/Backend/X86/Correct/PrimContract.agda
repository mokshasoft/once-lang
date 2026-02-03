------------------------------------------------------------------------
-- Once.Backend.X86.Correct.PrimContract
--
-- Contract for primitive operations: opaque assembly for code generation.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- KEY INSIGHT: Code generation and correctness proofs are SEPARATE.
--
-- This module defines what CCC needs for CODE GENERATION:
--   - Opaque assembly (List String)
--   - Length (for jump offset calculation)
--
-- Correctness proofs (Star traces, PrimEffect, etc.) are in separate
-- modules. Domain compilers provide those proofs independently.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.PrimContract where

open import Once.Type using (Type)

open import Data.String using (String)
open import Data.List using (List; length)
open import Data.Nat using (ℕ; _≥_)

------------------------------------------------------------------------
-- Assembly: Opaque to CCC
------------------------------------------------------------------------

-- | Assembly is just a list of strings
-- CCC concatenates and emits these without parsing
Assembly : Set
Assembly = List String

------------------------------------------------------------------------
-- PrimContract: What domain compilers provide for code generation
------------------------------------------------------------------------

-- | A contract for a primitive operation
--
-- This is what CCC needs to generate code:
--   - The assembly text to emit
--   - Proof it's non-empty (for compile-length > 0)
--
-- Correctness proofs are separate - they don't affect code generation.
--
record PrimContract (A B : Type) : Set where
  field
    -- | The compiled assembly as opaque text
    prim-assembly : Assembly

    -- | Assembly must be non-empty
    prim-nonempty : length prim-assembly ≥ 1

open PrimContract public

------------------------------------------------------------------------
-- X86 Contract Interface
------------------------------------------------------------------------

open import Once.Contract using (ContractInterface)

X86ContractInterface : ContractInterface
X86ContractInterface = record
  { Contract = PrimContract
  ; contract-assembly = prim-assembly
  ; contract-nonempty = prim-nonempty
  }
