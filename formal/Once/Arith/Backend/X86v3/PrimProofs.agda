------------------------------------------------------------------------
-- Once.Arith.Backend.X86v3.PrimProofs
--
-- Arithmetic PrimProofProviderV3 for X86v3 CCC.
--
-- The CCC sees Prims as opaque assembly blocks. This module provides
-- proofs that arithmetic assembly satisfies the CCC's contract.
--
-- The CCC doesn't know what prims exist - it just requires a proof
-- provider that can prove any prim correct given its contract.
------------------------------------------------------------------------

module Once.Arith.Backend.X86v3.PrimProofs where

open import Data.Nat using (ℕ)
open import Data.String using (String)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.X86v3.Types using (Type; ⟦_⟧)
open import Once.Backend.X86v3.IR using (PrimContractV3)
open import Once.Backend.X86v3.Allocation using (AllocState; module FrontierInvariant)

------------------------------------------------------------------------
-- Arithmetic PrimProofProviderV3
--
-- Provides proofs for arithmetic prims (add, sub, mul, etc.)
-- The proofs are postulated - to be proven from x86 assembly semantics.
------------------------------------------------------------------------

module ArithPrimProvider {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS} using (BeforeFrontier)

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF)

  open import Once.Backend.X86v3.Dispatcher
  open PrimProofInterface {FS} program-bound
    using (PrimProofV3; PrimProofProviderV3)

  -- The proof provider for arithmetic operations
  --
  -- This is postulated because proving it requires:
  --   1. x86 assembly semantics for each arithmetic operation
  --   2. Proof that the assembly satisfies the contract
  --
  -- Sound postulate: arithmetic assembly blocks are register-only,
  -- don't modify memory, and produce correct results.
  postulate
    arith-prim-proof : PrimProofProviderV3
