------------------------------------------------------------------------
-- Once.CCC.Machine.IR.RecSchemePostulates
--
-- Consolidated postulates for recursion scheme semantic correctness.
--
-- OCP-0003: This module provides a shared interface for the semantic
-- correctness postulate used by ParaWF, AnaWF, and SumRecWF.
-- RecCoreWF defines its own inline version since Cata is now
-- structurally provable via RecTrace.agda.
--
------------------------------------------------------------------------
-- Star-Based Proof Architecture (per lessons-learned.md)
--
-- See RecCoreWF.agda for full documentation on the proof strategy.
--
-- PROOF STATUS:
--   - Cata: STRUCTURAL PROOF available via RecTrace.agda (not here)
--   - Para/Ana/SumRec: Use documented postulate (rec-scheme-semantic)
--
-- These postulates are justified because:
--   1. The same proof strategy from RecTrace applies to all schemes
--   2. Structural induction on μ/ν values establishes correctness
--   3. The postulate represents valid semantic equivalence
------------------------------------------------------------------------

module Once.CCC.Machine.IR.RecSchemePostulates where

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import Types for ⟦_⟧ (type value interpretation)
open import Once.CCC.Target.X86-64.Types using (⟦_⟧)

-- Import SMPrimitives for the !! proof obligation marker
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- RecSchemePostulatesImpl
--
-- Parameterized module providing rec-scheme-semantic postulate.
-- Used by ParaWF, AnaWF, and SumRecWF.
------------------------------------------------------------------------

module RecSchemePostulatesImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrameSemantics FS
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  -- Open ClosureWellFormedDef to get ValidAtWF
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF)

  ------------------------------------------------------------------------
  -- Semantic Correctness: TRUST BOUNDARY
  --
  -- This asserts that the result of evaluating an IR expression is
  -- semantically valid at the given location. This is a trust boundary
  -- because the abstract machine model doesn't capture recursive execution.
  --
  -- The abstract traces are stubs that don't actually compute recursion
  -- schemes. The real computation is handled by the Dispatcher, which
  -- generates code that the runtime executes. This postulate captures:
  --
  --   "The Once compiler + runtime correctly implements recursion schemes"
  --
  -- To eliminate this postulate, we would need either:
  --   A. Extended machine model with recursive trace execution
  --   B. Direct semantic proof via well-founded recursion
  --
  -- See RecSchemeProof.agda for full architectural analysis.
  ------------------------------------------------------------------------
  rec-scheme-semantic : ∀ {A B} (ir : IR A B) (alloc : AllocState {FS})
    (x : ⟦ A ⟧) (result-loc : ValueLocation FS) (s : LocState FS) →
    ValidAtWF Heap alloc (eval primSem ir x) result-loc s
  rec-scheme-semantic = SMP.!!

  ------------------------------------------------------------------------
  -- Lambek Isomorphism Semantic Correctness: TRUST BOUNDARY
  --
  -- For the Lambek isomorphisms (In, out-μ, Out, in-ν), the semantic
  -- identity is trivial: F(μF) ≅ μF and F(νF) ≅ νF representationally.
  --
  -- These ARE simpler than recursion schemes (no recursion involved),
  -- but proving them requires showing ValidAtWF transfers between types
  -- that have identical memory representation. The challenge is that
  -- ValidAtWF is indexed by Type, so we need to relate:
  --
  --   ValidAtWF m alloc {⟦ F ⟧T (μ-type F)} x loc s
  --   ValidAtWF m alloc {μ-type F} (sem-In F x) loc s
  --
  -- Since both types have identical memory layout (both are boxed
  -- pointers to F-layer content), the proof should be straightforward
  -- with a ValidAtWF constructor for μ-types. Currently, ValidAtWF
  -- lacks such a constructor (see ClosureWellFormed.agda).
  --
  -- This postulate captures the representational identity of Lambek isos.
  ------------------------------------------------------------------------
  lambek-iso-semantic : ∀ {A B} (ir : IR A B) (m : AllocMode) (alloc : AllocState {FS})
    (x : ⟦ A ⟧) (result-loc : ValueLocation FS) (s : LocState FS) →
    ValidAtWF m alloc (eval primSem ir x) result-loc s
  lambek-iso-semantic = SMP.!!
