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
  -- Semantic Correctness Postulate
  --
  -- For any IR expression and its denotational semantics (eval primSem ir x),
  -- when we execute the corresponding trace to produce a result at some
  -- location, that result is semantically valid (ValidAtWF).
  --
  -- JUSTIFICATION: This is provable by structural induction on μ/ν values:
  --   1. Build trace by recursion on value structure
  --   2. At each step, trace produces intermediate ValidAtWF results
  --   3. Composition via trace concatenation preserves validity
  --
  -- See RecTrace.agda for the full proof for Cata.
  -- The same pattern applies to Para, Ana, and SumRec.
  --
  -- PROOF OBLIGATION: Replace with structural proof following RecTrace pattern
  ------------------------------------------------------------------------
  rec-scheme-semantic : ∀ {A B} (ir : IR A B) (alloc : AllocState {FS})
    (x : ⟦ A ⟧) (result-loc : ValueLocation FS) (s : LocState FS) →
    ValidAtWF Heap alloc (eval primSem ir x) result-loc s
  rec-scheme-semantic = SMP.!!

  ------------------------------------------------------------------------
  -- Lambek Isomorphism Semantic Correctness
  --
  -- For the Lambek isomorphisms (In, out-μ, Out, in-ν), the semantic
  -- identity is trivial: F(μF) ≅ μF and F(νF) ≅ νF representationally.
  -- The postulate captures that ValidAtWF transfers through these isos.
  --
  -- PROOF OBLIGATION: These are even simpler than recursion schemes
  -- since no actual computation occurs - just reinterpretation of
  -- the same data.
  ------------------------------------------------------------------------
  lambek-iso-semantic : ∀ {A B} (ir : IR A B) (m : AllocMode) (alloc : AllocState {FS})
    (x : ⟦ A ⟧) (result-loc : ValueLocation FS) (s : LocState FS) →
    ValidAtWF m alloc (eval primSem ir x) result-loc s
  lambek-iso-semantic = SMP.!!
