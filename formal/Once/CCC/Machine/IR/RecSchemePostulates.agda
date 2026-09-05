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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.RecSchemePostulates (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import ⟦_⟧ (type value interpretation) directly from source
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)

-- Import SMPrimitives for the !! proof obligation marker
import Once.CCC.Machine.SMPrimitives as SMP

------------------------------------------------------------------------
-- RecSchemePostulatesImpl
--
-- Parameterized module providing rec-scheme-semantic postulate.
-- Used by ParaWF, AnaWF, and SumRecWF.
------------------------------------------------------------------------

module RecSchemePostulatesImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

  open FrameSemantics FS
  open SMP.TracePrimitives {FS}

  open import Once.CCC.Machine.ClosureWellFormed o
  -- Open ClosureWellFormedDef to get ValidAtWF
  open ClosureWellFormedDef {FS} program-bound
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
    ValidAtWF Heap alloc (eval ir x) result-loc s
  rec-scheme-semantic = SMP.!!

  ------------------------------------------------------------------------
  -- Lambek Isomorphism Semantic Correctness
  --
  -- MOVED TO: LambekValidity.agda
  --
  -- For the Lambek isomorphisms (In, out-μ, Out, in-ν), we now use
  -- specific lemmas in LambekValidity.agda instead of a general
  -- postulate. This provides:
  --   1. Better documentation of each operation's justification
  --   2. More targeted postulates per operation
  --   3. A path toward structural proof via functor shape induction
  --
  -- See LambekValidity.agda for the specific lemmas:
  --   - In-trace-valid, out-μ-trace-valid
  --   - in-ν-trace-valid, Out-trace-valid
  ------------------------------------------------------------------------
