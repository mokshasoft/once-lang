-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compile.Correct
--
-- Top-level compilation correctness theorems.
--
-- For any SurfaceIR program and input, executing the compiled code
-- produces the same result as evaluating the source program.
--
-- Structure:
--   1. Frontend correctness (shared): Surface → IR preserves semantics
--   2. Backend correctness (per-target): IR → machine state is correct
--   3. End-to-end: Surface → machine state is correct
--
-- The full correctness chain:
--   evalSurface ir x
--     ≡ eval′ (compile ir) x           [compile-preserves-semantics]
--     ≡ result in machine state       [backend compile-correct]
--
-- NOTE: Full connection requires semantics consolidation.
-- Currently, frontend uses Once.Semantics.⟦_⟧ (ℤ, Closure)
-- while backend uses Once.Sem.⟦_⟧ (ℕ, plain functions).
-- See docs/proposals/semantics-consolidation-plan.md
------------------------------------------------------------------------

module Once.Compile.Correct where

open import Once.Type
open import Once.CCC.IR as Core
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Surface.IR using (SurfaceIR)
open import Once.Surface.Desugar using (desugar)
open import Once.Surface.Desugar.Correct using (evalSurface; desugar-correct)
open import Once.Optimize using (optimize)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Escape using (escape)
open import Once.Escape.Correct using (escape-correct)

open import Relation.Binary.PropositionalEquality using (_≡_; trans)

------------------------------------------------------------------------
-- Compilation pipeline
------------------------------------------------------------------------

-- Define compile locally to avoid broken re-exports in Once.Compile
compile : ∀ {A B} → SurfaceIR A B → Core.IR A B
compile ir = escape (optimize (desugar ir))

------------------------------------------------------------------------
-- Frontend correctness (shared by all backends)
--
-- The frontend pipeline:
--   SurfaceIR → desugar → IR → optimize → IR → escape → IR
--
-- This theorem shows: eval′ (compile ir) x ≡ evalSurface ir x
-- In other words: the compiled IR has the same semantics as the source.
------------------------------------------------------------------------

compile-preserves-semantics : ∀ {A B} (ir : SurfaceIR A B) (x : ⟦ A ⟧)
                            → eval′ (compile ir) x ≡ evalSurface ir x
compile-preserves-semantics ir x =
  -- compile = escape ∘ optimize ∘ desugar
  -- eval′ (escape (optimize (desugar ir))) x
  --   ≡ eval′ (optimize (desugar ir)) x     [escape-correct]
  --   ≡ eval′ (desugar ir) x                [optimize-correct]
  --   ≡ evalSurface ir x                   [desugar-correct]
  trans (escape-correct (optimize (desugar ir)) x)
        (trans (optimize-correct (desugar ir) x)
               (desugar-correct ir x))

------------------------------------------------------------------------
-- X86-64 backend correctness
--
-- The backend theorem is in: Once.CCC.Target.X86-64.Correct
--
--   compile-correct : IR → machine state represents eval result
--
-- Full end-to-end connection (Surface → machine) requires:
--   1. Semantics consolidation (unify Once.Sem and Once.Semantics)
--   2. Then compose compile-preserves-semantics with backend
--
-- After consolidation, the theorem would be:
--
--   compile-correct-surface : ∀ (ir : SurfaceIR A B) (x : ⟦ A ⟧) →
--     ... preconditions ... →
--     ∃[ s' ] Represents (evalSurface ir x) result-loc s'
------------------------------------------------------------------------