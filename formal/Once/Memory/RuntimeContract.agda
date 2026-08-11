-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.RuntimeContract
--
-- What the runtime/linker must provide.
--
-- This is a RECORD - architectures provide a single instance of this
-- record, consolidating all runtime assumptions.
--
-- Categories of guarantees:
--   1. Memory bounds (from OS/linker)
--   2. Region disjointness (linker guarantee)
--   3. Code region sufficiency (compiler + linker)
--
-- The compiler invariant (dealloc-well-formed) stays in DirectSimulation
-- since it's about IR well-formedness, not runtime guarantees.
------------------------------------------------------------------------

module Once.Memory.RuntimeContract where

open import Data.Nat using (ℕ; zero; _≤_; z≤n)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)

-- Import core types from existing MemoryLayoutSemantics
-- (keeping compatibility with existing codebase)
open import Once.Memory.MemoryLayoutSemantics
  using (Addr; RegionBounds; lower; upper; InRegion)

------------------------------------------------------------------------
-- RuntimeContract: Everything the runtime must guarantee
------------------------------------------------------------------------

record RuntimeContract : Set where
  field
    --------------------------------------------------------------------
    -- Memory Region Bounds (provided by OS/linker)
    --
    -- Stack and code regions have lower = 0 by convention.
    -- This makes many proofs definitional (refl).
    --------------------------------------------------------------------

    stack-upper : ℕ    -- Stack region: [0, stack-upper]
    heap-lower  : ℕ    -- Heap region:  [heap-lower, heap-upper]
    heap-upper  : ℕ
    code-upper  : ℕ    -- Code region:  [0, code-upper]

    --------------------------------------------------------------------
    -- Region Validity (linker guarantee)
    --------------------------------------------------------------------

    -- Heap bounds are well-formed
    heap-valid : heap-lower ≤ heap-upper

  --------------------------------------------------------------------
  -- Derived: Construct RegionBounds from fields
  --------------------------------------------------------------------

  stack-bounds : RegionBounds
  stack-bounds = record { lower = 0 ; upper = stack-upper ; bounds-valid = z≤n }

  heap-bounds : RegionBounds
  heap-bounds = record { lower = heap-lower ; upper = heap-upper ; bounds-valid = heap-valid }

  code-bounds : RegionBounds
  code-bounds = record { lower = 0 ; upper = code-upper ; bounds-valid = z≤n }

  field
    --------------------------------------------------------------------
    -- Region Disjointness (linker guarantee)
    --
    -- No address belongs to multiple regions.
    --------------------------------------------------------------------

    intervals-disjoint : ∀ (a : Addr) →
      ¬ (InRegion stack-bounds a × InRegion heap-bounds a) ×
      ¬ (InRegion stack-bounds a × InRegion code-bounds a) ×
      ¬ (InRegion heap-bounds a × InRegion code-bounds a)

    --------------------------------------------------------------------
    -- Code Region Sufficiency (compiler + linker)
    --
    -- Any compiled program fits in the code region.
    --------------------------------------------------------------------

    prog-fits : ∀ (prog-len : ℕ) → prog-len ≤ code-upper

open RuntimeContract public