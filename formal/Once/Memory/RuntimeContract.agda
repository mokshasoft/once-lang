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

open import Data.Nat using (ℕ; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (<-irrefl; ≤-<-trans; <-trans)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

-- Import core types from existing MemoryLayoutSemantics
-- (keeping compatibility with existing codebase)
open import Once.Memory.MemoryLayoutSemantics
  using (Addr; RegionBounds; InRegion)

------------------------------------------------------------------------
-- RuntimeContract: Everything the runtime must guarantee
------------------------------------------------------------------------

record RuntimeContract : Set where
  field
    --------------------------------------------------------------------
    -- Memory Region Bounds (provided by OS/linker)
    --
    -- PLAN 0.100 P0: the regions are ORDERED, stack below heap below code,
    -- and their disjointness is a THEOREM of that order. The contract used to
    -- POSTULATE disjointness while placing the stack AND the code at address
    -- 0, and it bounded EVERY program length by `code-upper` — so every
    -- `RuntimeContract` was empty and the per-arch postulates were postulates
    -- of `⊥` (`Probe.RuntimeContractModel` records the refutation and builds a model). An order is satisfiable (the
    -- probe also builds one), and nothing of the old content was used.
    --------------------------------------------------------------------

    stack-upper : ℕ    -- Stack region: [0, stack-upper]
    heap-lower  : ℕ    -- Heap region:  [heap-lower, heap-upper]
    heap-upper  : ℕ
    code-lower  : ℕ    -- Code region:  [code-lower, code-upper]
    code-upper  : ℕ

    stack<heap : stack-upper < heap-lower
    heap-valid : heap-lower ≤ heap-upper
    heap<code  : heap-upper < code-lower
    code-valid : code-lower ≤ code-upper

  --------------------------------------------------------------------
  -- Derived: Construct RegionBounds from fields
  --------------------------------------------------------------------

  stack-bounds : RegionBounds
  stack-bounds = record { lower = 0 ; upper = stack-upper ; bounds-valid = z≤n }

  heap-bounds : RegionBounds
  heap-bounds = record { lower = heap-lower ; upper = heap-upper ; bounds-valid = heap-valid }

  code-bounds : RegionBounds
  code-bounds = record { lower = code-lower ; upper = code-upper ; bounds-valid = code-valid }

  --------------------------------------------------------------------
  -- Region Disjointness — no address belongs to two regions, because each
  -- region ends below the next one's start.
  --------------------------------------------------------------------

  private
    -- `a ≤ x < y ≤ a` is impossible
    gap : ∀ {a x y} → a ≤ x → x < y → y ≤ a → ⊥
    gap a≤x x<y y≤a = <-irrefl refl (≤-<-trans y≤a (≤-<-trans a≤x x<y))

  stack<code : stack-upper < code-lower
  stack<code = <-trans stack<heap (≤-<-trans heap-valid heap<code)

  intervals-disjoint : ∀ (a : Addr) →
    ¬ (InRegion stack-bounds a × InRegion heap-bounds a) ×
    ¬ (InRegion stack-bounds a × InRegion code-bounds a) ×
    ¬ (InRegion heap-bounds a × InRegion code-bounds a)
  intervals-disjoint a =
      (λ { ((_ , a≤s) , (h≤a , _)) → gap a≤s stack<heap h≤a })
    , (λ { ((_ , a≤s) , (c≤a , _)) → gap a≤s stack<code c≤a })
    , (λ { ((_ , a≤h) , (c≤a , _)) → gap a≤h heap<code c≤a })

open RuntimeContract