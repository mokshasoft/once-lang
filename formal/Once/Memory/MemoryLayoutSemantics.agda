-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.MemoryLayoutSemantics
--
-- Memory layout interfaces and core types.
--
-- This module provides interface definitions:
--   1. Core types: Addr, RegionBounds
--   2. MemoryLayout record: what architectures must provide
--   3. StackGrowth record: stack slot addressing interface
--
-- Architectures (X86, RiscV64, etc.) provide concrete implementations.
-- See X86.Layout for the X86-64 instantiation.
------------------------------------------------------------------------

module Once.Memory.MemoryLayoutSemantics where

open import Data.Nat using (ℕ; zero; _≤_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using (_×_)

-- Re-export Word from Memory
open import Once.Memory.Memory using (Word) public

------------------------------------------------------------------------
-- Core Types
------------------------------------------------------------------------

-- | Memory address (natural number)
Addr : Set
Addr = ℕ

------------------------------------------------------------------------
-- Region Bounds
------------------------------------------------------------------------

-- | A memory region defined by its address interval [lower, upper]
record RegionBounds : Set where
  field
    lower : Addr
    upper : Addr
    bounds-valid : lower ≤ upper

open RegionBounds public

-- | Address is in region if within [lower, upper]
InRegion : RegionBounds → Addr → Set
InRegion rb a = lower rb ≤ a × a ≤ upper rb

------------------------------------------------------------------------
-- MemoryLayout Interface
--
-- Architectures provide concrete instances with:
--   - Actual region bounds (from OS/runtime)
--   - Proof that regions don't overlap
------------------------------------------------------------------------

record MemoryLayout : Set where
  field
    stack-bounds : RegionBounds
    heap-bounds  : RegionBounds
    code-bounds  : RegionBounds
    intervals-disjoint : ∀ a →
      ¬ (InRegion stack-bounds a × InRegion heap-bounds a) ×
      ¬ (InRegion stack-bounds a × InRegion code-bounds a) ×
      ¬ (InRegion heap-bounds a × InRegion code-bounds a)

------------------------------------------------------------------------
-- StackGrowth Interface
--
-- Architectures provide implementations based on their stack direction:
--   - X86: stack grows downward, slots grow upward from frame base
--   - Other archs may differ
--
-- Key abstractions:
--   - grow: slot address computation (direction-independent)
--   - FramePreserved: "frame won't be clobbered by writes at stack-ptr"
--   - StackGrew: "stack expanded from old to new"
------------------------------------------------------------------------

record StackGrowth : Set₁ where
  field
    --------------------------------------------------------------------
    -- Slot Address Computation
    --------------------------------------------------------------------

    -- | Compute address at slot offset k from base address
    grow : Addr → ℕ → Addr

    -- | Growing by zero is identity (slot 0 is at base)
    grow-identity : ∀ a → grow a zero ≡ a

    -- | Different offsets yield different addresses
    grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → grow a k₁ ≢ grow a k₂

    -- | Different base addresses yield different slot addresses
    grow-addr-injective : ∀ a₁ a₂ k → a₁ ≢ a₂ → grow a₁ k ≢ grow a₂ k

    --------------------------------------------------------------------
    -- Frame Preservation
    --
    -- FramePreserved frame stack-ptr means:
    --   "Memory at frame (and its slots) won't be clobbered by
    --    stack operations at stack-ptr"
    --
    -- X86: FramePreserved = _≥_ (frame >= stack-ptr)
    -- Upward-growth: FramePreserved = _≤_ (frame <= stack-ptr)
    --------------------------------------------------------------------

    -- | Frame is preserved when writing at/below stack-ptr
    FramePreserved : Addr → Addr → Set

    -- | Stack grew from old position to new position
    StackGrew : Addr → Addr → Set

    -- | Preserved frames stay preserved when stack grows
    frame-preserved-under-growth : ∀ frame old-sp new-sp →
      FramePreserved frame old-sp →
      StackGrew old-sp new-sp →
      FramePreserved frame new-sp

    -- | Slots in a preserved frame are also preserved
    slot-in-preserved-frame : ∀ frame k sp →
      FramePreserved frame sp →
      FramePreserved (grow frame k) sp