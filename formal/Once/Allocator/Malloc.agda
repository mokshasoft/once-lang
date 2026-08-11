-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Allocator.Malloc
--
-- Minimal malloc-like interface.
--
-- Operations:
--   alloc : request n bytes, get address (or nothing if OOM)
--   free  : return memory (may be no-op for arena allocators)
--
-- Properties:
--   alloc-in-heap : allocated addresses are in heap region
--
-- State is threaded explicitly (pure functional), but the interface
-- is minimal - no witness types, no slot-size in interface.
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; Addr)

module Once.Allocator.Malloc (layout : MemoryLayout) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Memory.Regions layout using (InHeap)

------------------------------------------------------------------------
-- Malloc Interface
------------------------------------------------------------------------

record Malloc : Set₁ where
  field
    -- Allocator state (implementation-specific)
    State : Set
    init : State

    -- Core operations
    alloc : ℕ → State → Maybe (Addr × State)
    free  : Addr → State → State

    -- Property: allocated addresses are in heap
    alloc-in-heap : ∀ {n s addr s'} →
                    alloc n s ≡ just (addr , s') →
                    InHeap addr

open Malloc public