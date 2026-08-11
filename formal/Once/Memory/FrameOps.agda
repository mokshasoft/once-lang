-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.FrameOps
--
-- Frame-level memory operations.
--
-- This module is PARAMETERIZED over:
--   - MemoryLayout: for region predicates
--   - StackGrowth: for slot addressing
--
-- Provides:
--   - frameSlot: read value at slot k of frame
--   - Memory preservation lemmas (stack writes don't affect heap/code)
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; StackGrowth; Addr)

module Once.Memory.FrameOps
  (layout : MemoryLayout)
  (sg : StackGrowth)
  where

open import Data.Nat using (ℕ; zero)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Import from Regions
open import Once.Memory.Regions layout
  using (InStack; InHeap; InCode;
         stack-heap-addr-disjoint; stack-code-addr-disjoint)

-- Import from StackSlots
open import Once.Memory.StackSlots layout sg
  using (StackPointer; slot-addr; addr; init-slot-at-base)

-- Import Memory operations
open import Once.Memory.Memory
  using (Memory; Word; readMem; writeMem; readMem-writeMem-diff)

------------------------------------------------------------------------
-- Frame Slot Access
------------------------------------------------------------------------

-- | Read value at slot k of stack frame at sp
frameSlot : Memory → StackPointer → ℕ → Maybe Word
frameSlot mem sp k = readMem mem (slot-addr sp k)

------------------------------------------------------------------------
-- Memory Preservation
--
-- Writing to stack doesn't affect heap/code regions (from disjointness).
------------------------------------------------------------------------

-- | Writing to a stack address preserves heap memory
stackAddr-write-preserves-heap : ∀ mem a val heap-a →
  InStack a → InHeap heap-a →
  readMem (writeMem mem a val) heap-a ≡ readMem mem heap-a
stackAddr-write-preserves-heap mem a val heap-a in-s in-h =
  readMem-writeMem-diff mem a heap-a val (stack-heap-addr-disjoint a heap-a in-s in-h)

-- | Writing to a stack address preserves code memory
stackAddr-write-preserves-code : ∀ mem a val code-a →
  InStack a → InCode code-a →
  readMem (writeMem mem a val) code-a ≡ readMem mem code-a
stackAddr-write-preserves-code mem a val code-a in-s in-c =
  readMem-writeMem-diff mem a code-a val (stack-code-addr-disjoint a code-a in-s in-c)

------------------------------------------------------------------------
-- Frame Slot Internal Lemmas
------------------------------------------------------------------------

module FrameSlotInternal where
  -- | frameSlot at initial slot reads from the stack pointer address
  init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
  init-frame-slot-at-base mem sp = cong (readMem mem) (init-slot-at-base sp)

  -- | frameSlot is just readMem at the slot address (by definition)
  frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
  frameSlot-is-readMem mem sp k = refl