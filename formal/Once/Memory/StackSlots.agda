-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.StackSlots
--
-- Stack slot addressing derived from StackGrowth interface.
--
-- This module is PARAMETERIZED over:
--   - MemoryLayout: for StackPointer (which needs InStack)
--   - StackGrowth: for slot address computation
--
-- Provides:
--   - slot-addr: compute address of slot k in frame
--   - Distinctness lemmas for slots and frames
------------------------------------------------------------------------

open import Once.Memory.MemoryLayoutSemantics
  using (MemoryLayout; StackGrowth; Addr)

module Once.Memory.StackSlots
  (layout : MemoryLayout)
  (sg : StackGrowth)
  where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

-- Import Regions for InStack and StackAddr
open import Once.Memory.Regions layout public
  using (InStack)

------------------------------------------------------------------------
-- Stack Address Type (bundled with region proof)
------------------------------------------------------------------------

-- | Stack address: in stack region by construction
record StackAddr : Set where
  constructor stack-addr
  field
    addr : Addr
    in-stack : InStack addr

open StackAddr public

-- | StackPointer is an alias for StackAddr
StackPointer : Set
StackPointer = StackAddr

------------------------------------------------------------------------
-- Stack Growth Interface (from parameter)
------------------------------------------------------------------------

open StackGrowth sg public
  using (grow; grow-identity; grow-injective; grow-addr-injective;
         FramePreserved; StackGrew; frame-preserved-under-growth;
         slot-in-preserved-frame)

------------------------------------------------------------------------
-- Slot Address Computation
------------------------------------------------------------------------

-- | Compute address of slot k in stack frame at sp
slot-addr : StackPointer → ℕ → Addr
slot-addr sp k = grow (addr sp) k

-- | Initial slot is at the stack pointer base (from grow-identity)
init-slot-at-base : ∀ sp → slot-addr sp zero ≡ addr sp
init-slot-at-base sp = grow-identity (addr sp)

-- | Different offsets give different addresses (from grow-injective)
offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
offset-distinct sp k₁ k₂ k₁≢k₂ = grow-injective (addr sp) k₁ k₂ k₁≢k₂

-- | Different stack pointers give different slot addresses (same offset)
sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
sp-distinct sp₁ sp₂ k addr≢ = grow-addr-injective (addr sp₁) (addr sp₂) k addr≢

------------------------------------------------------------------------
-- Slot Region Membership
------------------------------------------------------------------------

-- | Slot 0 is in stack region (trivial: slot-addr sp 0 = addr sp)
slot-in-stack-0 : ∀ sp → InStack (slot-addr sp 0)
slot-in-stack-0 sp = subst InStack (sym (grow-identity (addr sp))) (in-stack sp)

-- | DEPRECATED: General slot-in-stack requires capacity evidence for k > 0
-- Kept for backward compatibility; callers should migrate to:
--   k = 0: use slot-in-stack-0
--   k > 0: use StackCapacity.capacity-maintained
slot-in-stack : ∀ sp k → InStack (slot-addr sp k)
slot-in-stack sp zero = slot-in-stack-0 sp
slot-in-stack sp (suc k) = slot-in-stack-suc sp k
  where
    postulate
      slot-in-stack-suc : ∀ sp k → InStack (slot-addr sp (suc k))

------------------------------------------------------------------------
-- Address Type Conversions
------------------------------------------------------------------------

from-raw-stack : (a : Addr) → InStack a → StackAddr
from-raw-stack a proof = stack-addr a proof

to-raw-stack : StackAddr → Addr
to-raw-stack sa = StackAddr.addr sa