-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.StackGrowth
--
-- X86-64 stack growth implementation.
-- Provides the StackGrowth instance for x86-64 architecture.
--
-- X86-64 stack layout:
--   - Word size: 8 bytes
--   - Slot k is at: base + k * 8 (grows upward from base)
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.StackGrowth where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-comm; m≤m+n; +-cancelˡ-≡; *-cancelˡ-≡; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Level using (0ℓ)

open import Once.Memory.MemoryLayoutSemantics
  using (Addr; StackGrowth)

------------------------------------------------------------------------
-- X86-64 Constants
------------------------------------------------------------------------

-- | Word size for x86-64 (8 bytes)
word-size : ℕ
word-size = 8

------------------------------------------------------------------------
-- X86-64 Stack Growth Function
------------------------------------------------------------------------

-- | Compute slot address: base + k * word-size
x86-grow : Addr → ℕ → Addr
x86-grow base k = base + k * word-size

------------------------------------------------------------------------
-- Proofs of StackGrowth Properties
------------------------------------------------------------------------

-- | Growing by zero is identity
x86-grow-identity : ∀ a → x86-grow a zero ≡ a
x86-grow-identity a = +-identityʳ a

-- | Different offsets yield different addresses
-- Proof: a + k₁ * 8 = a + k₂ * 8 implies k₁ * 8 = k₂ * 8 implies k₁ = k₂
x86-grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → x86-grow a k₁ ≢ x86-grow a k₂
x86-grow-injective a k₁ k₂ k₁≢k₂ eq = k₁≢k₂ (cancel-*8 (+-cancelˡ-≡ a _ _ eq))
  where
    open import Data.Nat.Properties using (*-cancelʳ-≡)
    -- If k₁ * 8 = k₂ * 8, then k₁ = k₂ (cancel the 8 on the right)
    cancel-*8 : k₁ * word-size ≡ k₂ * word-size → k₁ ≡ k₂
    cancel-*8 eq' = *-cancelʳ-≡ k₁ k₂ word-size eq'

-- | Different base addresses yield different slot addresses (same offset)
-- Proof: a₁ + k * 8 = a₂ + k * 8 implies a₁ = a₂ (cancel the k * 8)
x86-grow-addr-injective : ∀ a₁ a₂ k → a₁ ≢ a₂ → x86-grow a₁ k ≢ x86-grow a₂ k
x86-grow-addr-injective a₁ a₂ k a₁≢a₂ eq = a₁≢a₂ (+-cancelʳ-≡ (k * word-size) a₁ a₂ eq)
  where
    open import Data.Nat.Properties using (+-cancelʳ-≡)

------------------------------------------------------------------------
-- X86-64 Frame Preservation
--
-- On x86-64, the stack grows downward (toward lower addresses).
-- A frame is "preserved" when its base address is >= the current
-- stack pointer, meaning it's in the caller's region and won't be
-- clobbered by writes to the current stack frame.
------------------------------------------------------------------------

-- | Frame is preserved if frame address >= stack pointer
-- This means the frame is "above" the current stack (in caller's region)
X86FramePreserved : Addr → Addr → Set
X86FramePreserved frame stack-ptr = frame ≥ stack-ptr

-- | Stack grew if new stack pointer <= old stack pointer
-- (stack pointer decreased, stack expanded downward)
X86StackGrew : Addr → Addr → Set
X86StackGrew old-sp new-sp = new-sp ≤ old-sp

-- | Preserved frames stay preserved when stack grows
-- If frame >= old-sp and new-sp <= old-sp, then frame >= new-sp
x86-frame-preserved-under-growth : ∀ frame old-sp new-sp →
  X86FramePreserved frame old-sp →
  X86StackGrew old-sp new-sp →
  X86FramePreserved frame new-sp
x86-frame-preserved-under-growth frame old-sp new-sp fp sg = ≤-trans sg fp

-- | Slots in a preserved frame are also preserved
-- If frame >= sp, then (frame + k * 8) >= sp
x86-slot-in-preserved-frame : ∀ frame k sp →
  X86FramePreserved frame sp →
  X86FramePreserved (x86-grow frame k) sp
x86-slot-in-preserved-frame frame k sp fp = ≤-trans fp (m≤m+n frame (k * word-size))

------------------------------------------------------------------------
-- X86-64 StackGrowth Instance
------------------------------------------------------------------------

x86-stack-growth : StackGrowth
x86-stack-growth = record
  { grow = x86-grow
  ; grow-identity = x86-grow-identity
  ; grow-injective = x86-grow-injective
  ; grow-addr-injective = x86-grow-addr-injective
  ; FramePreserved = X86FramePreserved
  ; StackGrew = X86StackGrew
  ; frame-preserved-under-growth = x86-frame-preserved-under-growth
  ; slot-in-preserved-frame = x86-slot-in-preserved-frame
  }