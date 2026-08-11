-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.StackGrowth
--
-- x86-32 stack growth implementation.
-- Provides the StackGrowth instance for x86-32 architecture.
--
-- x86-32 stack layout:
--   - Word size: 4 bytes
--   - Slot k is at: base + k * 4 (grows upward from base)
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.StackGrowth where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-comm; m≤m+n; +-cancelˡ-≡; *-cancelˡ-≡; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Level using (0ℓ)

open import Once.Memory.MemoryLayoutSemantics
  using (Addr; StackGrowth)

------------------------------------------------------------------------
-- x86-32 Constants
------------------------------------------------------------------------

-- | Word size for x86-32 (4 bytes)
word-size : ℕ
word-size = 4

------------------------------------------------------------------------
-- x86-32 Stack Growth Function
------------------------------------------------------------------------

-- | Compute slot address: base + k * word-size
x86-32-grow : Addr → ℕ → Addr
x86-32-grow base k = base + k * word-size

------------------------------------------------------------------------
-- Proofs of StackGrowth Properties
------------------------------------------------------------------------

-- | Growing by zero is identity
x86-32-grow-identity : ∀ a → x86-32-grow a zero ≡ a
x86-32-grow-identity a = +-identityʳ a

-- | Different offsets yield different addresses
-- Proof: a + k₁ * 4 = a + k₂ * 4 implies k₁ * 4 = k₂ * 4 implies k₁ = k₂
x86-32-grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → x86-32-grow a k₁ ≢ x86-32-grow a k₂
x86-32-grow-injective a k₁ k₂ k₁≢k₂ eq = k₁≢k₂ (cancel-*4 (+-cancelˡ-≡ a _ _ eq))
  where
    open import Data.Nat.Properties using (*-cancelʳ-≡)
    -- If k₁ * 4 = k₂ * 4, then k₁ = k₂ (cancel the 4 on the right)
    cancel-*4 : k₁ * word-size ≡ k₂ * word-size → k₁ ≡ k₂
    cancel-*4 eq' = *-cancelʳ-≡ k₁ k₂ word-size eq'

-- | Different base addresses yield different slot addresses (same offset)
-- Proof: a₁ + k * 4 = a₂ + k * 4 implies a₁ = a₂ (cancel the k * 4)
x86-32-grow-addr-injective : ∀ a₁ a₂ k → a₁ ≢ a₂ → x86-32-grow a₁ k ≢ x86-32-grow a₂ k
x86-32-grow-addr-injective a₁ a₂ k a₁≢a₂ eq = a₁≢a₂ (+-cancelʳ-≡ (k * word-size) a₁ a₂ eq)
  where
    open import Data.Nat.Properties using (+-cancelʳ-≡)

------------------------------------------------------------------------
-- x86-32 Frame Preservation
--
-- On x86-32, the stack grows downward (toward lower addresses).
-- A frame is "preserved" when its base address is >= the current
-- stack pointer, meaning it's in the caller's region and won't be
-- clobbered by writes to the current stack frame.
------------------------------------------------------------------------

-- | Frame is preserved if frame address >= stack pointer
-- This means the frame is "above" the current stack (in caller's region)
X86-32FramePreserved : Addr → Addr → Set
X86-32FramePreserved frame stack-ptr = frame ≥ stack-ptr

-- | Stack grew if new stack pointer <= old stack pointer
-- (stack pointer decreased, stack expanded downward)
X86-32StackGrew : Addr → Addr → Set
X86-32StackGrew old-sp new-sp = new-sp ≤ old-sp

-- | Preserved frames stay preserved when stack grows
-- If frame >= old-sp and new-sp <= old-sp, then frame >= new-sp
x86-32-frame-preserved-under-growth : ∀ frame old-sp new-sp →
  X86-32FramePreserved frame old-sp →
  X86-32StackGrew old-sp new-sp →
  X86-32FramePreserved frame new-sp
x86-32-frame-preserved-under-growth frame old-sp new-sp fp sg = ≤-trans sg fp

-- | Slots in a preserved frame are also preserved
-- If frame >= sp, then (frame + k * 4) >= sp
x86-32-slot-in-preserved-frame : ∀ frame k sp →
  X86-32FramePreserved frame sp →
  X86-32FramePreserved (x86-32-grow frame k) sp
x86-32-slot-in-preserved-frame frame k sp fp = ≤-trans fp (m≤m+n frame (k * word-size))

------------------------------------------------------------------------
-- x86-32 StackGrowth Instance
------------------------------------------------------------------------

x86-32-stack-growth : StackGrowth
x86-32-stack-growth = record
  { grow = x86-32-grow
  ; grow-identity = x86-32-grow-identity
  ; grow-injective = x86-32-grow-injective
  ; grow-addr-injective = x86-32-grow-addr-injective
  ; FramePreserved = X86-32FramePreserved
  ; StackGrew = X86-32StackGrew
  ; frame-preserved-under-growth = x86-32-frame-preserved-under-growth
  ; slot-in-preserved-frame = x86-32-slot-in-preserved-frame
  }