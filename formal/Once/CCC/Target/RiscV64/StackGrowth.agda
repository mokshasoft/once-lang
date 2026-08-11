-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.StackGrowth
--
-- RISC-V 64-bit stack growth implementation.
-- Provides the StackGrowth instance for RISC-V 64-bit architecture.
--
-- RISC-V 64 stack layout:
--   - Word size: 8 bytes
--   - Slot k is at: base + k * 8 (grows upward from base)
--   - Same as x86-64 (both are 64-bit with 8-byte words)
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.StackGrowth where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-comm; m≤m+n; +-cancelˡ-≡; *-cancelˡ-≡; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Level using (0ℓ)

open import Once.Memory.MemoryLayoutSemantics
  using (Addr; StackGrowth)

------------------------------------------------------------------------
-- RISC-V 64 Constants
------------------------------------------------------------------------

-- | Word size for RISC-V 64 (8 bytes)
word-size : ℕ
word-size = 8

------------------------------------------------------------------------
-- RISC-V 64 Stack Growth Function
------------------------------------------------------------------------

-- | Compute slot address: base + k * word-size
rv64-grow : Addr → ℕ → Addr
rv64-grow base k = base + k * word-size

------------------------------------------------------------------------
-- Proofs of StackGrowth Properties
------------------------------------------------------------------------

-- | Growing by zero is identity
rv64-grow-identity : ∀ a → rv64-grow a zero ≡ a
rv64-grow-identity a = +-identityʳ a

-- | Different offsets yield different addresses
-- Proof: a + k₁ * 8 = a + k₂ * 8 implies k₁ * 8 = k₂ * 8 implies k₁ = k₂
rv64-grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → rv64-grow a k₁ ≢ rv64-grow a k₂
rv64-grow-injective a k₁ k₂ k₁≢k₂ eq = k₁≢k₂ (cancel-*8 (+-cancelˡ-≡ a _ _ eq))
  where
    open import Data.Nat.Properties using (*-cancelʳ-≡)
    -- If k₁ * 8 = k₂ * 8, then k₁ = k₂ (cancel the 8 on the right)
    cancel-*8 : k₁ * word-size ≡ k₂ * word-size → k₁ ≡ k₂
    cancel-*8 eq' = *-cancelʳ-≡ k₁ k₂ word-size eq'

-- | Different base addresses yield different slot addresses (same offset)
-- Proof: a₁ + k * 8 = a₂ + k * 8 implies a₁ = a₂ (cancel the k * 8)
rv64-grow-addr-injective : ∀ a₁ a₂ k → a₁ ≢ a₂ → rv64-grow a₁ k ≢ rv64-grow a₂ k
rv64-grow-addr-injective a₁ a₂ k a₁≢a₂ eq = a₁≢a₂ (+-cancelʳ-≡ (k * word-size) a₁ a₂ eq)
  where
    open import Data.Nat.Properties using (+-cancelʳ-≡)

------------------------------------------------------------------------
-- RISC-V 64 Frame Preservation
--
-- On RISC-V 64, the stack grows downward (toward lower addresses).
-- A frame is "preserved" when its base address is >= the current
-- stack pointer, meaning it's in the caller's region and won't be
-- clobbered by writes to the current stack frame.
------------------------------------------------------------------------

-- | Frame is preserved if frame address >= stack pointer
-- This means the frame is "above" the current stack (in caller's region)
RV64FramePreserved : Addr → Addr → Set
RV64FramePreserved frame stack-ptr = frame ≥ stack-ptr

-- | Stack grew if new stack pointer <= old stack pointer
-- (stack pointer decreased, stack expanded downward)
RV64StackGrew : Addr → Addr → Set
RV64StackGrew old-sp new-sp = new-sp ≤ old-sp

-- | Preserved frames stay preserved when stack grows
-- If frame >= old-sp and new-sp <= old-sp, then frame >= new-sp
rv64-frame-preserved-under-growth : ∀ frame old-sp new-sp →
  RV64FramePreserved frame old-sp →
  RV64StackGrew old-sp new-sp →
  RV64FramePreserved frame new-sp
rv64-frame-preserved-under-growth frame old-sp new-sp fp sg = ≤-trans sg fp

-- | Slots in a preserved frame are also preserved
-- If frame >= sp, then (frame + k * 8) >= sp
rv64-slot-in-preserved-frame : ∀ frame k sp →
  RV64FramePreserved frame sp →
  RV64FramePreserved (rv64-grow frame k) sp
rv64-slot-in-preserved-frame frame k sp fp = ≤-trans fp (m≤m+n frame (k * word-size))

------------------------------------------------------------------------
-- RISC-V 64 StackGrowth Instance
------------------------------------------------------------------------

rv64-stack-growth : StackGrowth
rv64-stack-growth = record
  { grow = rv64-grow
  ; grow-identity = rv64-grow-identity
  ; grow-injective = rv64-grow-injective
  ; grow-addr-injective = rv64-grow-addr-injective
  ; FramePreserved = RV64FramePreserved
  ; StackGrew = RV64StackGrew
  ; frame-preserved-under-growth = rv64-frame-preserved-under-growth
  ; slot-in-preserved-frame = rv64-slot-in-preserved-frame
  }