-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Layout
--
-- Concrete x86-32 memory layout.
--
-- This module provides:
--   - x86-32-layout : MemoryLayout (constructed from RuntimeContract)
--   - Re-exports Common modules instantiated with x86-32 values
--
-- Runtime assumptions are provided via RuntimeParams.agda
--
-- IR proofs should NOT import this directly - they should use
-- Common.Regions, Common.StackSlots, etc. Only the top-level
-- Correct module imports this for concrete wiring.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Layout where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; <-≤-trans; m<m+n; m∸n≤m)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import types for layout construction
open import Once.Memory.MemoryLayoutSemantics as MLS
  using (MemoryLayout; RegionBounds; lower; upper; InRegion)
open MLS using (Addr; lower; upper) public

-- Import RuntimeContract and the X86-32 instance
open import Once.Memory.RuntimeContract as RC using (RuntimeContract)
import Once.CCC.Target.X86-32.RuntimeParams as RP

-- Import and re-export x86-32 stack growth
open import Once.CCC.Target.X86-32.StackGrowth public
  using (word-size; x86-32-stack-growth)

-- Re-export stack layout constants from IR.Stack
open import Once.CCC.IR.Stack public
  using (pair-slots; closure-slots)

------------------------------------------------------------------------
-- x86-32 Concrete Memory Layout
--
-- Constructed from RuntimeContract (memory bounds + region guarantees)
--
-- KEY INSIGHT: By defining bounds with lower = 0, properties become
-- definitional (refl) instead of requiring proofs.
------------------------------------------------------------------------

-- Region bounds from RuntimeContract
x86-32-stack-bounds : RegionBounds
x86-32-stack-bounds = RC.stack-bounds RP.x86-32-runtime

x86-32-heap-bounds : RegionBounds
x86-32-heap-bounds = RC.heap-bounds RP.x86-32-runtime

x86-32-code-bounds : RegionBounds
x86-32-code-bounds = RC.code-bounds RP.x86-32-runtime

-- x86-32 Memory Layout instance (constructed from RuntimeContract)
x86-32-layout : MemoryLayout
x86-32-layout = record
  { stack-bounds = x86-32-stack-bounds
  ; heap-bounds = x86-32-heap-bounds
  ; code-bounds = x86-32-code-bounds
  ; intervals-disjoint = RC.intervals-disjoint RP.x86-32-runtime
  }

------------------------------------------------------------------------
-- Re-export Common modules instantiated with x86-32 layout
------------------------------------------------------------------------

-- Regions (InStack, InHeap, InCode, disjointness)
-- Hide Addr since we already export it from MLS above
open import Once.Memory.Regions x86-32-layout public
  hiding (Addr)

-- Stack slots (slot-addr, StackPointer, etc.)
-- Hide InStack since it's already exported from Regions
open import Once.Memory.StackSlots x86-32-layout x86-32-stack-growth public
  hiding (InStack)

-- Frame operations (frameSlot, memory preservation)
open import Once.Memory.FrameOps x86-32-layout x86-32-stack-growth public


-- Re-export Memory operations
open import Once.Memory.Memory using (Memory; Word; readMem; writeMem) public

------------------------------------------------------------------------
-- x86-32-Specific Properties (lower = 0 is definitional)
------------------------------------------------------------------------

-- | x86-32 stack region has lower bound 0
-- Definitional from RuntimeContract's stack-bounds
x86-32-stack-lower-zero : lower stack-bounds ≡ 0
x86-32-stack-lower-zero = refl

-- | x86-32 code region has lower bound 0
-- Definitional from RuntimeContract's code-bounds
x86-32-code-lower-zero : lower code-bounds ≡ 0
x86-32-code-lower-zero = refl

-- | Program fits in code region (from RuntimeContract)
prog-fits-in-code : ∀ (prog-len : ℕ) → prog-len ≤ upper code-bounds
prog-fits-in-code = RC.prog-fits RP.x86-32-runtime

-- | Valid program counter is in code region
pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) →
  pc < prog-len →
  InCode pc
pc-in-code pc prog-len pc<prog-len = (z≤n , pc≤upper)
  where
    open import Data.Nat.Properties using (<⇒≤)
    pc≤upper : pc ≤ upper code-bounds
    pc≤upper = ≤-trans (<⇒≤ pc<prog-len) (prog-fits-in-code prog-len)

------------------------------------------------------------------------
-- Stack Subtraction (uses lower = 0)
------------------------------------------------------------------------

-- | Subtracting from a stack address preserves stack membership
stack-sub-preserves : ∀ a k →
  InStack a →
  k ≤ a →
  InStack (a ∸ k)
stack-sub-preserves a k (lower≤a , a≤upper) k≤a = (z≤n , a∸k≤upper)
  where
    a∸k≤upper : a ∸ k ≤ upper stack-bounds
    a∸k≤upper = ≤-trans (m∸n≤m a k) a≤upper

-- | Unconditional form (the `k ≤ a` premise above is unused — `lower = 0` and
-- `a ∸ k ≤ a`). Needed to move a FRAME down the stack (`shift-frame`).
stack-sub-preserves' : ∀ a k → InStack a → InStack (a ∸ k)
stack-sub-preserves' a k (lower≤a , a≤upper) = (z≤n , ≤-trans (m∸n≤m a k) a≤upper)

------------------------------------------------------------------------
-- x86-32-Specific Slot Addressing Lemmas
--
-- These lemmas depend on x86-32's upward stack growth direction.
------------------------------------------------------------------------

-- | Slot address is always ≥ base address (grows upward)
slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp
slot-addr-≥-base sp k = m≤m+n (addr sp) (k * word-size)

-- | Slot 1 is word-size bytes above base (x86-32-specific)
slot-addr-next-is-base-plus-word : ∀ sp → slot-addr sp 1 ≡ addr sp + word-size
slot-addr-next-is-base-plus-word sp = refl

------------------------------------------------------------------------
-- Frame Ordering Implies Slot Disjointness
------------------------------------------------------------------------

-- | When frame1 < frame2, slot 0 of frame1 is below any slot of frame2
frame-below-slot0-disjoint : ∀ (frame1 frame2 : StackPointer) k →
  addr frame1 < addr frame2 →
  slot-addr frame1 0 ≢ slot-addr frame2 k
frame-below-slot0-disjoint frame1 frame2 k frame1<frame2 eq =
  Data.Nat.Properties.<⇒≢ slot0<slot-k slot0≡slot-k
  where
    open import Data.Nat.Properties using (<⇒≢)
    slot0-eq : slot-addr frame1 0 ≡ addr frame1
    slot0-eq = grow-identity (addr frame1)

    slot-k-≥-frame2 : slot-addr frame2 k ≥ addr frame2
    slot-k-≥-frame2 = slot-addr-≥-base frame2 k

    slot0<slot-k : slot-addr frame1 0 < slot-addr frame2 k
    slot0<slot-k = subst (_< slot-addr frame2 k) (sym slot0-eq)
                         (<-≤-trans frame1<frame2 slot-k-≥-frame2)

    slot0≡slot-k : slot-addr frame1 0 ≡ slot-addr frame2 k
    slot0≡slot-k = eq

-- | When frame1 + word-size ≤ frame2, slot 0 of frame1 ≠ any slot of frame2
frame-preserved-slot0-disjoint : ∀ (frame1 frame2 : StackPointer) k →
  addr frame1 + word-size ≤ addr frame2 →
  slot-addr frame1 0 ≢ slot-addr frame2 k
frame-preserved-slot0-disjoint frame1 frame2 k frame1+4≤frame2 =
  frame-below-slot0-disjoint frame1 frame2 k frame1<frame2
  where
    word-size>0 : word-size > 0
    word-size>0 = s≤s z≤n

    frame1<frame1+4 : addr frame1 < addr frame1 + word-size
    frame1<frame1+4 = m<m+n (addr frame1) word-size>0

    frame1<frame2 : addr frame1 < addr frame2
    frame1<frame2 = <-≤-trans frame1<frame1+4 frame1+4≤frame2

------------------------------------------------------------------------
-- x86-32-Specific Calling Convention Lemmas
------------------------------------------------------------------------

-- | Slot address is above thunk's ebp
slot-addr-above-thunk-ebp : ∀ sp k esp thunk-ebp →
  addr sp ≡ esp + 4 →
  thunk-ebp ≡ esp ∸ 8 →
  esp > 8 →
  slot-addr sp k > thunk-ebp
slot-addr-above-thunk-ebp sp k esp thunk-ebp addr-eq ebp-eq esp>8 = slot>ebp
  where
    open import Data.Nat.Properties using (≤-<-trans)

    slot-eq : slot-addr sp k ≡ (esp + 4) + k * word-size
    slot-eq = cong (λ a → a + k * word-size) addr-eq

    slot≥esp+4 : slot-addr sp k ≥ esp + 4
    slot≥esp+4 = subst (_≥ esp + 4) (sym slot-eq) (m≤m+n (esp + 4) (k * word-size))

    esp+4>esp : esp + 4 > esp
    esp+4>esp = m<m+n esp (s≤s z≤n)

    ebp≤esp : thunk-ebp ≤ esp
    ebp≤esp = subst (_≤ esp) (sym ebp-eq) (m∸n≤m esp 8)

    slot>ebp : slot-addr sp k > thunk-ebp
    slot>ebp = ≤-<-trans ebp≤esp (<-≤-trans esp+4>esp slot≥esp+4)

------------------------------------------------------------------------
-- Re-export FrameSlotInternal at top level
------------------------------------------------------------------------

-- | frameSlot at slot 0 reads from the stack pointer address
init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
init-frame-slot-at-base = FrameSlotInternal.init-frame-slot-at-base