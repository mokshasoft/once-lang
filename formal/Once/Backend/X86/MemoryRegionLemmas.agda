------------------------------------------------------------------------
-- Once.Backend.X86.MemoryRegionLemmas
--
-- X86-64 specific memory region lemmas.
-- Re-exports Common.MemoryRegionLemmas instantiated with x86 stack growth,
-- and adds x86-specific lemmas.
------------------------------------------------------------------------

module Once.Backend.X86.MemoryRegionLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_; s≤s)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; +-comm; <-≤-trans; <⇒≢; +-monoʳ-<; m+n≤o⇒m≤o; m<m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import and re-export X86 stack growth
open import Once.Backend.X86.StackGrowth public
  using (word-size; x86-stack-growth)

-- Import and re-export Common.MemoryRegionLemmas instantiated with x86 stack growth
open import Once.Backend.Common.MemoryRegionLemmas x86-stack-growth public

------------------------------------------------------------------------
-- X86-Specific Slot Addressing Lemmas
--
-- These lemmas depend on x86's upward stack growth direction.
------------------------------------------------------------------------

-- | Slot address is always ≥ base address (x86 grows upward)
slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp
slot-addr-≥-base sp k = m≤m+n (addr sp) (k * word-size)

-- | Slot 1 is word-size bytes above base (x86-specific)
slot-addr-next-is-base-plus-word : ∀ sp → slot-addr sp 1 ≡ addr sp + word-size
slot-addr-next-is-base-plus-word sp = refl

------------------------------------------------------------------------
-- Frame Ordering Implies Slot Disjointness (PROVEN, not postulated!)
--
-- Key insight: For x86, slot_addr sp k = addr sp + k * word-size.
-- If frame2 > frame1 (strict ordering), then:
--   slot_addr frame1 0 = addr frame1
--   slot_addr frame2 k = addr frame2 + k * 8 ≥ addr frame2 > addr frame1
--
-- So slot 0 of the lower frame is strictly below ALL slots of higher frame.
------------------------------------------------------------------------

-- | When frame1 < frame2, slot 0 of frame1 is below any slot of frame2
-- This replaces the need for frames-disjoint-slots postulate!
frame-below-slot0-disjoint : ∀ (frame1 frame2 : StackPointer) k →
  addr frame1 < addr frame2 →
  slot-addr frame1 0 ≢ slot-addr frame2 k
frame-below-slot0-disjoint frame1 frame2 k frame1<frame2 eq = <⇒≢ slot0<slot-k slot0≡slot-k
  where
    -- slot-addr frame1 0 = addr frame1 (from grow-identity)
    -- slot-addr frame2 k = addr frame2 + k * word-size ≥ addr frame2 > addr frame1
    slot0-eq : slot-addr frame1 0 ≡ addr frame1
    slot0-eq = grow-identity (addr frame1)

    slot-k-≥-frame2 : slot-addr frame2 k ≥ addr frame2
    slot-k-≥-frame2 = slot-addr-≥-base frame2 k

    slot0<slot-k : slot-addr frame1 0 < slot-addr frame2 k
    slot0<slot-k = subst (_< slot-addr frame2 k) (sym slot0-eq)
                         (<-≤-trans frame1<frame2 slot-k-≥-frame2)

    slot0≡slot-k : slot-addr frame1 0 ≡ slot-addr frame2 k
    slot0≡slot-k = eq

-- | Generalization: when frame1 + word-size ≤ frame2, slot 0 of frame1 ≠ any slot of frame2
-- This handles the FramePreserved case where we have ≤ rather than <
frame-preserved-slot0-disjoint : ∀ (frame1 frame2 : StackPointer) k →
  addr frame1 + word-size ≤ addr frame2 →
  slot-addr frame1 0 ≢ slot-addr frame2 k
frame-preserved-slot0-disjoint frame1 frame2 k frame1+8≤frame2 =
  frame-below-slot0-disjoint frame1 frame2 k frame1<frame2
  where
    -- addr frame1 < addr frame1 + word-size ≤ addr frame2
    -- word-size = 8 > 0
    word-size>0 : word-size > 0
    word-size>0 = s≤s (Data.Nat.z≤n)
      where open import Data.Nat using (z≤n)

    frame1<frame1+8 : addr frame1 < addr frame1 + word-size
    frame1<frame1+8 = m<m+n (addr frame1) word-size>0

    frame1<frame2 : addr frame1 < addr frame2
    frame1<frame2 = <-≤-trans frame1<frame1+8 frame1+8≤frame2

------------------------------------------------------------------------
-- X86-Specific Calling Convention Lemmas
------------------------------------------------------------------------

-- | Slot address is above thunk's rbp
-- This is specific to x86-64 calling convention where:
--   - caller-sp = rsp + 8 (after call pushes return address)
--   - thunk-rbp = rsp - 16 (thunk's saved frame pointer)
postulate
  slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
    addr sp ≡ rsp + 8 →
    thunk-rbp ≡ rsp ∸ 16 →
    rsp > 16 →
    slot-addr sp k > thunk-rbp

------------------------------------------------------------------------
-- Re-export FrameSlotInternal at top level
------------------------------------------------------------------------

-- | frameSlot at slot 0 reads from the stack pointer address
init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
init-frame-slot-at-base = FrameSlotInternal.init-frame-slot-at-base

