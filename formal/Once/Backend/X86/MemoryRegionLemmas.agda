------------------------------------------------------------------------
-- Once.Backend.X86.MemoryRegionLemmas
--
-- X86-64 specific memory region lemmas.
-- Re-exports Common.MemoryRegionLemmas instantiated with x86 stack growth,
-- and adds x86-specific lemmas.
------------------------------------------------------------------------

module Once.Backend.X86.MemoryRegionLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; +-comm)
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
-- Backwards Compatibility Aliases
--
-- These provide the old names for gradual migration.
-- TODO: Remove after all usages are updated.
------------------------------------------------------------------------

-- | Old name for init-slot-at-base
slot-addr-0-is-base : ∀ sp → slot-addr sp zero ≡ addr sp
slot-addr-0-is-base = init-slot-at-base

-- | Old name for slot-addr-next-is-base-plus-word
slot-addr-1-is-base+8 : ∀ sp → slot-addr sp 1 ≡ addr sp + 8
slot-addr-1-is-base+8 = slot-addr-next-is-base-plus-word

------------------------------------------------------------------------
-- FrameSlot Compatibility
--
-- The FrameSlotInternal module is re-exported from Common.MemoryRegionLemmas.
-- We add the old name alias here at the top level.
------------------------------------------------------------------------

-- Old name alias for backwards compatibility
frameSlot-0-is-top : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
frameSlot-0-is-top = FrameSlotInternal.init-frame-slot-at-base
