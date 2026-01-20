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
-- Re-export FrameSlotInternal at top level
------------------------------------------------------------------------

-- | frameSlot at slot 0 reads from the stack pointer address
init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
init-frame-slot-at-base = FrameSlotInternal.init-frame-slot-at-base

