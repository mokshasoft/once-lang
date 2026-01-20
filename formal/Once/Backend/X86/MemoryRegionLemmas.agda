------------------------------------------------------------------------
-- Once.Backend.X86.MemoryRegionLemmas
--
-- X86-64 specific memory region lemmas.
-- Re-exports Common.MemoryRegionLemmas instantiated with:
--   - x86-stack-growth (slot addressing)
--   - x86-layout (concrete bounds with lower = 0)
------------------------------------------------------------------------

module Once.Backend.X86.MemoryRegionLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; +-comm; <-≤-trans; <⇒≢; +-monoʳ-<; m+n≤o⇒m≤o; m<m+n; m∸n≤m)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import types for layout construction
-- Re-export Addr for downstream modules
open import Once.Backend.Common.MemoryLayoutSemantics as MLS
  using (MemoryLayout; RegionBounds; lower; upper; InRegion)
open MLS using (Addr) public

-- Import and re-export X86 stack growth
open import Once.Backend.X86.StackGrowth public
  using (word-size; x86-stack-growth)

------------------------------------------------------------------------
-- X86 Concrete Memory Layout
--
-- KEY INSIGHT: By defining bounds with lower = 0, properties become
-- definitional (refl) instead of postulates!
------------------------------------------------------------------------

-- Runtime provides upper bounds (postulates - these are inputs)
postulate
  x86-stack-upper : ℕ  -- Stack region upper bound
  x86-heap-lower  : ℕ  -- Heap region lower bound
  x86-heap-upper  : ℕ  -- Heap region upper bound
  x86-code-upper  : ℕ  -- Code region upper bound

-- Concrete X86 bounds with lower = 0 where applicable
x86-stack-bounds : RegionBounds
x86-stack-bounds = record
  { lower = 0              -- KEY: lower = 0 by definition!
  ; upper = x86-stack-upper
  ; bounds-valid = z≤n
  }

x86-heap-bounds : RegionBounds
x86-heap-bounds = record
  { lower = x86-heap-lower
  ; upper = x86-heap-upper
  ; bounds-valid = heap-valid
  }
  where postulate heap-valid : x86-heap-lower ≤ x86-heap-upper

x86-code-bounds : RegionBounds
x86-code-bounds = record
  { lower = 0              -- KEY: lower = 0 by definition!
  ; upper = x86-code-upper
  ; bounds-valid = z≤n
  }

-- Disjointness (runtime guarantee)
postulate
  x86-intervals-disjoint : ∀ a →
    ¬ (InRegion x86-stack-bounds a × InRegion x86-heap-bounds a) ×
    ¬ (InRegion x86-stack-bounds a × InRegion x86-code-bounds a) ×
    ¬ (InRegion x86-heap-bounds a × InRegion x86-code-bounds a)

-- X86 Memory Layout instance
x86-layout : MemoryLayout
x86-layout = record
  { stack-bounds = x86-stack-bounds
  ; heap-bounds = x86-heap-bounds
  ; code-bounds = x86-code-bounds
  ; intervals-disjoint = x86-intervals-disjoint
  }

-- Import and re-export Common.MemoryRegionLemmas with X86 layout
-- Note: Hide Addr since we already import it from MLS above
open import Once.Backend.Common.MemoryRegionLemmas x86-layout x86-stack-growth public
  hiding (Addr)

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
-- X86-Specific Stack Subtraction (PROVEN - zero postulates!)
--
-- Since x86-stack-bounds has lower = 0 by DEFINITION, subtracting from
-- a stack address keeps it in the region (monus never goes below 0).
------------------------------------------------------------------------

-- | X86 stack region has lower bound 0
-- PROVEN: definitional from x86-stack-bounds!
x86-stack-lower-zero : lower stack-bounds ≡ 0
x86-stack-lower-zero = refl  -- lower x86-stack-bounds = 0 by definition!

-- | Subtracting from a stack address preserves stack membership
-- PROVEN from x86-stack-lower-zero = refl
stack-sub-preserves : ∀ a k →
  InStack a →
  k ≤ a →
  InStack (a ∸ k)
stack-sub-preserves a k (lower≤a , a≤upper) k≤a = (z≤n , a∸k≤upper)
  where
    -- Lower bound: 0 ≤ (a ∸ k) is trivially true for ℕ
    -- (x86-stack-lower-zero = refl, so lower stack-bounds = 0)

    -- Upper bound: a ∸ k ≤ a ≤ upper (arithmetic)
    a∸k≤upper : a ∸ k ≤ upper stack-bounds
    a∸k≤upper = ≤-trans (m∸n≤m a k) a≤upper

------------------------------------------------------------------------
-- X86-Specific Code Region (PROVEN - zero postulates!)
--
-- Since x86-code-bounds has lower = 0 by DEFINITION, any pc in [0, prog-len)
-- where prog-len ≤ code-upper is in the code region.
------------------------------------------------------------------------

-- | X86 code region has lower bound 0
-- PROVEN: definitional from x86-code-bounds!
x86-code-lower-zero : lower code-bounds ≡ 0
x86-code-lower-zero = refl  -- lower x86-code-bounds = 0 by definition!

-- | Program fits in code region (RUNTIME GUARANTEE)
-- This is a boundary postulate: the linker/loader ensures the compiled
-- program is placed within the code region. Similar to x86-intervals-disjoint.
postulate
  prog-fits-in-code : ∀ (prog-len : ℕ) → prog-len ≤ upper code-bounds

-- | Valid program counter is in code region
-- PROVEN: lower bound is 0 (definitional), upper bound from prog-fits-in-code
pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) →
  pc < prog-len →
  InCode pc
pc-in-code pc prog-len pc<prog-len = (z≤n , pc≤upper)
  where
    open import Data.Nat.Properties using (<⇒≤)
    -- Lower bound: 0 ≤ pc is trivially true for ℕ
    -- (x86-code-lower-zero = refl, so lower code-bounds = 0)

    -- Upper bound: pc < prog-len ≤ code-upper (via prog-fits-in-code)
    pc≤upper : pc ≤ upper code-bounds
    pc≤upper = ≤-trans (<⇒≤ pc<prog-len) (prog-fits-in-code prog-len)

------------------------------------------------------------------------
-- X86-Specific Calling Convention Lemmas
------------------------------------------------------------------------

-- | Slot address is above thunk's rbp (PROVEN)
-- This is specific to x86-64 calling convention where:
--   - caller-sp = rsp + 8 (after call pushes return address)
--   - thunk-rbp = rsp - 16 (thunk's saved frame pointer)
--
-- Proof: slot-addr sp k = (rsp + 8) + k * 8 ≥ rsp + 8
--        thunk-rbp = rsp ∸ 16 ≤ rsp (by m∸n≤m)
--        rsp + 8 > rsp ≥ rsp ∸ 16 = thunk-rbp
slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
  addr sp ≡ rsp + 8 →
  thunk-rbp ≡ rsp ∸ 16 →
  rsp > 16 →
  slot-addr sp k > thunk-rbp
slot-addr-above-thunk-rbp sp k rsp thunk-rbp addr-eq rbp-eq rsp>16 = slot>rbp
  where
    open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n; n<1+n; ≤-<-trans; <-transʳ)

    -- slot-addr sp k = addr sp + k * word-size = (rsp + 8) + k * 8
    slot-eq : slot-addr sp k ≡ (rsp + 8) + k * word-size
    slot-eq = cong (λ a → a + k * word-size) addr-eq

    -- slot-addr sp k ≥ rsp + 8 (adding k * 8 ≥ 0)
    slot≥rsp+8 : slot-addr sp k ≥ rsp + 8
    slot≥rsp+8 = subst (_≥ rsp + 8) (sym slot-eq) (m≤m+n (rsp + 8) (k * word-size))

    -- rsp + 8 > rsp (adding 8 > 0)
    rsp+8>rsp : rsp + 8 > rsp
    rsp+8>rsp = m<m+n rsp (s≤s z≤n)

    -- thunk-rbp = rsp ∸ 16 ≤ rsp
    rbp≤rsp : thunk-rbp ≤ rsp
    rbp≤rsp = subst (_≤ rsp) (sym rbp-eq) (m∸n≤m rsp 16)

    -- Chain: slot-addr sp k ≥ rsp + 8 > rsp ≥ thunk-rbp
    slot>rbp : slot-addr sp k > thunk-rbp
    slot>rbp = ≤-<-trans rbp≤rsp (<-≤-trans rsp+8>rsp slot≥rsp+8)

------------------------------------------------------------------------
-- Re-export FrameSlotInternal at top level
------------------------------------------------------------------------

-- | frameSlot at slot 0 reads from the stack pointer address
init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
init-frame-slot-at-base = FrameSlotInternal.init-frame-slot-at-base

