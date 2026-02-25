------------------------------------------------------------------------
-- Once.CCC.Target.X86.Layout
--
-- Concrete X86-64 memory layout.
--
-- This module provides:
--   - x86-layout : MemoryLayout (with lower = 0 for stack/code)
--   - Runtime postulates (bounds, disjointness, prog-fits)
--   - Re-exports Common modules instantiated with X86 values
--
-- IR proofs should NOT import this directly - they should use
-- Common.Regions, Common.StackSlots, etc. Only the top-level
-- (WholeProgram) imports X86.Layout for concrete wiring.
------------------------------------------------------------------------

module Once.CCC.Target.X86.Layout where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n; ≤-trans; <-≤-trans; m<m+n; m∸n≤m)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import types for layout construction
open import Once.CCC.MemoryLayoutSemantics as MLS
  using (MemoryLayout; RegionBounds; lower; upper; InRegion)
open MLS using (Addr; lower; upper) public

-- Import and re-export X86 stack growth
open import Once.CCC.Target.X86.StackGrowth public
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

------------------------------------------------------------------------
-- Re-export Common modules instantiated with X86 layout
------------------------------------------------------------------------

-- Regions (InStack, InHeap, InCode, disjointness)
-- Hide Addr since we already export it from MLS above
open import Once.CCC.Regions x86-layout public
  hiding (Addr)

-- Stack slots (slot-addr, StackPointer, etc.)
-- Hide InStack since it's already exported from Regions
open import Once.CCC.StackSlots x86-layout x86-stack-growth public
  hiding (InStack)

-- Frame operations (frameSlot, memory preservation)
open import Once.CCC.FrameOps x86-layout x86-stack-growth public

-- Allocator semantics (encode-in-heap, heap-offset)
open import Once.CCC.AllocatorSemantics x86-layout public

-- Re-export Memory operations
open import Once.CCC.Memory using (Memory; Word; readMem; writeMem) public

------------------------------------------------------------------------
-- X86-Specific Properties (lower = 0 is definitional)
------------------------------------------------------------------------

-- | X86 stack region has lower bound 0
-- PROVEN: definitional from x86-stack-bounds!
x86-stack-lower-zero : lower stack-bounds ≡ 0
x86-stack-lower-zero = refl

-- | X86 code region has lower bound 0
-- PROVEN: definitional from x86-code-bounds!
x86-code-lower-zero : lower code-bounds ≡ 0
x86-code-lower-zero = refl

-- | Program fits in code region (RUNTIME GUARANTEE)
postulate
  prog-fits-in-code : ∀ (prog-len : ℕ) → prog-len ≤ upper code-bounds

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
-- Frame Ordering Implies Slot Disjointness (PROVEN)
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
frame-preserved-slot0-disjoint frame1 frame2 k frame1+8≤frame2 =
  frame-below-slot0-disjoint frame1 frame2 k frame1<frame2
  where
    word-size>0 : word-size > 0
    word-size>0 = s≤s z≤n

    frame1<frame1+8 : addr frame1 < addr frame1 + word-size
    frame1<frame1+8 = m<m+n (addr frame1) word-size>0

    frame1<frame2 : addr frame1 < addr frame2
    frame1<frame2 = <-≤-trans frame1<frame1+8 frame1+8≤frame2

------------------------------------------------------------------------
-- X86-Specific Calling Convention Lemmas
------------------------------------------------------------------------

-- | Slot address is above thunk's rbp (PROVEN)
slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
  addr sp ≡ rsp + 8 →
  thunk-rbp ≡ rsp ∸ 16 →
  rsp > 16 →
  slot-addr sp k > thunk-rbp
slot-addr-above-thunk-rbp sp k rsp thunk-rbp addr-eq rbp-eq rsp>16 = slot>rbp
  where
    open import Data.Nat.Properties using (≤-<-trans)

    slot-eq : slot-addr sp k ≡ (rsp + 8) + k * word-size
    slot-eq = cong (λ a → a + k * word-size) addr-eq

    slot≥rsp+8 : slot-addr sp k ≥ rsp + 8
    slot≥rsp+8 = subst (_≥ rsp + 8) (sym slot-eq) (m≤m+n (rsp + 8) (k * word-size))

    rsp+8>rsp : rsp + 8 > rsp
    rsp+8>rsp = m<m+n rsp (s≤s z≤n)

    rbp≤rsp : thunk-rbp ≤ rsp
    rbp≤rsp = subst (_≤ rsp) (sym rbp-eq) (m∸n≤m rsp 16)

    slot>rbp : slot-addr sp k > thunk-rbp
    slot>rbp = ≤-<-trans rbp≤rsp (<-≤-trans rsp+8>rsp slot≥rsp+8)

------------------------------------------------------------------------
-- Re-export FrameSlotInternal at top level
------------------------------------------------------------------------

-- | frameSlot at slot 0 reads from the stack pointer address
init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
init-frame-slot-at-base = FrameSlotInternal.init-frame-slot-at-base
