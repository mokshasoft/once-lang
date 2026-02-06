------------------------------------------------------------------------
-- Once.Backend.Common.FrameSemantics
--
-- Architecture-independent calling convention semantics (Adjacency-Based).
--
-- This module defines the contract for stack frame ownership using
-- EXACT SLOT OFFSETS, not inequality predicates. This ensures:
--   1. Tight memory layout with no gaps
--   2. Each address is at a specific slot in a specific frame
--   3. Disjointness follows from frame ordering
--
-- Key insight: At function entry, frames are separated by exact offsets.
-- Callee's frame starts at a known offset from caller's frame. Slots
-- within each frame are at exact offsets from frame base. This is stronger
-- than inequality-based disjointness (addr ≥ rsp) which allows gaps.
--
-- Architecture instantiation:
--   - X86-64: slots grow upward from frame base (frame base is at lower addr)
--   - Other archs: define slot-addr and frame ordering per their growth
--
-- See: Once.Backend.X86.FrameInstantiation for X86-64 implementation
------------------------------------------------------------------------

module Once.Backend.Common.FrameSemantics where

open import Data.Nat using (ℕ; zero)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- Import Addr from MemoryLayoutSemantics
open import Once.Backend.Common.MemoryLayoutSemantics using (Addr)

------------------------------------------------------------------------
-- FrameSemantics Interface (Adjacency-Based)
--
-- Stack frames are addressed via exact slot offsets, not inequalities.
--
-- The key abstraction:
--   - Frame: identity of a stack frame
--   - slot-addr f k: exact address of slot k in frame f
--   - _≺_: frame ordering (callee "further" than caller)
--   - frame-disjoint: ordered frames have disjoint slots
------------------------------------------------------------------------

record FrameSemantics : Set₁ where
  field
    --------------------------------------------------------------------
    -- Frame Type
    --
    -- Represents a stack frame. Each frame has a base address and
    -- slots at exact offsets from that base. The frame identity
    -- abstracts away the specific address.
    --------------------------------------------------------------------

    Frame : Set

    -- | Frame base address (stack pointer at frame creation)
    frame-base : Frame → Addr

    --------------------------------------------------------------------
    -- Slot Addressing (Exact Offsets)
    --
    -- slot-addr f k gives the address of slot k in frame f.
    -- This is an exact offset, not a range or inequality.
    --
    -- Architecture instantiations compute this via their growth
    -- direction (x86: base + k, upward: base - k).
    --------------------------------------------------------------------

    -- | Address of slot k in frame f
    slot-addr : Frame → ℕ → Addr

    -- | Slot 0 is at the frame base
    slot-zero-at-base : ∀ f → slot-addr f zero ≡ frame-base f

    -- | Different slots in same frame have different addresses
    slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → slot-addr f k₁ ≢ slot-addr f k₂

    --------------------------------------------------------------------
    -- Frame Ordering
    --
    -- Callee's frame is "further" than caller's in growth direction.
    -- This ordering is abstract: each architecture defines what
    -- "further" means based on its stack growth direction.
    --
    -- X86-64: f₁ ≺ f₂ means base(f₁) < base(f₂) (callee at lower addr)
    -- Stack-grows-up: f₁ ≺ f₂ means base(f₁) > base(f₂)
    --------------------------------------------------------------------

    -- | Frame ordering: f₁ ≺ f₂ means f₁ is "further" in growth direction
    _≺_ : Frame → Frame → Set

    --------------------------------------------------------------------
    -- Frame Disjointness (Key Property)
    --
    -- Slots in ordered frames don't overlap. This is THE core
    -- property enabling caller/callee isolation.
    --
    -- If callee's frame is further than caller's (callee ≺ caller),
    -- then no slot in callee's frame can equal any slot in caller's.
    --
    -- This is STRONGER than inequality-based disjointness:
    --   - Inequality: "all addresses ≥ boundary are disjoint from < boundary"
    --   - Slots: "address at slot k in frame f₁ ≢ address at slot j in frame f₂"
    --
    -- The slot-based property proves tight layout with no wasted space.
    --------------------------------------------------------------------

    -- | Slots in ordered frames are disjoint
    frame-disjoint : ∀ f₁ f₂ k₁ k₂ → f₁ ≺ f₂ → slot-addr f₁ k₁ ≢ slot-addr f₂ k₂

open FrameSemantics public

------------------------------------------------------------------------
-- AtSlot: Address is at specific slot in specific frame
--
-- This is the core predicate for ownership: proving an address is
-- at exact slot k in frame f establishes its exact position.
------------------------------------------------------------------------

AtSlot : (fs : FrameSemantics) → Addr → Frame fs → ℕ → Set
AtSlot fs addr f k = addr ≡ slot-addr fs f k

------------------------------------------------------------------------
-- InFrame: Address is somewhere in frame (existential)
--
-- Weaker predicate: address is some slot in the frame.
-- Useful when the specific slot is not needed.
------------------------------------------------------------------------

InFrame : (fs : FrameSemantics) → Addr → Frame fs → Set
InFrame fs addr f = Σ ℕ (λ k → AtSlot fs addr f k)

------------------------------------------------------------------------
-- Derived Properties
------------------------------------------------------------------------

-- | If addresses are in ordered frames, they're distinct
in-frame-disjoint : ∀ (fs : FrameSemantics) (f₁ f₂ : Frame fs) (addr : Addr) →
  _≺_ fs f₁ f₂ →
  InFrame fs addr f₁ →
  InFrame fs addr f₂ →
  ⊥
in-frame-disjoint fs f₁ f₂ addr f₁≺f₂ (k₁ , eq₁) (k₂ , eq₂) =
  frame-disjoint fs f₁ f₂ k₁ k₂ f₁≺f₂ (Relation.Binary.PropositionalEquality.trans
    (Relation.Binary.PropositionalEquality.sym eq₁) eq₂)
  where open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Caller/Callee Frame Relationship
--
-- In a function call:
--   - caller-frame: caller's stack frame (before the call)
--   - callee-frame: callee's stack frame (after sub sp, N)
--
-- The relationship is: callee-frame ≺ caller-frame
-- (callee is "further" in growth direction)
--
-- This means all of callee's slots are disjoint from caller's slots,
-- so callee's stack operations don't affect caller's data.
------------------------------------------------------------------------

-- | Caller's slot is preserved when callee writes to its own frame
caller-slot-preserved : ∀ (fs : FrameSemantics)
  (caller-frame callee-frame : Frame fs)
  (caller-slot callee-slot : ℕ) →
  _≺_ fs callee-frame caller-frame →
  slot-addr fs callee-frame callee-slot ≢ slot-addr fs caller-frame caller-slot
caller-slot-preserved fs caller callee k₁ k₂ callee≺caller =
  frame-disjoint fs callee caller k₂ k₁ callee≺caller
