-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.FrameSemantics
--
-- Architecture-independent calling convention semantics (Adjacency-Based).
--
-- This module defines the contract for stack frame ownership using
-- EXACT SLOT OFFSETS, not inequality predicates. This ensures:
--   1. Tight memory layout with no gaps
--   2. Each address is at a specific slot in a specific frame
--   3. Disjointness follows from frame ordering + capacity bounds
--
-- Key insight: At function entry, frames are separated by exact offsets.
-- Callee's frame starts at a known offset from caller's frame. Slots
-- within each frame are at exact offsets from frame base.
--
-- BOUNDED DISJOINTNESS:
--   The key property is BOUNDED frame-disjoint: slots within the frame's
--   capacity are disjoint from the next frame's slots. This is provable
--   for any architecture because:
--     - Slots grow in a known direction from frame base
--     - Capacity bounds ensure slots stay within the gap to next frame
--     - Pure arithmetic
--
-- Architecture instantiation:
--   - X86-64: slots grow upward from frame base (frame base is at lower addr)
--   - Other archs: define slot-addr and frame ordering per their growth
--
-- See: Once.CCC.Target.X86.FrameInstantiation for X86-64 implementation
------------------------------------------------------------------------

module Once.CCC.FrameSemantics where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _∸_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (*-mono-≤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (Dec)

-- Import Addr from MemoryLayoutSemantics
open import Once.Memory.MemoryLayoutSemantics using (Addr)

-- Plan 0.73 (D113): the target's FLOAT FORMAT is a target fact of exactly the
-- kind this record already collects (`frame-word` is the machine word), so it
-- joins them rather than getting a second mechanism of its own.
open import Once.Float.Dyadic using (FloatFormat)

------------------------------------------------------------------------
-- FrameSemantics Interface (Adjacency-Based)
--
-- Stack frames are addressed via exact slot offsets, not inequalities.
--
-- The key abstraction:
--   - Frame: identity of a stack frame
--   - slot-addr f k: exact address of slot k in frame f
--   - _≺_: frame ordering (callee "further" than caller)
--   - frame-disjoint-bounded: bounded slots in ordered frames are disjoint
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

    -- | Decidable equality for frames
    _≟F_ : (f₁ f₂ : Frame) → Dec (f₁ ≡ f₂)

    -- | Frame base address (stack pointer at frame creation)
    frame-base : Frame → Addr

    --------------------------------------------------------------------
    -- Slot Addressing (Exact Offsets)
    --
    -- slot-addr f k gives the address of slot k in frame f.
    -- This is an exact offset, not a range or inequality.
    --
    -- Architecture instantiations compute this via their growth
    -- direction (x86: base + k * word-size).
    --------------------------------------------------------------------

    -- | Address of slot k in frame f
    slot-addr : Frame → ℕ → Addr

    -- | Slot 0 is at the frame base
    slot-zero-at-base : ∀ f → slot-addr f zero ≡ frame-base f

    -- | Different slots in same frame have different addresses
    slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → slot-addr f k₁ ≢ slot-addr f k₂

    --------------------------------------------------------------------
    -- Frame MOVEMENT (Plan 0.54 rung D)
    --
    -- Frames move with the stack pointer: a prologue's `sub rsp, n·word`
    -- makes the CALLEE's frame, `n` slots below the caller's, and the
    -- matching epilogue moves back. This is what distinguishes a callee's
    -- slot `k` from its caller's slot `k` — without it the abstract machine
    -- identifies two cells the hardware keeps apart, and no stack ADDRESS
    -- can be given a meaning (see `AtStack` in SMCore).
    --------------------------------------------------------------------

    -- | The frame `n` slots further in the growth direction (callee side).
    -- The way BACK is not an address computation — the machine restores the
    -- caller's frame from the frame stack `AllocState.saved-frames`, mirroring
    -- how the prologue/epilogue pair up.
    shift-frame : Frame → ℕ → Frame

    -- | Slot size in bytes (the machine word).
    frame-word : ℕ

    -- | …and it is at least one byte (plan 0.74 J6, D115).
    --
    -- A machine whose word is zero bytes cannot address anything, so this was
    -- always true; what changed is that something now DEPENDS on it.
    -- `fs-numerics` turns this into the target's Int width, and the literal
    -- exactness theorem it carries is false at width zero. So the fact has to
    -- be stated rather than assumed, and each frame instantiation says it.
    frame-word-pos : 0 < frame-word

    -- | Slots are LINEAR from the frame base — the target's `[sp + k·word]`.
    -- This is what lets a stack POINTER (`AtStack f k`) be given an address.
    slot-addr-linear : ∀ f k → slot-addr f k ≡ frame-base f + k * frame-word

    -- | A shifted frame's base is exactly `n` slots down: the prologue's
    -- `sub sp, n·word`.
    shift-base : ∀ f n → frame-base (shift-frame f n) ≡ frame-base f ∸ n * frame-word

    --------------------------------------------------------------------
    -- The target's FLOAT FORMAT (plan 0.73, D113)
    --
    -- `frame-word` is already here because the machine cannot address a
    -- slot without knowing the target's word. The float format is the same
    -- kind of fact for the same reason: under D113 a `Float` DENOTES the
    -- target's representation, so the abstract machine cannot materialise a
    -- float literal without knowing how this target lays one out — `1.5` is
    -- `0x3FC00000` at 32 bits and `0x3FF8000000000000` at 64.
    --
    -- With it here, `instr-load-const`'s dyadic payload is encoded AT EXEC
    -- TIME, so a `StoredValue` is uniformly bits and the per-arch `fenc`
    -- parameter threaded through the FlatCore correspondence disappears.
    --
    -- A target with no float support does not express that here (a format
    -- is always statable); it refuses `Float` through `FitsInReg`, which
    -- plan 0.72 P4 gives the arch.
    --------------------------------------------------------------------

    -- | How this target lays out a float: `binary32`, `binary64`, …
    float-format : FloatFormat

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

    -- | Frame ordering is transitive
    -- This follows naturally from address comparison (< is transitive).
    -- Needed for BeforeFrontier transfer across frame push/pop.
    ≺-trans : ∀ {f₁ f₂ f₃} → f₁ ≺ f₂ → f₂ ≺ f₃ → f₁ ≺ f₃

    -- | Frame ordering is irreflexive
    -- This follows naturally from address comparison (< is irreflexive).
    -- Needed for deriving f ≢ g from g ≺ f (e.g., in BeforeFrontier).
    ≺-irrefl : ∀ {f} → f ≺ f → ⊥

    -- | Frame ordering is trichotomous (total order)
    -- For any two frames, exactly one of: f₁ ≺ f₂, f₁ ≡ f₂, f₂ ≺ f₁
    -- This follows from addresses being natural numbers with trichotomous <.
    -- Needed for BeforeFrontier transfer between frames.
    ≺-compare : ∀ f₁ f₂ → (f₁ ≺ f₂) ⊎ (f₁ ≡ f₂) ⊎ (f₂ ≺ f₁)

    --------------------------------------------------------------------
    -- Bounded Frame Disjointness (Key Property)
    --
    -- Slots in ordered frames don't overlap WHEN the slot is within
    -- the gap to the next frame. This is THE core property enabling
    -- caller/callee isolation.
    --
    -- The bound condition (slot-addr f₁ k₁ < frame-base f₂) ensures
    -- we only claim disjointness for slots that fit in the allocated
    -- stack space. This is PROVABLE for any architecture:
    --   - slot-addr f₂ k₂ ≥ frame-base f₂ (slots grow from base)
    --   - slot-addr f₁ k₁ < frame-base f₂ (given)
    --   - Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂ (disjoint)
    --
    -- Architectures provide concrete implementations.
    --------------------------------------------------------------------

    -- | Bounded slots in ordered frames are disjoint
    frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
      f₁ ≺ f₂ →
      slot-addr f₁ k₁ < frame-base f₂ →  -- Slot is within gap
      slot-addr f₁ k₁ ≢ slot-addr f₂ k₂

open FrameSemantics public

------------------------------------------------------------------------
-- NOTE: Location (AllocMode) is NOT part of FrameSemantics
--
-- Location (StackAlloc frame slot | HeapAlloc addr) is defined in
-- MemoryValid.agda because:
--   1. It includes heap locations, which have nothing to do with frames
--   2. It's specific to validity tracking, not frame semantics
--   3. FrameSemantics should only deal with stack frames
--
-- See: Once.CCC.Target.X86.Correct.MemoryValid for the Location type.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: Frame Gap Sufficiency
--
-- Gap sufficiency (slot-addr f₁ capacity ≤ frame-base f₂) is NOT part
-- of the FrameSemantics interface because:
--
--   1. It's NOT an inherent property of frames - it depends on how
--      frames are created (prologue allocation)
--
--   2. For INTERNAL calls (Apply/thunk): Gap sufficiency is PROVABLE
--      from the code generation. The prologue allocates exactly
--      ir-stack-requirement slots, so slots within that capacity
--      are guaranteed to be below the caller's frame.
--
--   3. Only at PROGRAM ENTRY is gap sufficiency a trust boundary -
--      we trust the OS/runtime set up sufficient space before calling
--      our code.
--
-- See: Once.CCC.Target.X86.Correct.InitState.init-frame-gap-sufficient
-- for the program entry trust boundary postulate.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- THE TARGET'S NUMERICS, derived (plan 0.74, D115)
--
-- The machine already knows both facts: `float-format` above, and the WIDTH,
-- which is `frame-word` (the machine word in BYTES) times eight. So a module
-- fixed to a target never needs to name a width — which is what made baking
-- `Word64` anywhere avoidable.
--
-- Derived rather than a field, so it cannot disagree with the two facts it is
-- built from.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; mkTargetNum)

fs-numerics : FrameSemantics → TargetNum
fs-numerics FS = mkTargetNum (8 * frame-word FS) (float-format FS) bits-pos
  where
    -- `0 < 8 * frame-word FS` from `0 < frame-word FS`: eight copies of a
    -- positive number is positive.
    bits-pos : 0 < 8 * frame-word FS
    bits-pos = *-mono-≤ {1} {8} (s≤s z≤n) (frame-word-pos FS)
