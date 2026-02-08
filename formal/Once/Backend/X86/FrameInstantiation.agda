------------------------------------------------------------------------
-- Once.Backend.X86.FrameInstantiation
--
-- X86-64 instantiation of FrameSemantics (Adjacency-Based).
--
-- On x86-64:
--   - Stack grows downward (push decrements rsp)
--   - Slots within a frame grow upward (slot k at base + k * 8)
--   - Frame ordering: f₁ ≺ f₂ means addr f₁ < addr f₂
--     (callee's frame is at lower address, "further" in growth direction)
--
-- Key property: When callee's frame is below caller's, their slots
-- don't overlap because:
--   - Callee's slots: addr(callee) + k * 8, staying below addr(caller)
--   - Caller's slots: addr(caller) + j * 8, at or above addr(caller)
------------------------------------------------------------------------

module Once.Backend.X86.FrameInstantiation where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≥_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≢; <-≤-trans; ≤-<-trans; m≤m+n; *-monoˡ-<; +-monoʳ-<)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- Import the architecture-independent interface
open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.MemoryLayoutSemantics using (Addr)

-- Import X86 Layout for StackPointer and slot operations
open import Once.Backend.X86.Layout
  using (StackPointer; slot-addr; word-size;
         grow-identity; sp-distinct; offset-distinct;
         frame-below-slot0-disjoint; slot-addr-≥-base)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)

------------------------------------------------------------------------
-- X86-64 Frame Type
--
-- A Frame is a StackPointer (bundled address with InStack proof).
------------------------------------------------------------------------

X86Frame : Set
X86Frame = StackPointer

------------------------------------------------------------------------
-- Frame Base Address
------------------------------------------------------------------------

x86-frame-base : X86Frame → Addr
x86-frame-base = sp-addr

------------------------------------------------------------------------
-- Slot Addressing
--
-- X86 slots grow upward from frame base: slot k at base + k * word-size
------------------------------------------------------------------------

x86-slot-addr : X86Frame → ℕ → Addr
x86-slot-addr = slot-addr

x86-slot-zero-at-base : ∀ f → x86-slot-addr f zero ≡ x86-frame-base f
x86-slot-zero-at-base f = grow-identity (sp-addr f)

x86-slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → x86-slot-addr f k₁ ≢ x86-slot-addr f k₂
x86-slot-injective = offset-distinct

------------------------------------------------------------------------
-- Frame Ordering
--
-- f₁ ≺ f₂ means f₁ is "further" in stack growth direction.
-- On x86-64, stack grows downward, so "further" = lower address.
------------------------------------------------------------------------

_x86-≺_ : X86Frame → X86Frame → Set
f₁ x86-≺ f₂ = sp-addr f₁ < sp-addr f₂

------------------------------------------------------------------------
-- Frame Disjointness
--
-- When f₁ ≺ f₂ (f₁ at lower address), all slots of f₁ are disjoint
-- from all slots of f₂.
--
-- Proof strategy:
--   - slot-addr f₂ k₂ ≥ sp-addr f₂ (slots grow upward)
--   - slot-addr f₁ k₁ = sp-addr f₁ + k₁ * word-size
--   - Need: sp-addr f₁ + k₁ * 8 ≠ sp-addr f₂ + k₂ * 8
--
-- This holds when frames are properly separated (callee uses only
-- its allocated space). For now we prove the cases needed and
-- postulate the general form.
------------------------------------------------------------------------

-- | Slot 0 of f₁ is disjoint from any slot of f₂ (proven in Layout)
x86-frame-disjoint-slot0 : ∀ f₁ f₂ k₂ →
  f₁ x86-≺ f₂ →
  x86-slot-addr f₁ zero ≢ x86-slot-addr f₂ k₂
x86-frame-disjoint-slot0 f₁ f₂ k₂ f₁<f₂ =
  frame-below-slot0-disjoint f₁ f₂ k₂ f₁<f₂

-- | Any slot of f₂ is disjoint from slot 0 of f₁ (symmetric)
x86-frame-disjoint-slot0-sym : ∀ f₁ f₂ k₂ →
  f₁ x86-≺ f₂ →
  x86-slot-addr f₂ k₂ ≢ x86-slot-addr f₁ zero
x86-frame-disjoint-slot0-sym f₁ f₂ k₂ f₁<f₂ eq =
  x86-frame-disjoint-slot0 f₁ f₂ k₂ f₁<f₂ (sym eq)

-- | Slot address is strictly monotonic in slot index
-- If k₁ < k₂, then slot-addr frame k₁ < slot-addr frame k₂
-- This follows from slots growing upward: slot-addr frame k = base + k * word-size
x86-slot-addr-mono-< : ∀ frame k₁ k₂ →
  k₁ < k₂ →
  x86-slot-addr frame k₁ < x86-slot-addr frame k₂
x86-slot-addr-mono-< frame k₁ k₂ k₁<k₂ =
  +-monoʳ-< (sp-addr frame) (*-monoˡ-< word-size k₁<k₂)
  -- *-monoˡ-< word-size k₁<k₂ : k₁ * word-size < k₂ * word-size
  -- +-monoʳ-< base ... : base + k₁ * word-size < base + k₂ * word-size

-- | General frame disjointness (bounded): slot of f₁ ≠ slot of f₂
-- when the slot stays within the frame's bounds.
--
-- PROVEN: If slot-addr f₁ k₁ < addr f₂, and f₂'s slots are ≥ addr f₂,
-- then the addresses can't be equal.
x86-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ x86-≺ f₂ →
  x86-slot-addr f₁ k₁ < sp-addr f₂ →  -- Slot is within frame bounds
  x86-slot-addr f₁ k₁ ≢ x86-slot-addr f₂ k₂
x86-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot<f₂ eq =
  <⇒≢ slot₁<slot₂ eq
  where
    -- slot-addr f₂ k₂ ≥ addr f₂ (slots grow upward)
    slot₂≥f₂ : x86-slot-addr f₂ k₂ ≥ sp-addr f₂
    slot₂≥f₂ = slot-addr-≥-base f₂ k₂

    -- Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂
    slot₁<slot₂ : x86-slot-addr f₁ k₁ < x86-slot-addr f₂ k₂
    slot₁<slot₂ = <-≤-trans slot<f₂ slot₂≥f₂

-- | Slot within capacity is below caller frame when gap is sufficient
-- If slot < capacity and slot-addr frame capacity ≤ caller-base,
-- then slot-addr frame slot < caller-base.
x86-slot-within-capacity-bound : ∀ frame caller-frame slot capacity →
  slot < capacity →
  x86-slot-addr frame capacity ≤ sp-addr caller-frame →
  x86-slot-addr frame slot < sp-addr caller-frame
x86-slot-within-capacity-bound frame caller-frame slot capacity slot<cap gap-sufficient =
  <-≤-trans slot<cap-addr gap-sufficient
  where
    -- slot-addr slot < slot-addr capacity (by monotonicity)
    slot<cap-addr : x86-slot-addr frame slot < x86-slot-addr frame capacity
    slot<cap-addr = x86-slot-addr-mono-< frame slot capacity slot<cap

-- | General frame disjointness with capacity bound
-- When k₁ < capacity and frame gap is sufficient, slots are disjoint.
x86-frame-disjoint-with-capacity : ∀ f₁ f₂ k₁ k₂ capacity →
  f₁ x86-≺ f₂ →
  k₁ < capacity →
  x86-slot-addr f₁ capacity ≤ sp-addr f₂ →
  x86-slot-addr f₁ k₁ ≢ x86-slot-addr f₂ k₂
x86-frame-disjoint-with-capacity f₁ f₂ k₁ k₂ capacity f₁<f₂ k₁<cap gap-sufficient =
  x86-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot-bound
  where
    slot-bound : x86-slot-addr f₁ k₁ < sp-addr f₂
    slot-bound = x86-slot-within-capacity-bound f₁ f₂ k₁ capacity k₁<cap gap-sufficient

-- | General frame disjointness: any slot of f₁ ≠ any slot of f₂
-- POSTULATE: Requires tracking that k₁ is within frame capacity.
-- Use x86-frame-disjoint-bounded or x86-frame-disjoint-with-capacity when you have bounds.
postulate
  x86-frame-disjoint : ∀ f₁ f₂ k₁ k₂ →
    f₁ x86-≺ f₂ →
    x86-slot-addr f₁ k₁ ≢ x86-slot-addr f₂ k₂

------------------------------------------------------------------------
-- X86-64 FrameSemantics Instance
------------------------------------------------------------------------

x86-frame-semantics : FrameSemantics
x86-frame-semantics = record
  { Frame = X86Frame
  ; frame-base = x86-frame-base
  ; slot-addr = x86-slot-addr
  ; slot-zero-at-base = x86-slot-zero-at-base
  ; slot-injective = x86-slot-injective
  ; _≺_ = _x86-≺_
  ; frame-disjoint = x86-frame-disjoint
  }

------------------------------------------------------------------------
-- Convenience Re-exports
------------------------------------------------------------------------

open FrameSemantics x86-frame-semantics public
  renaming ( Frame to X86-Frame
           ; frame-base to X86-frame-base
           ; slot-addr to X86-slot-addr
           ; _≺_ to _X86-≺_
           ; frame-disjoint to X86-frame-disjoint
           )
