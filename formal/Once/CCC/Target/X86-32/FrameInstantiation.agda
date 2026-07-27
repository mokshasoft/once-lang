-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.FrameInstantiation
--
-- x86-32 instantiation of FrameSemantics.
--
-- On x86-32:
--   - Stack grows downward (push decrements esp)
--   - Slots within a frame grow upward (slot k at base + k * 4)
--   - Frame ordering: f₁ ≺ f₂ means addr f₁ < addr f₂
--     (callee's frame is at lower address, "further" in growth direction)
--
-- Key property: When callee's frame is below caller's, bounded slots
-- don't overlap because:
--   - Callee's slots: addr(callee) + k * 4, staying below addr(caller)
--   - Caller's slots: addr(caller) + j * 4, at or above addr(caller)
--
-- Bounded disjointness follows from arithmetic on slot addresses.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.FrameInstantiation where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≥_; _+_; _*_; s≤s; z≤n; _∸_)
open import Data.Nat.Properties using (<⇒≢; <-trans; <-≤-trans; ≤-<-trans; m≤m+n; *-monoˡ-<; +-monoʳ-<; _≟_; ≤-irrelevant; <-irrefl; <-cmp)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

-- Import the architecture-independent interface
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.MemoryLayoutSemantics using (Addr)

-- Import x86-32 Layout for StackPointer and slot operations
open import Once.CCC.Target.X86-32.Layout
  using (StackPointer; slot-addr; word-size;
         grow-identity; sp-distinct; offset-distinct;
         frame-below-slot0-disjoint; slot-addr-≥-base;
         InStack; in-stack)
open import Once.CCC.Target.X86-32.Layout using (stack-addr; in-stack; stack-sub-preserves') renaming (addr to sp-addr)

------------------------------------------------------------------------
-- x86-32 Frame Type
--
-- A Frame is a StackPointer (bundled address with InStack proof).
------------------------------------------------------------------------

X86-32Frame : Set
X86-32Frame = StackPointer

------------------------------------------------------------------------
-- Decidable Equality for Frames
--
-- Two StackPointers are equal iff their addresses are equal.
-- The InStack proofs are equal by ≤-irrelevant.
------------------------------------------------------------------------

-- Helper: InStack proofs are equal when addresses are equal
InStack-irrelevant : ∀ {a} (p q : InStack a) → p ≡ q
InStack-irrelevant (p₁ , p₂) (q₁ , q₂) = cong₂ _,_ (≤-irrelevant p₁ q₁) (≤-irrelevant p₂ q₂)

_x86-32-≟F_ : (f₁ f₂ : X86-32Frame) → Dec (f₁ ≡ f₂)
f₁ x86-32-≟F f₂ with sp-addr f₁ ≟ sp-addr f₂
... | no  a≢a = no λ { refl → a≢a refl }
... | yes a≡a = yes (sp-eq a≡a)
  where
    -- When addresses are equal, the InStack proofs are also equal
    sp-eq : sp-addr f₁ ≡ sp-addr f₂ → f₁ ≡ f₂
    sp-eq refl with InStack-irrelevant (in-stack f₁) (in-stack f₂)
    ... | refl = refl

------------------------------------------------------------------------
-- Frame Base Address
------------------------------------------------------------------------

x86-32-frame-base : X86-32Frame → Addr
x86-32-frame-base = sp-addr

------------------------------------------------------------------------
-- Slot Addressing
--
-- x86-32 slots grow upward from frame base: slot k at base + k * word-size
------------------------------------------------------------------------

-- | Direct definition of x86-32 slot address: base + k * word-size
-- This gives definitional reduction, unlike using the abstract slot-addr.
x86-32-slot-addr : X86-32Frame → ℕ → Addr
x86-32-slot-addr f k = sp-addr f + k * word-size

-- | Proof that x86-32-slot-addr equals the abstract slot-addr
x86-32-slot-addr-eq : ∀ f k → x86-32-slot-addr f k ≡ slot-addr f k
x86-32-slot-addr-eq f k = refl  -- Both compute to sp-addr f + k * word-size

x86-32-slot-zero-at-base : ∀ f → x86-32-slot-addr f zero ≡ x86-32-frame-base f
x86-32-slot-zero-at-base f = Data.Nat.Properties.+-identityʳ (sp-addr f)
  where import Data.Nat.Properties

-- | Slot (suc k) is word-size bytes above slot k
x86-32-slot-addr-suc : ∀ f k → x86-32-slot-addr f (suc k) ≡ x86-32-slot-addr f k + word-size
x86-32-slot-addr-suc f k =
  trans (cong (sp-addr f +_) (+-comm word-size (k * word-size)))
        (sym (+-assoc (sp-addr f) (k * word-size) word-size))
  where open import Data.Nat.Properties using (+-assoc; +-comm)

x86-32-slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → x86-32-slot-addr f k₁ ≢ x86-32-slot-addr f k₂
x86-32-slot-injective = offset-distinct

------------------------------------------------------------------------
-- Frame Ordering
--
-- f₁ ≺ f₂ means f₁ is "further" in stack growth direction.
-- On x86-32, stack grows downward, so "further" = lower address.
------------------------------------------------------------------------

_x86-32-≺_ : X86-32Frame → X86-32Frame → Set
f₁ x86-32-≺ f₂ = sp-addr f₁ < sp-addr f₂

-- | Frame ordering is transitive (follows from < on addresses)
x86-32-≺-trans : ∀ {f₁ f₂ f₃} → f₁ x86-32-≺ f₂ → f₂ x86-32-≺ f₃ → f₁ x86-32-≺ f₃
x86-32-≺-trans {f₁} {f₂} {f₃} f₁≺f₂ f₂≺f₃ = <-trans f₁≺f₂ f₂≺f₃

-- | Frame ordering is irreflexive (follows from < on addresses)
x86-32-≺-irrefl : ∀ {f} → f x86-32-≺ f → ⊥
x86-32-≺-irrefl {f} f≺f = <-irrefl refl f≺f

-- | Frame ordering is trichotomous (total order on addresses)
x86-32-≺-compare : ∀ f₁ f₂ → (f₁ x86-32-≺ f₂) ⊎ (f₁ ≡ f₂) ⊎ (f₂ x86-32-≺ f₁)
x86-32-≺-compare f₁ f₂ with <-cmp (sp-addr f₁) (sp-addr f₂)
... | tri< a<b _ _ = inj₁ a<b
... | tri≈ _ a≡b _ = inj₂ (inj₁ (sp-eq a≡b))
  where
    sp-eq : sp-addr f₁ ≡ sp-addr f₂ → f₁ ≡ f₂
    sp-eq refl with InStack-irrelevant (in-stack f₁) (in-stack f₂)
    ... | refl = refl
... | tri> _ _ b<a = inj₂ (inj₂ b<a)

------------------------------------------------------------------------
-- Frame Disjointness
--
-- When f₁ ≺ f₂ (f₁ at lower address), bounded slots of f₁ are disjoint
-- from all slots of f₂.
------------------------------------------------------------------------

-- | Slot address is strictly monotonic in slot index
x86-32-slot-addr-mono-< : ∀ frame k₁ k₂ →
  k₁ < k₂ →
  x86-32-slot-addr frame k₁ < x86-32-slot-addr frame k₂
x86-32-slot-addr-mono-< frame k₁ k₂ k₁<k₂ =
  +-monoʳ-< (sp-addr frame) (*-monoˡ-< word-size k₁<k₂)

-- | Bounded frame disjointness: slot of f₁ ≠ slot of f₂
x86-32-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ x86-32-≺ f₂ →
  x86-32-slot-addr f₁ k₁ < sp-addr f₂ →  -- Slot is within frame bounds
  x86-32-slot-addr f₁ k₁ ≢ x86-32-slot-addr f₂ k₂
x86-32-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot<f₂ eq =
  <⇒≢ slot₁<slot₂ eq
  where
    slot₂≥f₂ : x86-32-slot-addr f₂ k₂ ≥ sp-addr f₂
    slot₂≥f₂ = slot-addr-≥-base f₂ k₂

    slot₁<slot₂ : x86-32-slot-addr f₁ k₁ < x86-32-slot-addr f₂ k₂
    slot₁<slot₂ = <-≤-trans slot<f₂ slot₂≥f₂

-- | Slot within capacity is below caller frame when gap is sufficient
x86-32-slot-within-capacity-bound : ∀ frame caller-frame slot capacity →
  slot < capacity →
  x86-32-slot-addr frame capacity ≤ sp-addr caller-frame →
  x86-32-slot-addr frame slot < sp-addr caller-frame
x86-32-slot-within-capacity-bound frame caller-frame slot capacity slot<cap gap-sufficient =
  <-≤-trans slot<cap-addr gap-sufficient
  where
    slot<cap-addr : x86-32-slot-addr frame slot < x86-32-slot-addr frame capacity
    slot<cap-addr = x86-32-slot-addr-mono-< frame slot capacity slot<cap

-- | Frame disjointness with capacity bound
x86-32-frame-disjoint-with-capacity : ∀ f₁ f₂ k₁ k₂ capacity →
  f₁ x86-32-≺ f₂ →
  k₁ < capacity →
  x86-32-slot-addr f₁ capacity ≤ sp-addr f₂ →
  x86-32-slot-addr f₁ k₁ ≢ x86-32-slot-addr f₂ k₂
x86-32-frame-disjoint-with-capacity f₁ f₂ k₁ k₂ capacity f₁<f₂ k₁<cap gap-sufficient =
  x86-32-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot-bound
  where
    slot-bound : x86-32-slot-addr f₁ k₁ < sp-addr f₂
    slot-bound = x86-32-slot-within-capacity-bound f₁ f₂ k₁ capacity k₁<cap gap-sufficient

------------------------------------------------------------------------
-- Frame movement: the callee frame sits `n` slots DOWN (the prologue's
-- `sub esp, n·word`). The stack region is downward-closed, so this is total.
------------------------------------------------------------------------

x86-32-shift-frame : X86-32Frame → ℕ → X86-32Frame
x86-32-shift-frame f n =
  stack-addr (sp-addr f ∸ n * word-size)
             (stack-sub-preserves' (sp-addr f) (n * word-size) (in-stack f))

------------------------------------------------------------------------
-- x86-32 FrameSemantics Instance
------------------------------------------------------------------------

x86-32-frame-semantics : FrameSemantics
x86-32-frame-semantics = record
  { Frame = X86-32Frame
  ; _≟F_ = _x86-32-≟F_
  ; frame-base = x86-32-frame-base
  ; slot-addr = x86-32-slot-addr
  ; shift-frame = x86-32-shift-frame
  ; slot-zero-at-base = x86-32-slot-zero-at-base
  ; slot-injective = x86-32-slot-injective
  ; _≺_ = _x86-32-≺_
  ; ≺-trans = λ f₁≺f₂ f₂≺f₃ → <-trans f₁≺f₂ f₂≺f₃
  ; ≺-irrefl = λ f≺f → <-irrefl refl f≺f
  ; ≺-compare = x86-32-≺-compare
  ; frame-disjoint-bounded = x86-32-frame-disjoint-bounded
  }

------------------------------------------------------------------------
-- Convenience Re-exports
------------------------------------------------------------------------

open FrameSemantics x86-32-frame-semantics public
  renaming ( Frame to X86-32-Frame
           ; frame-base to X86-32-frame-base
           ; slot-addr to X86-32-slot-addr
           ; _≺_ to _X86-32-≺_
           )