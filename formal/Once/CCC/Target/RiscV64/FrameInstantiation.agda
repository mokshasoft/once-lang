-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.FrameInstantiation
--
-- RISC-V 64-bit instantiation of FrameSemantics.
--
-- On RISC-V 64:
--   - Stack grows downward (push decrements sp)
--   - Slots within a frame grow upward (slot k at base + k * 8)
--   - Frame ordering: f₁ ≺ f₂ means addr f₁ < addr f₂
--     (callee's frame is at lower address, "further" in growth direction)
--
-- Key property: When callee's frame is below caller's, bounded slots
-- don't overlap because:
--   - Callee's slots: addr(callee) + k * 8, staying below addr(caller)
--   - Caller's slots: addr(caller) + j * 8, at or above addr(caller)
--
-- Bounded disjointness follows from arithmetic on slot addresses.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.FrameInstantiation where

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
open import Once.Float.Dyadic using (binary64)
open import Once.Memory.MemoryLayoutSemantics using (Addr)

-- Import RISC-V 64 Layout for StackPointer and slot operations
open import Once.CCC.Target.RiscV64.Layout
  using (StackPointer; slot-addr; word-size;
         grow-identity; sp-distinct; offset-distinct;
         frame-below-slot0-disjoint; slot-addr-≥-base;
         InStack; in-stack)
open import Once.CCC.Target.RiscV64.Layout using (stack-addr; in-stack; stack-sub-preserves') renaming (addr to sp-addr)

------------------------------------------------------------------------
-- RISC-V 64 Frame Type
--
-- A Frame is a StackPointer (bundled address with InStack proof).
------------------------------------------------------------------------

RV64Frame : Set
RV64Frame = StackPointer

------------------------------------------------------------------------
-- Decidable Equality for Frames
--
-- Two StackPointers are equal iff their addresses are equal.
-- The InStack proofs are equal by ≤-irrelevant.
------------------------------------------------------------------------

-- Helper: InStack proofs are equal when addresses are equal
InStack-irrelevant : ∀ {a} (p q : InStack a) → p ≡ q
InStack-irrelevant (p₁ , p₂) (q₁ , q₂) = cong₂ _,_ (≤-irrelevant p₁ q₁) (≤-irrelevant p₂ q₂)

_rv64-≟F_ : (f₁ f₂ : RV64Frame) → Dec (f₁ ≡ f₂)
f₁ rv64-≟F f₂ with sp-addr f₁ ≟ sp-addr f₂
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

rv64-frame-base : RV64Frame → Addr
rv64-frame-base = sp-addr

------------------------------------------------------------------------
-- Slot Addressing
--
-- RISC-V 64 slots grow upward from frame base: slot k at base + k * word-size
------------------------------------------------------------------------

-- | Direct definition of RISC-V 64 slot address: base + k * word-size
-- This gives definitional reduction, unlike using the abstract slot-addr.
rv64-slot-addr : RV64Frame → ℕ → Addr
rv64-slot-addr f k = sp-addr f + k * word-size

-- | Proof that rv64-slot-addr equals the abstract slot-addr
rv64-slot-addr-eq : ∀ f k → rv64-slot-addr f k ≡ slot-addr f k
rv64-slot-addr-eq f k = refl  -- Both compute to sp-addr f + k * word-size

rv64-slot-zero-at-base : ∀ f → rv64-slot-addr f zero ≡ rv64-frame-base f
rv64-slot-zero-at-base f = Data.Nat.Properties.+-identityʳ (sp-addr f)
  where import Data.Nat.Properties

-- | Slot (suc k) is word-size bytes above slot k
-- This is THE canonical slot-addr-suc for use with rv64-frame-semantics
--
-- Proof: slot-addr sp (suc k) = sp + (suc k) * word-size
--                             = sp + (word-size + k * word-size)   [by def of *]
--                             = sp + (k * word-size + word-size)   [by +-comm]
--                             = (sp + k * word-size) + word-size   [by +-assoc]
--                             = slot-addr sp k + word-size
rv64-slot-addr-suc : ∀ f k → rv64-slot-addr f (suc k) ≡ rv64-slot-addr f k + word-size
rv64-slot-addr-suc f k =
  trans (cong (sp-addr f +_) (+-comm word-size (k * word-size)))
        (sym (+-assoc (sp-addr f) (k * word-size) word-size))
  where open import Data.Nat.Properties using (+-assoc; +-comm)

rv64-slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → rv64-slot-addr f k₁ ≢ rv64-slot-addr f k₂
rv64-slot-injective = offset-distinct

------------------------------------------------------------------------
-- Frame Ordering
--
-- f₁ ≺ f₂ means f₁ is "further" in stack growth direction.
-- On RISC-V 64, stack grows downward, so "further" = lower address.
------------------------------------------------------------------------

_rv64-≺_ : RV64Frame → RV64Frame → Set
f₁ rv64-≺ f₂ = sp-addr f₁ < sp-addr f₂

-- | Frame ordering is transitive (follows from < on addresses)
rv64-≺-trans : ∀ {f₁ f₂ f₃} → f₁ rv64-≺ f₂ → f₂ rv64-≺ f₃ → f₁ rv64-≺ f₃
rv64-≺-trans {f₁} {f₂} {f₃} f₁≺f₂ f₂≺f₃ = <-trans f₁≺f₂ f₂≺f₃

-- | Frame ordering is irreflexive (follows from < on addresses)
rv64-≺-irrefl : ∀ {f} → f rv64-≺ f → ⊥
rv64-≺-irrefl {f} f≺f = <-irrefl refl f≺f

-- | Frame ordering is trichotomous (total order on addresses)
rv64-≺-compare : ∀ f₁ f₂ → (f₁ rv64-≺ f₂) ⊎ (f₁ ≡ f₂) ⊎ (f₂ rv64-≺ f₁)
rv64-≺-compare f₁ f₂ with <-cmp (sp-addr f₁) (sp-addr f₂)
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
--
-- Proof strategy:
--   - slot-addr f₂ k₂ ≥ sp-addr f₂ (slots grow upward)
--   - slot-addr f₁ k₁ < sp-addr f₂ (given by bound)
--   - Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂ (disjoint)
------------------------------------------------------------------------

-- | Slot address is strictly monotonic in slot index
-- If k₁ < k₂, then slot-addr frame k₁ < slot-addr frame k₂
rv64-slot-addr-mono-< : ∀ frame k₁ k₂ →
  k₁ < k₂ →
  rv64-slot-addr frame k₁ < rv64-slot-addr frame k₂
rv64-slot-addr-mono-< frame k₁ k₂ k₁<k₂ =
  +-monoʳ-< (sp-addr frame) (*-monoˡ-< word-size k₁<k₂)

-- | Bounded frame disjointness: slot of f₁ ≠ slot of f₂
-- when the slot stays within the frame's bounds.
--
-- If slot-addr f₁ k₁ < addr f₂, and f₂'s slots are ≥ addr f₂,
-- then the addresses can't be equal.
rv64-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ rv64-≺ f₂ →
  rv64-slot-addr f₁ k₁ < sp-addr f₂ →  -- Slot is within frame bounds
  rv64-slot-addr f₁ k₁ ≢ rv64-slot-addr f₂ k₂
rv64-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot<f₂ eq =
  <⇒≢ slot₁<slot₂ eq
  where
    -- slot-addr f₂ k₂ ≥ addr f₂ (slots grow upward)
    slot₂≥f₂ : rv64-slot-addr f₂ k₂ ≥ sp-addr f₂
    slot₂≥f₂ = slot-addr-≥-base f₂ k₂

    -- Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂
    slot₁<slot₂ : rv64-slot-addr f₁ k₁ < rv64-slot-addr f₂ k₂
    slot₁<slot₂ = <-≤-trans slot<f₂ slot₂≥f₂

-- | Slot within capacity is below caller frame when gap is sufficient
rv64-slot-within-capacity-bound : ∀ frame caller-frame slot capacity →
  slot < capacity →
  rv64-slot-addr frame capacity ≤ sp-addr caller-frame →
  rv64-slot-addr frame slot < sp-addr caller-frame
rv64-slot-within-capacity-bound frame caller-frame slot capacity slot<cap gap-sufficient =
  <-≤-trans slot<cap-addr gap-sufficient
  where
    slot<cap-addr : rv64-slot-addr frame slot < rv64-slot-addr frame capacity
    slot<cap-addr = rv64-slot-addr-mono-< frame slot capacity slot<cap

-- | Frame disjointness with capacity bound
-- When k₁ < capacity and frame gap is sufficient, slots are disjoint.
rv64-frame-disjoint-with-capacity : ∀ f₁ f₂ k₁ k₂ capacity →
  f₁ rv64-≺ f₂ →
  k₁ < capacity →
  rv64-slot-addr f₁ capacity ≤ sp-addr f₂ →
  rv64-slot-addr f₁ k₁ ≢ rv64-slot-addr f₂ k₂
rv64-frame-disjoint-with-capacity f₁ f₂ k₁ k₂ capacity f₁<f₂ k₁<cap gap-sufficient =
  rv64-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot-bound
  where
    slot-bound : rv64-slot-addr f₁ k₁ < sp-addr f₂
    slot-bound = rv64-slot-within-capacity-bound f₁ f₂ k₁ capacity k₁<cap gap-sufficient

------------------------------------------------------------------------
-- Frame movement: the callee frame sits `n` slots DOWN (the prologue's
-- `sub sp, n·word`). The stack region is downward-closed, so this is total.
------------------------------------------------------------------------

rv64-shift-frame : RV64Frame → ℕ → RV64Frame
rv64-shift-frame f n =
  stack-addr (sp-addr f ∸ n * word-size)
             (stack-sub-preserves' (sp-addr f) (n * word-size) (in-stack f))

------------------------------------------------------------------------
-- RISC-V 64 FrameSemantics Instance
------------------------------------------------------------------------

rv64-frame-semantics : FrameSemantics
rv64-frame-semantics = record
  { Frame = RV64Frame
  ; _≟F_ = _rv64-≟F_
  ; frame-base = rv64-frame-base
  ; slot-addr = rv64-slot-addr
  ; shift-frame = rv64-shift-frame
  ; frame-word = word-size
  -- plan 0.74 J6: the word is at least one byte, so the target's Int width
  -- is at least one bit — which is what the literal exactness theorem needs.
  ; frame-word-pos = s≤s z≤n
  ; slot-addr-linear = λ f k → refl
  ; shift-base = λ f n → refl
  -- Plan 0.73 (D113): riscv64 with the `D` extension; a `double` fits a 64-bit register.
  ; float-format = binary64
  ; slot-zero-at-base = rv64-slot-zero-at-base
  ; slot-injective = rv64-slot-injective
  ; _≺_ = _rv64-≺_
  ; ≺-trans = λ f₁≺f₂ f₂≺f₃ → <-trans f₁≺f₂ f₂≺f₃
  ; ≺-irrefl = λ f≺f → <-irrefl refl f≺f
  ; ≺-compare = rv64-≺-compare
  ; frame-disjoint-bounded = rv64-frame-disjoint-bounded
  }

------------------------------------------------------------------------
-- Convenience Re-exports
------------------------------------------------------------------------

open FrameSemantics rv64-frame-semantics public
  renaming ( Frame to RiscV64-Frame
           ; frame-base to RiscV64-frame-base
           ; slot-addr to RiscV64-slot-addr
           ; _≺_ to _RiscV64-≺_
           )