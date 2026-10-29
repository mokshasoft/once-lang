-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Nat.Properties using (<⇒≢; <-trans; <-≤-trans; *-monoˡ-<; +-monoʳ-<; _≟_; ≤-irrelevant; <-irrefl; <-cmp; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

-- Import the architecture-independent interface
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Internal.Trace using (Interp)
open import Once.Spec.Float.Dyadic using (binary32)
open import Once.Memory.MemoryLayoutSemantics using (Addr)

-- Import x86-32 Layout for StackPointer and slot operations
open import Once.CCC.Target.X86-32.Layout using (StackPointer; slot-addr; offset-distinct; slot-addr-≥-base; InStack; in-stack; _≟SP_; stack-addr-inj)
open import Once.CCC.Target.X86-32.StackGrowth using (word-size)
open import Once.CCC.Target.X86-32.Layout using (stack-addr; stack-sub-preserves') renaming (addr to sp-addr)

------------------------------------------------------------------------
-- x86-32-32 Frame Type (plan 0.124 S1)
--
-- A Frame is a StackPointer TAGGED WITH ITS DEPTH: the number of slots it
-- sits below the entry frame. The address is where the frame lives; the
-- depth is which frame it is.
--
-- They come apart only at the stack floor. `sp ∸ n·word` stops at zero, so a
-- call made from the lowest frame used to get its caller's own frame back,
-- and the callee's `c-thunk` cleared the caller's live slots (plan 0.124 §3a).
-- The depth never stops, so the callee's frame is always new and always
-- `≺` its caller's (`x86-32-shift-≺`). The abstract stack has no floor; running
-- out of stack is the concrete machine's outcome, as running out of heap is.
--
-- Every address law reads the address only, so it is unchanged.
------------------------------------------------------------------------

X86-32Frame : Set
X86-32Frame = StackPointer × ℕ

frame-sp : X86-32Frame → StackPointer
frame-sp = proj₁

frame-depth : X86-32Frame → ℕ
frame-depth = proj₂

------------------------------------------------------------------------
-- Decidable Equality for Frames
--
-- Two frames are equal iff their addresses and their depths are equal.
------------------------------------------------------------------------

_x86-32-≟F_ : DecidableEquality X86-32Frame
(sp₁ , d₁) x86-32-≟F (sp₂ , d₂) with sp₁ ≟SP sp₂
... | no sp≢   = no λ { refl → sp≢ refl }
... | yes refl with d₁ ≟ d₂
...   | yes refl = yes refl
...   | no d≢    = no λ { refl → d≢ refl }

------------------------------------------------------------------------
-- Frame Base Address
------------------------------------------------------------------------

x86-32-frame-base : X86-32Frame → Addr
x86-32-frame-base f = sp-addr (frame-sp f)

------------------------------------------------------------------------
-- Slot Addressing
--
-- Slots grow upward from frame base: slot k at base + k * word-size
------------------------------------------------------------------------

-- | Direct definition of x86-32 slot address: base + k * word-size
-- This gives definitional reduction, unlike using the abstract slot-addr.
x86-32-slot-addr : X86-32Frame → ℕ → Addr
x86-32-slot-addr f k = x86-32-frame-base f + k * word-size

-- | Proof that x86-32-slot-addr equals the abstract slot-addr
x86-32-slot-addr-eq : ∀ f k → x86-32-slot-addr f k ≡ slot-addr (frame-sp f) k
x86-32-slot-addr-eq f k = refl  -- Both compute to sp-addr + k * word-size

x86-32-slot-zero-at-base : ∀ f → x86-32-slot-addr f zero ≡ x86-32-frame-base f
x86-32-slot-zero-at-base f = Data.Nat.Properties.+-identityʳ (x86-32-frame-base f)
  where import Data.Nat.Properties

-- | Slot (suc k) is word-size bytes above slot k
-- This is THE canonical slot-addr-suc for use with x86-32-frame-semantics
--
-- Proof: slot-addr sp (suc k) = sp + (suc k) * word-size
--                             = sp + (word-size + k * word-size)   [by def of *]
--                             = sp + (k * word-size + word-size)   [by +-comm]
--                             = (sp + k * word-size) + word-size   [by +-assoc]
--                             = slot-addr sp k + word-size
x86-32-slot-addr-suc : ∀ f k → x86-32-slot-addr f (suc k) ≡ x86-32-slot-addr f k + word-size
x86-32-slot-addr-suc f k =
  trans (cong (x86-32-frame-base f +_) (+-comm word-size (k * word-size)))
        (sym (+-assoc (x86-32-frame-base f) (k * word-size) word-size))
  where open import Data.Nat.Properties using (+-assoc; +-comm)

x86-32-slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → x86-32-slot-addr f k₁ ≢ x86-32-slot-addr f k₂
x86-32-slot-injective f = offset-distinct (frame-sp f)

------------------------------------------------------------------------
-- Frame Ordering
--
-- f₁ ≺ f₂ means f₁ is "further" in stack growth direction: DEEPER, or at
-- the same depth and lower. Depth decides, so a callee is `≺` its caller
-- even where the address cannot say so (the floor). The address breaks
-- ties, which keeps the order total.
------------------------------------------------------------------------

_x86-32-≺_ : X86-32Frame → X86-32Frame → Set
f₁ x86-32-≺ f₂ = frame-depth f₂ < frame-depth f₁
            ⊎ (frame-depth f₁ ≡ frame-depth f₂ × x86-32-frame-base f₁ < x86-32-frame-base f₂)

-- | Frame ordering is transitive (lexicographic on depth, then address)
x86-32-≺-trans : ∀ {f₁ f₂ f₃} → f₁ x86-32-≺ f₂ → f₂ x86-32-≺ f₃ → f₁ x86-32-≺ f₃
x86-32-≺-trans (inj₁ d₂<d₁)        (inj₁ d₃<d₂)        = inj₁ (<-trans d₃<d₂ d₂<d₁)
x86-32-≺-trans (inj₁ d₂<d₁)        (inj₂ (refl , _))   = inj₁ d₂<d₁
x86-32-≺-trans (inj₂ (refl , _))   (inj₁ d₃<d₂)        = inj₁ d₃<d₂
x86-32-≺-trans (inj₂ (refl , a₁<a₂)) (inj₂ (refl , a₂<a₃)) = inj₂ (refl , <-trans a₁<a₂ a₂<a₃)

-- | Frame ordering is irreflexive
x86-32-≺-irrefl : ∀ {f} → f x86-32-≺ f → ⊥
x86-32-≺-irrefl (inj₁ d<d)       = <-irrefl refl d<d
x86-32-≺-irrefl (inj₂ (_ , a<a)) = <-irrefl refl a<a

-- | Frame ordering is trichotomous (lexicographic on two total orders)
x86-32-≺-compare : ∀ f₁ f₂ → (f₁ x86-32-≺ f₂) ⊎ (f₁ ≡ f₂) ⊎ (f₂ x86-32-≺ f₁)
x86-32-≺-compare (sp₁ , d₁) (sp₂ , d₂) with <-cmp d₂ d₁
... | tri< d₂<d₁ _ _ = inj₁ (inj₁ d₂<d₁)
... | tri> _ _ d₁<d₂ = inj₂ (inj₂ (inj₁ d₁<d₂))
... | tri≈ _ refl _ with <-cmp (sp-addr sp₁) (sp-addr sp₂)
...   | tri< a<b _ _ = inj₁ (inj₂ (refl , a<b))
...   | tri≈ _ a≡b _ = inj₂ (inj₁ (cong (_, d₁) (stack-addr-inj a≡b)))
...   | tri> _ _ b<a = inj₂ (inj₂ (inj₂ (refl , b<a)))

------------------------------------------------------------------------
-- Frame Disjointness
--
-- A slot of f₁ that lies below f₂'s base is disjoint from all slots of f₂.
-- The ordering premise is not needed: the bound alone decides it.
--
-- Proof strategy:
--   - slot-addr f₂ k₂ ≥ frame-base f₂ (slots grow upward)
--   - slot-addr f₁ k₁ < frame-base f₂ (given by bound)
--   - Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂ (disjoint)
------------------------------------------------------------------------

-- | Slot address is strictly monotonic in slot index
-- If k₁ < k₂, then slot-addr frame k₁ < slot-addr frame k₂
x86-32-slot-addr-mono-< : ∀ frame k₁ k₂ →
  k₁ < k₂ →
  x86-32-slot-addr frame k₁ < x86-32-slot-addr frame k₂
x86-32-slot-addr-mono-< frame k₁ k₂ k₁<k₂ =
  +-monoʳ-< (x86-32-frame-base frame) (*-monoˡ-< word-size k₁<k₂)

-- | Bounded frame disjointness: slot of f₁ ≠ slot of f₂
-- when the slot stays within the frame's bounds.
x86-32-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ x86-32-≺ f₂ →
  x86-32-slot-addr f₁ k₁ < x86-32-frame-base f₂ →  -- Slot is within frame bounds
  x86-32-slot-addr f₁ k₁ ≢ x86-32-slot-addr f₂ k₂
x86-32-frame-disjoint-bounded f₁ f₂ k₁ k₂ _ slot<f₂ eq =
  <⇒≢ slot₁<slot₂ eq
  where
    -- slot-addr f₂ k₂ ≥ frame-base f₂ (slots grow upward)
    slot₂≥f₂ : x86-32-slot-addr f₂ k₂ ≥ x86-32-frame-base f₂
    slot₂≥f₂ = slot-addr-≥-base (frame-sp f₂) k₂

    -- Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂
    slot₁<slot₂ : x86-32-slot-addr f₁ k₁ < x86-32-slot-addr f₂ k₂
    slot₁<slot₂ = <-≤-trans slot<f₂ slot₂≥f₂

-- | Slot within capacity is below caller frame when gap is sufficient
x86-32-slot-within-capacity-bound : ∀ frame caller-frame slot capacity →
  slot < capacity →
  x86-32-slot-addr frame capacity ≤ x86-32-frame-base caller-frame →
  x86-32-slot-addr frame slot < x86-32-frame-base caller-frame
x86-32-slot-within-capacity-bound frame caller-frame slot capacity slot<cap gap-sufficient =
  <-≤-trans slot<cap-addr gap-sufficient
  where
    slot<cap-addr : x86-32-slot-addr frame slot < x86-32-slot-addr frame capacity
    slot<cap-addr = x86-32-slot-addr-mono-< frame slot capacity slot<cap

-- | Frame disjointness with capacity bound
-- When k₁ < capacity and frame gap is sufficient, slots are disjoint.
x86-32-frame-disjoint-with-capacity : ∀ f₁ f₂ k₁ k₂ capacity →
  f₁ x86-32-≺ f₂ →
  k₁ < capacity →
  x86-32-slot-addr f₁ capacity ≤ x86-32-frame-base f₂ →
  x86-32-slot-addr f₁ k₁ ≢ x86-32-slot-addr f₂ k₂
x86-32-frame-disjoint-with-capacity f₁ f₂ k₁ k₂ capacity f₁<f₂ k₁<cap gap-sufficient =
  x86-32-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot-bound
  where
    slot-bound : x86-32-slot-addr f₁ k₁ < x86-32-frame-base f₂
    slot-bound = x86-32-slot-within-capacity-bound f₁ f₂ k₁ capacity k₁<cap gap-sufficient

------------------------------------------------------------------------
-- Frame movement: the callee frame sits `n` slots DOWN (the prologue's
-- `sub sp, n·word`) and `n` slots DEEPER. The stack region is
-- downward-closed, so the address is total; at the floor it stops at zero,
-- but the depth does not. `n + d` rather than `d + n`, so a shift by zero is
-- the frame itself by definition.
------------------------------------------------------------------------

x86-32-shift-frame : X86-32Frame → ℕ → X86-32Frame
x86-32-shift-frame (sp , d) n =
  ( stack-addr (sp-addr sp ∸ n * word-size)
               (stack-sub-preserves' (sp-addr sp) (n * word-size) (in-stack sp))
  , n + d )

-- | THE LAW plan 0.124 is for: a shift of at least one slot is strictly
-- further, for every frame, the floor included. By the depth alone.
x86-32-shift-≺ : ∀ f n → 0 < n → x86-32-shift-frame f n x86-32-≺ f
x86-32-shift-≺ (sp , d) (suc n) _ = inj₁ (s≤s (m≤n+m d n))

x86-32-shift-below : ∀ {f′ f} n → f′ x86-32-≺ f → x86-32-shift-frame f′ n x86-32-≺ f
x86-32-shift-below {_ , d′} zero    h                  = h
x86-32-shift-below {_ , d′} (suc n) (inj₁ d<d′)        = inj₁ (<-≤-trans d<d′ (m≤n+m d′ (suc n)))
x86-32-shift-below {_ , d′} (suc n) (inj₂ (refl , _))  = inj₁ (s≤s (m≤n+m d′ n))

------------------------------------------------------------------------
-- x86-32 FrameSemantics Instance
------------------------------------------------------------------------

-- Plan 0.105: the machine is a function of the program's interpretation (what
-- an FFI SigOp gives back), as the meaning is.
x86-32-frame-semantics : Interp → FrameSemantics
x86-32-frame-semantics ι = record
  { fs-interp = ι
  ; Frame = X86-32Frame
  ; _≟F_ = _x86-32-≟F_
  ; frame-base = x86-32-frame-base
  ; slot-addr = x86-32-slot-addr
  ; shift-frame = x86-32-shift-frame
  ; frame-word = word-size
  -- plan 0.74 J6: the word is at least one byte, so the target's Int width
  -- is at least one bit — which is what the literal exactness theorem needs.
  ; frame-word-pos = s≤s z≤n
  ; slot-addr-linear = λ f k → refl
  ; shift-base = λ f n → refl
  -- Plan 0.73 (D113): x86-32 keeps floats in a 32-bit GPR: a `binary64` immediate would not fit
-- a word, so this target lays a `Float` out as single precision.
  ; float-format = binary32
  ; slot-zero-at-base = x86-32-slot-zero-at-base
  ; slot-injective = x86-32-slot-injective
  ; _≺_ = _x86-32-≺_
  ; ≺-trans = λ {f₁} {f₂} {f₃} → x86-32-≺-trans {f₁} {f₂} {f₃}
  ; ≺-irrefl = λ {f} → x86-32-≺-irrefl {f}
  ; ≺-compare = x86-32-≺-compare
  ; shift-≺ = x86-32-shift-≺
  ; shift-below = λ {f′} {f} → x86-32-shift-below {f′} {f}
  ; frame-disjoint-bounded = x86-32-frame-disjoint-bounded
  }
