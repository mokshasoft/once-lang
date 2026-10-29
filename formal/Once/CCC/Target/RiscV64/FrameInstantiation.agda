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
open import Once.Spec.Float.Dyadic using (binary64)
open import Once.Memory.MemoryLayoutSemantics using (Addr)

-- Import RISC-V 64 Layout for StackPointer and slot operations
open import Once.CCC.Target.RiscV64.Layout using (StackPointer; slot-addr; offset-distinct; slot-addr-≥-base; InStack; in-stack; _≟SP_; stack-addr-inj)
open import Once.CCC.Target.RiscV64.StackGrowth using (word-size)
open import Once.CCC.Target.RiscV64.Layout using (stack-addr; stack-sub-preserves') renaming (addr to sp-addr)

------------------------------------------------------------------------
-- riscv64 Frame Type (plan 0.124 S1)
--
-- A Frame is a StackPointer TAGGED WITH ITS DEPTH: the number of slots it
-- sits below the entry frame. The address is where the frame lives; the
-- depth is which frame it is.
--
-- They come apart only at the stack floor. `sp ∸ n·word` stops at zero, so a
-- call made from the lowest frame used to get its caller's own frame back,
-- and the callee's `c-thunk` cleared the caller's live slots (plan 0.124 §3a).
-- The depth never stops, so the callee's frame is always new and always
-- `≺` its caller's (`rv64-shift-≺`). The abstract stack has no floor; running
-- out of stack is the concrete machine's outcome, as running out of heap is.
--
-- Every address law reads the address only, so it is unchanged.
------------------------------------------------------------------------

RV64Frame : Set
RV64Frame = StackPointer × ℕ

frame-sp : RV64Frame → StackPointer
frame-sp = proj₁

frame-depth : RV64Frame → ℕ
frame-depth = proj₂

------------------------------------------------------------------------
-- Decidable Equality for Frames
--
-- Two frames are equal iff their addresses and their depths are equal.
------------------------------------------------------------------------

_rv64-≟F_ : DecidableEquality RV64Frame
(sp₁ , d₁) rv64-≟F (sp₂ , d₂) with sp₁ ≟SP sp₂
... | no sp≢   = no λ { refl → sp≢ refl }
... | yes refl with d₁ ≟ d₂
...   | yes refl = yes refl
...   | no d≢    = no λ { refl → d≢ refl }

------------------------------------------------------------------------
-- Frame Base Address
------------------------------------------------------------------------

rv64-frame-base : RV64Frame → Addr
rv64-frame-base f = sp-addr (frame-sp f)

------------------------------------------------------------------------
-- Slot Addressing
--
-- Slots grow upward from frame base: slot k at base + k * word-size
------------------------------------------------------------------------

-- | Direct definition of riscv64 slot address: base + k * word-size
-- This gives definitional reduction, unlike using the abstract slot-addr.
rv64-slot-addr : RV64Frame → ℕ → Addr
rv64-slot-addr f k = rv64-frame-base f + k * word-size

-- | Proof that rv64-slot-addr equals the abstract slot-addr
rv64-slot-addr-eq : ∀ f k → rv64-slot-addr f k ≡ slot-addr (frame-sp f) k
rv64-slot-addr-eq f k = refl  -- Both compute to sp-addr + k * word-size

rv64-slot-zero-at-base : ∀ f → rv64-slot-addr f zero ≡ rv64-frame-base f
rv64-slot-zero-at-base f = Data.Nat.Properties.+-identityʳ (rv64-frame-base f)
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
  trans (cong (rv64-frame-base f +_) (+-comm word-size (k * word-size)))
        (sym (+-assoc (rv64-frame-base f) (k * word-size) word-size))
  where open import Data.Nat.Properties using (+-assoc; +-comm)

rv64-slot-injective : ∀ f k₁ k₂ → k₁ ≢ k₂ → rv64-slot-addr f k₁ ≢ rv64-slot-addr f k₂
rv64-slot-injective f = offset-distinct (frame-sp f)

------------------------------------------------------------------------
-- Frame Ordering
--
-- f₁ ≺ f₂ means f₁ is "further" in stack growth direction: DEEPER, or at
-- the same depth and lower. Depth decides, so a callee is `≺` its caller
-- even where the address cannot say so (the floor). The address breaks
-- ties, which keeps the order total.
------------------------------------------------------------------------

_rv64-≺_ : RV64Frame → RV64Frame → Set
f₁ rv64-≺ f₂ = frame-depth f₂ < frame-depth f₁
            ⊎ (frame-depth f₁ ≡ frame-depth f₂ × rv64-frame-base f₁ < rv64-frame-base f₂)

-- | Frame ordering is transitive (lexicographic on depth, then address)
rv64-≺-trans : ∀ {f₁ f₂ f₃} → f₁ rv64-≺ f₂ → f₂ rv64-≺ f₃ → f₁ rv64-≺ f₃
rv64-≺-trans (inj₁ d₂<d₁)        (inj₁ d₃<d₂)        = inj₁ (<-trans d₃<d₂ d₂<d₁)
rv64-≺-trans (inj₁ d₂<d₁)        (inj₂ (refl , _))   = inj₁ d₂<d₁
rv64-≺-trans (inj₂ (refl , _))   (inj₁ d₃<d₂)        = inj₁ d₃<d₂
rv64-≺-trans (inj₂ (refl , a₁<a₂)) (inj₂ (refl , a₂<a₃)) = inj₂ (refl , <-trans a₁<a₂ a₂<a₃)

-- | Frame ordering is irreflexive
rv64-≺-irrefl : ∀ {f} → f rv64-≺ f → ⊥
rv64-≺-irrefl (inj₁ d<d)       = <-irrefl refl d<d
rv64-≺-irrefl (inj₂ (_ , a<a)) = <-irrefl refl a<a

-- | Frame ordering is trichotomous (lexicographic on two total orders)
rv64-≺-compare : ∀ f₁ f₂ → (f₁ rv64-≺ f₂) ⊎ (f₁ ≡ f₂) ⊎ (f₂ rv64-≺ f₁)
rv64-≺-compare (sp₁ , d₁) (sp₂ , d₂) with <-cmp d₂ d₁
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
rv64-slot-addr-mono-< : ∀ frame k₁ k₂ →
  k₁ < k₂ →
  rv64-slot-addr frame k₁ < rv64-slot-addr frame k₂
rv64-slot-addr-mono-< frame k₁ k₂ k₁<k₂ =
  +-monoʳ-< (rv64-frame-base frame) (*-monoˡ-< word-size k₁<k₂)

-- | Bounded frame disjointness: slot of f₁ ≠ slot of f₂
-- when the slot stays within the frame's bounds.
rv64-frame-disjoint-bounded : ∀ f₁ f₂ k₁ k₂ →
  f₁ rv64-≺ f₂ →
  rv64-slot-addr f₁ k₁ < rv64-frame-base f₂ →  -- Slot is within frame bounds
  rv64-slot-addr f₁ k₁ ≢ rv64-slot-addr f₂ k₂
rv64-frame-disjoint-bounded f₁ f₂ k₁ k₂ _ slot<f₂ eq =
  <⇒≢ slot₁<slot₂ eq
  where
    -- slot-addr f₂ k₂ ≥ frame-base f₂ (slots grow upward)
    slot₂≥f₂ : rv64-slot-addr f₂ k₂ ≥ rv64-frame-base f₂
    slot₂≥f₂ = slot-addr-≥-base (frame-sp f₂) k₂

    -- Therefore slot-addr f₁ k₁ < slot-addr f₂ k₂
    slot₁<slot₂ : rv64-slot-addr f₁ k₁ < rv64-slot-addr f₂ k₂
    slot₁<slot₂ = <-≤-trans slot<f₂ slot₂≥f₂

-- | Slot within capacity is below caller frame when gap is sufficient
rv64-slot-within-capacity-bound : ∀ frame caller-frame slot capacity →
  slot < capacity →
  rv64-slot-addr frame capacity ≤ rv64-frame-base caller-frame →
  rv64-slot-addr frame slot < rv64-frame-base caller-frame
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
  rv64-slot-addr f₁ capacity ≤ rv64-frame-base f₂ →
  rv64-slot-addr f₁ k₁ ≢ rv64-slot-addr f₂ k₂
rv64-frame-disjoint-with-capacity f₁ f₂ k₁ k₂ capacity f₁<f₂ k₁<cap gap-sufficient =
  rv64-frame-disjoint-bounded f₁ f₂ k₁ k₂ f₁<f₂ slot-bound
  where
    slot-bound : rv64-slot-addr f₁ k₁ < rv64-frame-base f₂
    slot-bound = rv64-slot-within-capacity-bound f₁ f₂ k₁ capacity k₁<cap gap-sufficient

------------------------------------------------------------------------
-- Frame movement: the callee frame sits `n` slots DOWN (the prologue's
-- `sub sp, n·word`) and `n` slots DEEPER. The stack region is
-- downward-closed, so the address is total; at the floor it stops at zero,
-- but the depth does not. `n + d` rather than `d + n`, so a shift by zero is
-- the frame itself by definition.
------------------------------------------------------------------------

rv64-shift-frame : RV64Frame → ℕ → RV64Frame
rv64-shift-frame (sp , d) n =
  ( stack-addr (sp-addr sp ∸ n * word-size)
               (stack-sub-preserves' (sp-addr sp) (n * word-size) (in-stack sp))
  , n + d )

-- | THE LAW plan 0.124 is for: a shift of at least one slot is strictly
-- further, for every frame, the floor included. By the depth alone.
rv64-shift-≺ : ∀ f n → 0 < n → rv64-shift-frame f n rv64-≺ f
rv64-shift-≺ (sp , d) (suc n) _ = inj₁ (s≤s (m≤n+m d n))

rv64-shift-below : ∀ {f′ f} n → f′ rv64-≺ f → rv64-shift-frame f′ n rv64-≺ f
rv64-shift-below {_ , d′} zero    h                  = h
rv64-shift-below {_ , d′} (suc n) (inj₁ d<d′)        = inj₁ (<-≤-trans d<d′ (m≤n+m d′ (suc n)))
rv64-shift-below {_ , d′} (suc n) (inj₂ (refl , _))  = inj₁ (s≤s (m≤n+m d′ n))

------------------------------------------------------------------------
-- RISC-V 64 FrameSemantics Instance
------------------------------------------------------------------------

-- Plan 0.105: the machine is a function of the program's interpretation (what
-- an FFI SigOp gives back), as the meaning is.
rv64-frame-semantics : Interp → FrameSemantics
rv64-frame-semantics ι = record
  { fs-interp = ι
  ; Frame = RV64Frame
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
  ; ≺-trans = λ {f₁} {f₂} {f₃} → rv64-≺-trans {f₁} {f₂} {f₃}
  ; ≺-irrefl = λ {f} → rv64-≺-irrefl {f}
  ; ≺-compare = rv64-≺-compare
  ; shift-≺ = rv64-shift-≺
  ; shift-below = λ {f′} {f} → rv64-shift-below {f′} {f}
  ; frame-disjoint-bounded = rv64-frame-disjoint-bounded
  }
