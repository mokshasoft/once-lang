------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackCapacityBase
--
-- Base definitions for stack capacity that don't depend on IR.
-- Split from StackInstantiation to break circular dependency:
--   Foundation → PrimContract → StackCapacity (this module)
--
-- This module provides:
--   - StackCapacity record
--   - Capacity preservation lemmas
--   - Basic capacity arithmetic
--
-- IR-dependent functions (ir-rsp-delta, ir-stack-requirement, etc.)
-- remain in StackInstantiation.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackCapacityBase where

open import Once.Type

-- Import slot-size and slots from Syntax (single source of truth)
open import Once.Backend.X86.Syntax public using (slot-size; slots)
open import Once.Backend.X86.Syntax hiding (slot-size; slots)

open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import region abstractions (interval-based model)
open import Once.Backend.X86.Layout
  using (InStack; stack-sub-preserves)

open import Data.Unit using (⊤; tt)

-- Arithmetic imports
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≤?_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; ∸-+-assoc; +-∸-assoc; m+n∸n≡m; ≤-trans; +-monoʳ-≤; +-monoʳ-<; m∸n≤m; ≤-refl; ∸-monoʳ-<; m≤n⇒m∸n≡0; ≰⇒>; <⇒≤; <⇒≢; ⊔-mono-≤; m∸n+n≡m; m≤n⊔m; m≤m+n; m≤m⊔n; n≤1+n; ≤-<-trans; +-cancelʳ-<)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Stack Capacity (X86 instantiation)
------------------------------------------------------------------------

-- | Stack capacity: X86-specific proof that stack can accommodate n slots.
-- Each slot is 8 bytes (one word on x86-64).
--
-- This type contains ARITHMETIC in its fields (rsp > n *ℕ slot-size).
-- The proof layer should not use these fields directly.
-- Instead, use the abstract interface functions below.
record StackCapacity (s : State) (n : ℕ) : Set where
  field
    -- rsp points to stack region (interval membership)
    rsp-in-stack : InStack (readReg (regs s) rsp)

    -- rsp has sufficient space for n slots (concrete X86 bound)
    rsp-sufficient : readReg (regs s) rsp > n *ℕ slot-size

    -- After allocating k slots (k ≤ n), still in stack region
    capacity-maintained : ∀ k → k ≤ n →
      InStack (readReg (regs s) rsp ∸ (k *ℕ slot-size))

open StackCapacity public

------------------------------------------------------------------------
-- Capacity Operations (arithmetic-heavy)
------------------------------------------------------------------------

-- | Capacity is preserved when rsp doesn't change
capacity-preserved-rsp-unchanged : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackCapacity s' n
capacity-preserved-rsp-unchanged s s' n cap rsp-eq = record
  { rsp-in-stack = subst InStack (sym rsp-eq) (rsp-in-stack cap)
  ; rsp-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n →
      subst InStack (sym (cong (_∸ (k *ℕ slot-size)) rsp-eq))
            (capacity-maintained cap k k≤n)
  }

-- | After push (rsp -= slot-size), capacity decreases by 1
capacity-after-push : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc n) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size →
  StackCapacity s' n
capacity-after-push s s' n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : InStack new-rsp
    rsp'-in-stack = subst InStack (sym rsp-eq) (capacity-maintained cap 1 (s≤s z≤n))

    rsp'-sufficient : new-rsp > n *ℕ slot-size
    rsp'-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) sub-lemma
      where
        old-bound : old-rsp > slot-size +ℕ n *ℕ slot-size
        old-bound = rsp-sufficient cap

        slot-size≤old : slot-size ≤ old-rsp
        slot-size≤old = <⇒≤ (≤-<-trans (m≤m+n slot-size (n *ℕ slot-size)) old-bound)

        old-rsp-eq : (old-rsp ∸ slot-size) +ℕ slot-size ≡ old-rsp
        old-rsp-eq = m∸n+n≡m slot-size≤old

        old-bound' : old-rsp > n *ℕ slot-size +ℕ slot-size
        old-bound' = subst (old-rsp >_) (+-comm slot-size (n *ℕ slot-size)) old-bound

        sub-lemma : old-rsp ∸ slot-size > n *ℕ slot-size
        sub-lemma = +-cancelʳ-< slot-size (n *ℕ slot-size) (old-rsp ∸ slot-size) bound-step
          where
            bound-step : n *ℕ slot-size +ℕ slot-size < (old-rsp ∸ slot-size) +ℕ slot-size
            bound-step = subst (n *ℕ slot-size +ℕ slot-size <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → InStack (new-rsp ∸ (k *ℕ slot-size))
    cap-maintained k k≤n =
      let 1+k≤sn : (1 +ℕ k) ≤ suc n
          1+k≤sn = s≤s k≤n
          old-cap-at-1+k : InStack (old-rsp ∸ ((1 +ℕ k) *ℕ slot-size))
          old-cap-at-1+k = capacity-maintained cap (1 +ℕ k) 1+k≤sn
          step1 : (old-rsp ∸ slot-size) ∸ (k *ℕ slot-size) ≡ old-rsp ∸ (slot-size +ℕ k *ℕ slot-size)
          step1 = ∸-+-assoc old-rsp slot-size (k *ℕ slot-size)
          arith-eq : slot-size +ℕ k *ℕ slot-size ≡ (1 +ℕ k) *ℕ slot-size
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ slot-size) ≡ old-rsp ∸ ((1 +ℕ k) *ℕ slot-size)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ slot-size)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in subst InStack (sym addr-eq) old-cap-at-1+k

------------------------------------------------------------------------
-- RSP Bound Conversions
------------------------------------------------------------------------

-- | General conversion: rsp > n*8 gives StackCapacity s n
rsp-bound-to-capacity : ∀ (n : ℕ) (s : State) →
  InStack (readReg (regs s) rsp) →
  readReg (regs s) rsp > n *ℕ slot-size →
  StackCapacity s n
rsp-bound-to-capacity n s rsp-in-stack rsp-bound = record
  { rsp-in-stack = rsp-in-stack
  ; rsp-sufficient = rsp-bound
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (*-monoˡ-≤; <⇒≤; ≤-<-trans)
    rsp-val = readReg (regs s) rsp
    k*slot≤rsp : ∀ k → k ≤ n → k *ℕ slot-size ≤ rsp-val
    k*slot≤rsp k k≤n = <⇒≤ (≤-<-trans (*-monoˡ-≤ slot-size k≤n) rsp-bound)
    cap-maintained : ∀ k → k ≤ n → InStack (rsp-val ∸ (k *ℕ slot-size))
    cap-maintained k k≤n = stack-sub-preserves rsp-val (k *ℕ slot-size) rsp-in-stack (k*slot≤rsp k k≤n)

-- | Convert StackCapacity back to concrete bound (for compatibility)
-- two-push-offset = 16 = 2 * slot-size
two-push-offset : ℕ
two-push-offset = slots 2

capacity-2-to-rsp-bound : ∀ (s : State) →
  StackCapacity s 2 →
  readReg (regs s) rsp > two-push-offset
capacity-2-to-rsp-bound s cap = rsp-sufficient cap

------------------------------------------------------------------------
-- Capacity Weakening
------------------------------------------------------------------------

-- | Weaken capacity: if we have capacity for n slots, we have capacity for m ≤ n
capacity-weaken : ∀ (s : State) (m n : ℕ) →
  m ≤ n →
  StackCapacity s n →
  StackCapacity s m
capacity-weaken s m n m≤n cap = record
  { rsp-in-stack = rsp-in-stack cap
  ; rsp-sufficient = ≤-trans (s≤s (slots-mono m≤n)) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤m → capacity-maintained cap k (≤-trans k≤m m≤n)
  }
  where
    slots-mono : ∀ {a b} → a ≤ b → a *ℕ slot-size ≤ b *ℕ slot-size
    slots-mono {zero} _ = z≤n
    slots-mono {suc a} {suc b} (s≤s a≤b) = +-monoʳ-≤ slot-size (slots-mono a≤b)

------------------------------------------------------------------------
-- Slot Monotonicity
------------------------------------------------------------------------

-- | Slot monotonicity for ≤ (follows from slots being multiplication)
-- Useful for deriving smaller bounds: a ≤ b → slots a ≤ slots b
slots-mono-≤ : ∀ {a b} → a ≤ b → slots a ≤ slots b
slots-mono-≤ {zero} {b} _ = z≤n
slots-mono-≤ {suc a} {suc b} (s≤s a≤b) = +-monoʳ-≤ slot-size (slots-mono-≤ a≤b)

------------------------------------------------------------------------
-- RSP Bound Preservation
------------------------------------------------------------------------

-- | rsp > bound preservation when rsp is unchanged (generic version)
rsp-bound-preserved-unchanged : ∀ (bound : ℕ) (s s' : State) →
  readReg (regs s) rsp > bound →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > bound
rsp-bound-preserved-unchanged bound s s' rsp-sufficient rsp-eq = subst (_> bound) (sym rsp-eq) rsp-sufficient
