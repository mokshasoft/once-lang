------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInstantiation
--
-- X86 instantiation layer: concrete arithmetic for stack operations.
--
-- This module contains ALL computational arithmetic (∸, +ℕ, *ℕ 8) that
-- proves the abstract StackInvariant properties for the X86 backend.
--
-- DESIGN (D041 Architecture):
-- - StackInvariant.agda: abstract types (R15Status, RbpInvariant) - NO arithmetic
-- - StackInstantiation.agda (this file): arithmetic proofs, imports StackInvariant
-- - IR/*.agda (proof layer): imports this module for all stack operations
--
-- The proof layer should use abstract interfaces like:
--   apply-frame-1, abstract-to-rsp-8-in-stack
-- These hide the arithmetic (rsp ∸ 8) behind region-based types.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInstantiation where

open import Once.Type
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import and re-export abstract types from StackInvariant
open import Once.Backend.X86.Correct.StackInvariant public
  using (R15Status; r15-unused; r15-in-heap; r15-in-code; r15-in-stack;
         RbpInvariant; open RbpInvariant;
         StackInvariant; FrameEvidenceFor;
         stack-write-preserves-heap-r15; stack-write-preserves-code-r15;
         stack-write-preserves-unused-r15; stack-write-preserves-instack-r15;
         stack-write-preserves-r15;
         stack-inv-preserved-unchanged; stack-inv-preserved-r15-unchanged;
         stack-inv-for-code-ptr)

-- Import region abstractions
open import Once.Backend.Common.MemoryRegions
  using (Region; stack; heap; code; Addr; region-of;
         regions-disjoint; stack≢heap; stack≢code;
         stack-heap-disjoint; stack-code-disjoint;
         zero-not-in-stack; pc-in-code;
         stack-sub-preserves-region;
         StackPointer; slot-addr; sp-distinct; offset-distinct;
         frames-disjoint-slots; slot-in-stack; slot-addr-0-is-base;
         slot-addr-1-is-base+8)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr; in-stack to sp-in-stack)
open import Data.Unit using (⊤; tt)

-- Arithmetic imports (the instantiation layer uses these)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; ∸-+-assoc; +-∸-assoc; m+n∸n≡m; ≤-trans; +-monoʳ-≤; m∸n≤m; ≤-refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Stack Capacity (X86 instantiation)
------------------------------------------------------------------------

-- | Stack capacity: X86-specific proof that stack can accommodate n slots.
-- Each slot is 8 bytes (one word on x86-64).
--
-- This type contains ARITHMETIC in its fields (rsp > n *ℕ 8).
-- The proof layer should not use these fields directly.
-- Instead, use the abstract interface functions below.
record StackCapacity (s : State) (n : ℕ) : Set where
  field
    -- rsp points to stack region
    rsp-in-stack : region-of (readReg (regs s) rsp) ≡ stack

    -- rsp has sufficient space for n slots (concrete X86 bound)
    rsp-sufficient : readReg (regs s) rsp > n *ℕ 8

    -- After allocating k slots (k ≤ n), still in stack region
    capacity-maintained : ∀ k → k ≤ n →
      region-of (readReg (regs s) rsp ∸ (k *ℕ 8)) ≡ stack

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
  { rsp-in-stack = trans (cong region-of rsp-eq) (rsp-in-stack cap)
  ; rsp-sufficient = subst (_> n *ℕ 8) (sym rsp-eq) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n →
      trans (cong (λ r → region-of (r ∸ (k *ℕ 8))) rsp-eq)
            (capacity-maintained cap k k≤n)
  }

-- | After push (rsp -= 8), capacity decreases by 1
capacity-after-push : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc n) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 8 →
  StackCapacity s' n
capacity-after-push s s' n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (m+n∸n≡m; m∸n+n≡m; <⇒≤; +-monoʳ-<)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 1 (s≤s z≤n))

    rsp'-sufficient : new-rsp > n *ℕ 8
    rsp'-sufficient = subst (_> n *ℕ 8) (sym rsp-eq) sub-lemma
      where
        open import Data.Nat.Properties using (≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

        old-bound : old-rsp > 8 +ℕ n *ℕ 8
        old-bound = rsp-sufficient cap

        8≤old : 8 ≤ old-rsp
        8≤old = <⇒≤ (≤-<-trans (m≤m+n 8 (n *ℕ 8)) old-bound)

        old-rsp-eq : (old-rsp ∸ 8) +ℕ 8 ≡ old-rsp
        old-rsp-eq = m∸n+n≡m 8≤old

        old-bound' : old-rsp > n *ℕ 8 +ℕ 8
        old-bound' = subst (old-rsp >_) (+-comm 8 (n *ℕ 8)) old-bound

        sub-lemma : old-rsp ∸ 8 > n *ℕ 8
        sub-lemma = +-cancelʳ-< 8 (n *ℕ 8) (old-rsp ∸ 8) bound-step
          where
            bound-step : n *ℕ 8 +ℕ 8 < (old-rsp ∸ 8) +ℕ 8
            bound-step = subst (n *ℕ 8 +ℕ 8 <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n =
      let 1+k≤sn : (1 +ℕ k) ≤ suc n
          1+k≤sn = s≤s k≤n
          old-cap-at-1+k : region-of (old-rsp ∸ ((1 +ℕ k) *ℕ 8)) ≡ stack
          old-cap-at-1+k = capacity-maintained cap (1 +ℕ k) 1+k≤sn
          step1 : (old-rsp ∸ 8) ∸ (k *ℕ 8) ≡ old-rsp ∸ (8 +ℕ k *ℕ 8)
          step1 = ∸-+-assoc old-rsp 8 (k *ℕ 8)
          arith-eq : 8 +ℕ k *ℕ 8 ≡ (1 +ℕ k) *ℕ 8
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ 8) ≡ old-rsp ∸ ((1 +ℕ k) *ℕ 8)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ 8)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-1+k

-- | After pop (rsp += 8), capacity increases by 1
capacity-after-pop : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ 8 →
  region-of (readReg (regs s') rsp) ≡ stack →
  StackCapacity s' (suc n)
capacity-after-pop s s' n cap rsp-eq new-rsp-in-stack = record
  { rsp-in-stack = new-rsp-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (+-monoʳ-<; +-comm)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-sufficient : new-rsp > (suc n) *ℕ 8
    rsp'-sufficient = subst (_> (suc n) *ℕ 8) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ 8 > n *ℕ 8 +ℕ 8
        step1 = +-monoˡ-< 8 (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ 8 > (suc n) *ℕ 8
        add-lemma = subst (old-rsp +ℕ 8 >_) (+-comm (n *ℕ 8) 8) step1

    cap-maintained : ∀ k → k ≤ suc n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained (suc k) (s≤s k≤n) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ 8)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ 8) ∸ (8 +ℕ k *ℕ 8) ≡ ((old-rsp +ℕ 8) ∸ 8) ∸ (k *ℕ 8)
        step1 = sym (∸-+-assoc (old-rsp +ℕ 8) 8 (k *ℕ 8))
        step2 : (old-rsp +ℕ 8) ∸ 8 ≡ old-rsp
        step2 = m+n∸n≡m old-rsp 8
        arith-eq : (old-rsp +ℕ 8) ∸ ((suc k) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        arith-eq = trans step1 (cong (_∸ (k *ℕ 8)) step2)
        addr-eq : new-rsp ∸ ((suc k) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        addr-eq = trans (cong (λ r → r ∸ ((suc k) *ℕ 8)) rsp-eq) arith-eq

-- | After sub rsp, 16 (rsp -= 16), capacity decreases by 2
capacity-after-alloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc (suc n)) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 16 →
  StackCapacity s' n
capacity-after-alloc-2-slots s s' n cap rsp-eq = record
  { rsp-in-stack = rsp'-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (m∸n+n≡m; <⇒≤; ≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 2 (s≤s (s≤s z≤n)))

    rsp'-sufficient : new-rsp > n *ℕ 8
    rsp'-sufficient = subst (_> n *ℕ 8) (sym rsp-eq) sub-lemma
      where
        old-bound : old-rsp > 16 +ℕ n *ℕ 8
        old-bound = rsp-sufficient cap

        16≤old : 16 ≤ old-rsp
        16≤old = <⇒≤ (≤-<-trans (m≤m+n 16 (n *ℕ 8)) old-bound)

        old-rsp-eq : (old-rsp ∸ 16) +ℕ 16 ≡ old-rsp
        old-rsp-eq = m∸n+n≡m 16≤old

        old-bound' : old-rsp > n *ℕ 8 +ℕ 16
        old-bound' = subst (old-rsp >_) (+-comm 16 (n *ℕ 8)) old-bound

        sub-lemma : old-rsp ∸ 16 > n *ℕ 8
        sub-lemma = +-cancelʳ-< 16 (n *ℕ 8) (old-rsp ∸ 16) bound-step
          where
            bound-step : n *ℕ 8 +ℕ 16 < (old-rsp ∸ 16) +ℕ 16
            bound-step = subst (n *ℕ 8 +ℕ 16 <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n =
      let 2+k≤ssn : (2 +ℕ k) ≤ suc (suc n)
          2+k≤ssn = s≤s (s≤s k≤n)
          old-cap-at-2+k : region-of (old-rsp ∸ ((2 +ℕ k) *ℕ 8)) ≡ stack
          old-cap-at-2+k = capacity-maintained cap (2 +ℕ k) 2+k≤ssn
          step1 : (old-rsp ∸ 16) ∸ (k *ℕ 8) ≡ old-rsp ∸ (16 +ℕ k *ℕ 8)
          step1 = ∸-+-assoc old-rsp 16 (k *ℕ 8)
          arith-eq : 16 +ℕ k *ℕ 8 ≡ (2 +ℕ k) *ℕ 8
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ 8) ≡ old-rsp ∸ ((2 +ℕ k) *ℕ 8)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ 8)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-2+k

-- | After add rsp, 16 (rsp += 16), capacity increases by 2
capacity-after-dealloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ 16 →
  region-of (readReg (regs s') rsp) ≡ stack →
  StackCapacity s' (suc (suc n))
capacity-after-dealloc-2-slots s s' n cap rsp-eq new-rsp-in-stack = record
  { rsp-in-stack = new-rsp-in-stack
  ; rsp-sufficient = rsp'-sufficient
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (+-monoʳ-<; +-comm; m≤m+n)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-sufficient : new-rsp > (suc (suc n)) *ℕ 8
    rsp'-sufficient = subst (_> (suc (suc n)) *ℕ 8) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ 16 > n *ℕ 8 +ℕ 16
        step1 = +-monoˡ-< 16 (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ 16 > (suc (suc n)) *ℕ 8
        add-lemma = subst (old-rsp +ℕ 16 >_) (+-comm (n *ℕ 8) 16) step1

    cap-maintained : ∀ k → k ≤ suc (suc n) → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained 1 _ = stack-sub-preserves-region new-rsp 8 new-rsp-in-stack 8≤new-rsp
      where
        open import Data.Nat.Properties using (<⇒≤; +-monoˡ-<; <-trans)
        rsp>0 : old-rsp > 0
        rsp>0 = ≤-trans (s≤s z≤n) (rsp-sufficient cap)
        step1 : old-rsp +ℕ 16 > 16
        step1 = +-monoˡ-< 16 rsp>0
        step2 : 16 > 8
        step2 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        new-rsp-bound : new-rsp > 8
        new-rsp-bound = subst (_> 8) (sym rsp-eq) (<-trans step2 step1)
        8≤new-rsp : 8 ≤ new-rsp
        8≤new-rsp = <⇒≤ new-rsp-bound
    cap-maintained (suc (suc k)) (s≤s (s≤s k≤n)) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ 8)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ 16) ∸ (16 +ℕ k *ℕ 8) ≡ ((old-rsp +ℕ 16) ∸ 16) ∸ (k *ℕ 8)
        step1 = sym (∸-+-assoc (old-rsp +ℕ 16) 16 (k *ℕ 8))
        step2 : (old-rsp +ℕ 16) ∸ 16 ≡ old-rsp
        step2 = m+n∸n≡m old-rsp 16
        arith-eq : (old-rsp +ℕ 16) ∸ ((suc (suc k)) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        arith-eq = trans step1 (cong (_∸ (k *ℕ 8)) step2)
        addr-eq : new-rsp ∸ ((suc (suc k)) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        addr-eq = trans (cong (λ r → r ∸ ((suc (suc k)) *ℕ 8)) rsp-eq) arith-eq

------------------------------------------------------------------------
-- Deriving Address Properties from Capacity
------------------------------------------------------------------------

-- | With capacity n ≥ 2, address rsp - 16 is in stack region
slot-2-addr-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  region-of (readReg (regs s) rsp ∸ 16) ≡ stack
slot-2-addr-in-stack s cap = capacity-maintained cap 2 (s≤s (s≤s z≤n))

-- | With capacity n ≥ 1, address rsp - 8 is in stack region
slot-1-addr-in-stack : ∀ (s : State) →
  StackCapacity s 1 →
  region-of (readReg (regs s) rsp ∸ 8) ≡ stack
slot-1-addr-in-stack s cap = capacity-maintained cap 1 (s≤s z≤n)

------------------------------------------------------------------------
-- Converting from rsp bounds to StackCapacity
------------------------------------------------------------------------

-- | General conversion: rsp > n*8 gives StackCapacity s n
rsp-bound-to-capacity : ∀ (s : State) (n : ℕ) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > n *ℕ 8 →
  StackCapacity s n
rsp-bound-to-capacity s n rsp-in-stack rsp-bound = record
  { rsp-in-stack = rsp-in-stack
  ; rsp-sufficient = rsp-bound
  ; capacity-maintained = cap-maintained
  }
  where
    open import Data.Nat.Properties using (*-monoˡ-≤; <⇒≤; ≤-<-trans)
    rsp-val = readReg (regs s) rsp
    k*8≤rsp : ∀ k → k ≤ n → k *ℕ 8 ≤ rsp-val
    k*8≤rsp k k≤n = <⇒≤ (≤-<-trans (*-monoˡ-≤ 8 k≤n) rsp-bound)
    cap-maintained : ∀ k → k ≤ n → region-of (rsp-val ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n = stack-sub-preserves-region rsp-val (k *ℕ 8) rsp-in-stack (k*8≤rsp k k≤n)

-- | Convert rsp > 16 to StackCapacity 2
rsp-to-capacity-2 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  StackCapacity s 2
rsp-to-capacity-2 s rsp-in-stack rsp-sufficient = rsp-bound-to-capacity s 2 rsp-in-stack rsp-sufficient

-- | Convert rsp > 32 to StackCapacity 4
rsp-to-capacity-4 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 32 →
  StackCapacity s 4
rsp-to-capacity-4 s rsp-in-stack rsp>32 = rsp-bound-to-capacity s 4 rsp-in-stack rsp>32

-- | Convert rsp > 40 to StackCapacity 5
rsp-to-capacity-5 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 40 →
  StackCapacity s 5
rsp-to-capacity-5 s rsp-in-stack rsp>40 = rsp-bound-to-capacity s 5 rsp-in-stack rsp>40

-- | Convert StackCapacity back to concrete bound (for compatibility)
capacity-2-to-rsp-bound : ∀ (s : State) →
  StackCapacity s 2 →
  readReg (regs s) rsp > 16
capacity-2-to-rsp-bound s cap = rsp-sufficient cap

-- | rsp > 16 preservation when rsp is unchanged
rsp-bound-preserved-unchanged : ∀ (s s' : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > 16
rsp-bound-preserved-unchanged s s' rsp-sufficient rsp-eq = subst (_> 16) (sym rsp-eq) rsp-sufficient

------------------------------------------------------------------------
-- Abstract Frame Creation
------------------------------------------------------------------------

-- | Create a StackPointer for a frame at offset k slots below current rsp.
make-frame-at-slot : ∀ {n} (s : State) → StackCapacity s n → (k : ℕ) → k ≤ n → StackPointer
make-frame-at-slot s cap k k≤n = record
  { addr = readReg (regs s) rsp ∸ (k *ℕ 8)
  ; in-stack = capacity-maintained cap k k≤n
  }

-- | The frame created at slot 0 has addr = current rsp
make-frame-at-slot-0-addr : ∀ {n} (s : State) (cap : StackCapacity s n) →
  sp-addr (make-frame-at-slot s cap 0 z≤n) ≡ readReg (regs s) rsp
make-frame-at-slot-0-addr s cap = refl

-- | Frame at slot 1 has addr = rsp - 8
make-frame-at-slot-1-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
  sp-addr (make-frame-at-slot s cap 1 (s≤s z≤n)) ≡ readReg (regs s) rsp ∸ 8
make-frame-at-slot-1-addr s cap = refl

-- | Frame at slot 2 has addr = rsp - 16
make-frame-at-slot-2-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc n))) →
  sp-addr (make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))) ≡ readReg (regs s) rsp ∸ 16
make-frame-at-slot-2-addr s cap = refl

-- | Frame at slot 3 has addr = rsp - 24
make-frame-at-slot-3-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc n)))) →
  sp-addr (make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))) ≡ readReg (regs s) rsp ∸ 24
make-frame-at-slot-3-addr s cap = refl

-- | Frame at slot 4 has addr = rsp - 32
make-frame-at-slot-4-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc n))))) →
  sp-addr (make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ readReg (regs s) rsp ∸ 32
make-frame-at-slot-4-addr s cap = refl

-- | Frame at slot 5 has addr = rsp - 40
make-frame-at-slot-5-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc (suc n)))))) →
  sp-addr (make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ≡ readReg (regs s) rsp ∸ 40
make-frame-at-slot-5-addr s cap = refl

-- | Frames at lower slot indices have higher addresses (stack grows down)
frame-at-lower-slot-≥ : ∀ {n} (s : State) (cap : StackCapacity s n) (k₁ k₂ : ℕ)
  (k₁≤n : k₁ ≤ n) (k₂≤n : k₂ ≤ n) →
  k₁ ≤ k₂ →
  sp-addr (make-frame-at-slot s cap k₁ k₁≤n) ≥ sp-addr (make-frame-at-slot s cap k₂ k₂≤n)
frame-at-lower-slot-≥ s cap k₁ k₂ k₁≤n k₂≤n k₁≤k₂ = ∸-monoʳ-≤ (readReg (regs s) rsp) (*-monoˡ-≤ 8 k₁≤k₂)
  where
    open import Data.Nat.Properties using (∸-monoʳ-≤; *-monoˡ-≤)

------------------------------------------------------------------------
-- Apply-specific Abstract Interface (D041-compliant)
------------------------------------------------------------------------

-- | Apply frame at slot 1 (one slot below rsp)
apply-frame-1 : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) → StackPointer
apply-frame-1 s cap = make-frame-at-slot s cap 1 (s≤s z≤n)

apply-frame-slot-0-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
                              region-of (slot-addr (apply-frame-1 s cap) 0) ≡ stack
apply-frame-slot-0-in-stack s cap = slot-in-stack (apply-frame-1 s cap) 0

-- | Bridge from abstract to concrete for Apply's push address (rsp - 8)
abstract-to-rsp-8-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
                             region-of (readReg (regs s) rsp ∸ 8) ≡ stack
abstract-to-rsp-8-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (apply-frame-1 s cap))
               (make-frame-at-slot-1-addr s cap))
        (apply-frame-slot-0-in-stack s cap)

------------------------------------------------------------------------
-- ThunkExec-specific Abstract Interface (D041-compliant)
------------------------------------------------------------------------

-- | Thunk frame at slot 2 (rsp - 16)
thunk-frame-2 : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc n))) → StackPointer
thunk-frame-2 s cap = make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))

-- | Bridge from abstract to concrete for (rsp - 16)
abstract-to-rsp-16-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc n))) →
                              region-of (readReg (regs s) rsp ∸ 16) ≡ stack
abstract-to-rsp-16-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (thunk-frame-2 s cap)) refl)
        (slot-in-stack (thunk-frame-2 s cap) 0)

-- | Thunk frame at slot 3 (rsp - 24)
thunk-frame-3 : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc n)))) → StackPointer
thunk-frame-3 s cap = make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))

-- | Bridge from abstract to concrete for (rsp - 24)
abstract-to-rsp-24-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc n)))) →
                              region-of (readReg (regs s) rsp ∸ 24) ≡ stack
abstract-to-rsp-24-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (thunk-frame-3 s cap)) refl)
        (slot-in-stack (thunk-frame-3 s cap) 0)

-- | Thunk frame at slot 4 (rsp - 32)
thunk-frame-4 : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc n))))) → StackPointer
thunk-frame-4 s cap = make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n))))

-- | Bridge from abstract to concrete for (rsp - 32)
abstract-to-rsp-32-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc n))))) →
                              region-of (readReg (regs s) rsp ∸ 32) ≡ stack
abstract-to-rsp-32-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (thunk-frame-4 s cap)) refl)
        (slot-in-stack (thunk-frame-4 s cap) 0)

-- | Thunk rbp frame at slot 2 >= new rsp at slot 4
thunk-rbp-frame-≥-new-rsp : ∀ (s : State) (cap : StackCapacity s 4) →
  sp-addr (make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))) ≥
  sp-addr (make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
thunk-rbp-frame-≥-new-rsp s cap =
  frame-at-lower-slot-≥ s cap 2 4 (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s (s≤s z≤n))))
                        (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Pair-specific Abstract Interface
------------------------------------------------------------------------

-- | Pair frame at slot 5 (rsp - 40)
pair-frame-0 : (s : State) (cap : StackCapacity s 5) → StackPointer
pair-frame-0 s cap = make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

pair-frame-slot-0-in-stack : (s : State) (cap : StackCapacity s 5) →
                             region-of (slot-addr (pair-frame-0 s cap) 0) ≡ stack
pair-frame-slot-0-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 0

pair-frame-slot-1-in-stack : (s : State) (cap : StackCapacity s 5) →
                             region-of (slot-addr (pair-frame-0 s cap) 1) ≡ stack
pair-frame-slot-1-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 1

-- | Pair rbp frame at slot 3 (rsp - 24)
pair-rbp-frame-≥-r15-frame : ∀ (s : State) (cap : StackCapacity s 5) →
  sp-addr (make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))) ≥
  sp-addr (make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
pair-rbp-frame-≥-r15-frame s cap =
  frame-at-lower-slot-≥ s cap 3 5 (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
                        (s≤s (s≤s (s≤s z≤n)))

-- | rsp - 40 is in stack region when we have capacity 5
pair-r15-in-stack : ∀ (s : State) →
  StackCapacity s 5 →
  region-of (readReg (regs s) rsp ∸ 40) ≡ stack
pair-r15-in-stack s cap = capacity-maintained cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- | (rsp - 40) + 8 is in stack region when we have capacity 5
pair-second-slot-in-stack : ∀ (s : State) →
  StackCapacity s 5 →
  region-of ((readReg (regs s) rsp ∸ 40) +ℕ 8) ≡ stack
pair-second-slot-in-stack s cap =
  subst (λ a → region-of a ≡ stack)
        (sym (alloc-5-slots-second-addr-eq rsp-val (cap-to-pair-setup-rsp-bound cap)))
        (capacity-maintained cap 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
  where
    open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <⇒≤)
    rsp-val = readReg (regs s) rsp
    cap-to-pair-setup-rsp-bound : StackCapacity s 5 → readReg (regs s) rsp ≥ 40
    cap-to-pair-setup-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    alloc-5-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ 40 → (rsp-val ∸ 40) +ℕ 8 ≡ rsp-val ∸ 32
    alloc-5-slots-second-addr-eq rsp-val rsp≥40 = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits-after-4-slots)
      where
        step1 : rsp-val ∸ 40 ≡ (rsp-val ∸ 32) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 32 8)
        word-fits-after-4-slots : 8 ≤ rsp-val ∸ 32
        word-fits-after-4-slots = ∸-monoˡ-≤ 32 rsp≥40

-- | Get StackCapacity for Pair setup from runtime rsp bound
pair-stack-capacity : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 40 →
  StackCapacity s 5
pair-stack-capacity = rsp-to-capacity-5

-- | Create StackInvariant for state after Pair setup
pair-setup-stack-inv : ∀ (s s-setup : State) →
  StackCapacity s 5 →
  readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ 40 →
  readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ 40 →
  StackInvariant s-setup
pair-setup-stack-inv s s-setup cap r15-eq rsp-eq =
  r15-in-stack pair-frame 0 r15-is-slot0 pair-frame-bound
  where
    base-in-stack : region-of (readReg (regs s) rsp ∸ 40) ≡ stack
    base-in-stack = pair-r15-in-stack s cap
    pair-frame : StackPointer
    pair-frame = record
      { addr = readReg (regs s) rsp ∸ 40
      ; in-stack = base-in-stack
      }
    r15-is-slot0 : readReg (regs s-setup) r15 ≡ slot-addr pair-frame 0
    r15-is-slot0 = trans r15-eq (sym (slot-addr-0-is-base pair-frame))
    pair-frame-bound : sp-addr pair-frame ≥ readReg (regs s-setup) rsp
    pair-frame-bound = subst (sp-addr pair-frame ≥_) (sym rsp-eq) ≤-refl

------------------------------------------------------------------------
-- Combined Region Lemmas for Stack Operations
------------------------------------------------------------------------

-- | After sub rsp 16, both write addresses (new-rsp and new-rsp+8) are in stack
alloc-2-slots-addrs-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ 16
  in (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ 8) ≡ stack)
alloc-2-slots-addrs-in-stack s cap =
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ 16
      write1-in-stack : region-of new-rsp ≡ stack
      write1-in-stack = slot-2-addr-in-stack s cap
      write2-in-stack : region-of (new-rsp +ℕ 8) ≡ stack
      write2-in-stack = subst (λ a → region-of a ≡ stack)
                              (sym (alloc-2-slots-second-addr-eq rsp-val (cap-to-inl-inr-rsp-bound cap)))
                              (slot-1-addr-in-stack s (capacity-weaken cap))
  in write1-in-stack , write2-in-stack
  where
    open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <-trans)
    cap-to-inl-inr-rsp-bound : StackCapacity s 2 → readReg (regs s) rsp ≥ 16
    cap-to-inl-inr-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    capacity-weaken : StackCapacity s 2 → StackCapacity s 1
    capacity-weaken cap2 = record
      { rsp-in-stack = rsp-in-stack cap2
      ; rsp-sufficient = <-trans rsp>8 (rsp-sufficient cap2)
      ; capacity-maintained = λ k k≤1 →
          capacity-maintained cap2 k (≤-trans k≤1 (s≤s z≤n))
      }
      where
        rsp>8 : 8 < 16
        rsp>8 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    alloc-2-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ 16 → (rsp-val ∸ 16) +ℕ 8 ≡ rsp-val ∸ 8
    alloc-2-slots-second-addr-eq rsp-val rsp≥16 = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits-after-1-slot)
      where
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        word-fits-after-1-slot : 8 ≤ rsp-val ∸ 8
        word-fits-after-1-slot = ∸-monoˡ-≤ 8 rsp≥16

-- | Stack writes at rsp - k*8 don't affect heap addresses
stack-write-disjoint-from-heap : ∀ (s : State) (n k : ℕ) (heap-addr : Addr) →
  StackCapacity s n →
  k ≤ n →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ (k *ℕ 8) ≢ heap-addr
stack-write-disjoint-from-heap s n k heap-addr cap k≤n heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ (k *ℕ 8)) heap-addr
                      (capacity-maintained cap k k≤n) heap-proof

------------------------------------------------------------------------
-- Combined State Invariant (R15Status + StackCapacity)
------------------------------------------------------------------------

-- | Combined invariant for x86 execution state
record AbstractStackInvariant (s : State) : Set where
  field
    r15-status : R15Status s
    capacity   : StackCapacity s 2

open AbstractStackInvariant public

-- | Create AbstractStackInvariant from StackInvariant and rsp bound
from-old-invariants : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  AbstractStackInvariant s
from-old-invariants s stack-inv rsp-in-stack rsp-sufficient = record
  { r15-status = stack-inv
  ; capacity = rsp-to-capacity-2 s rsp-in-stack rsp-sufficient
  }

------------------------------------------------------------------------
-- Address disjointness proofs using regions
------------------------------------------------------------------------

-- | Prove that stack write at (rsp - 16) doesn't affect r15
stack-write-slot-2-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ 16 ≢ readReg (regs s) r15
stack-write-slot-2-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (m∸n≤m; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ 16
    stack-addr-in-stack = slot-2-addr-in-stack s (capacity inv)
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m' (readReg (regs s) rsp) 16 (s≤s z≤n) (rsp-sufficient (capacity inv))
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ 16
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Similarly for (rsp - 8)
stack-write-slot-1-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ 8 ≢ readReg (regs s) r15
stack-write-slot-1-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (m∸n≤m; <-trans; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ 8
    stack-addr-in-stack = capacity-maintained (capacity inv) 1 (s≤s z≤n)
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    rsp>8 : readReg (regs s) rsp > 8
    rsp>8 = <-trans 8<16 (rsp-sufficient (capacity inv))
      where
        8<16 : 8 < 16
        8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m' (readReg (regs s) rsp) 8 (s≤s z≤n) rsp>8
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ 8
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Proof that stack writes don't affect heap-allocated data
stack-write-preserves-heap-data : ∀ (s : State) (heap-addr : Addr) →
  AbstractStackInvariant s →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ 16 ≢ heap-addr
stack-write-preserves-heap-data s heap-addr inv heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ 16) heap-addr
                      (slot-2-addr-in-stack s (capacity inv))
                      heap-proof

------------------------------------------------------------------------
-- Address disjointness from StackInvariant (legacy compatibility)
------------------------------------------------------------------------

-- | Prove (rsp - 16) and (rsp - 8) are different from r15
addr-diff-from-invariant : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-r15 = readReg (regs s) r15
  in (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
addr-diff-from-invariant s stack-inv rsp-in-stack rsp-suff = diff1 , diff2
  where
    open import Data.Nat.Properties using (m∸n≤m; <-trans; <⇒≢; <-≤-trans; ∸-monoˡ-≤)
    open import Data.Product using (proj₁; proj₂)
    rsp-val = readReg (regs s) rsp
    cap = rsp-to-capacity-2 s rsp-in-stack rsp-suff
    addrs-in-stack = alloc-2-slots-addrs-in-stack s cap
    write1-in-stack = proj₁ addrs-in-stack
    write2-in-stack = proj₂ addrs-in-stack
    stack-addr1 = rsp-val ∸ 16
    stack-addr2 = (rsp-val ∸ 16) +ℕ 8
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    addr1<rsp : stack-addr1 < rsp-val
    addr1<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-suff
    addr2<rsp : stack-addr2 < rsp-val
    addr2<rsp = subst (_< rsp-val) (sym addr2-eq) (m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8)
      where
        open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; <⇒≤)
        rsp>8 : rsp-val > 8
        rsp>8 = <-trans 8<16 rsp-suff
          where
            8<16 : 8 < 16
            8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        rsp≥16 : rsp-val ≥ 16
        rsp≥16 = <⇒≤ rsp-suff
        addr2-eq : stack-addr2 ≡ rsp-val ∸ 8
        addr2-eq = trans (cong (_+ℕ 8) (sym (∸-+-assoc rsp-val 8 8)))
                         (m∸n+n≡m (∸-monoˡ-≤ 8 rsp≥16))
    diff-helper : ∀ stack-addr → region-of stack-addr ≡ stack → stack-addr < rsp-val →
                  R15Status s → stack-addr ≢ readReg (regs s) r15
    diff-helper addr addr-in-stack addr<rsp (r15-unused r15≡0) =
      stack-write-preserves-unused-r15 s addr addr-in-stack r15≡0
    diff-helper addr addr-in-stack addr<rsp (r15-in-heap r15-heap) =
      stack-write-preserves-heap-r15 s addr addr-in-stack r15-heap
    diff-helper addr addr-in-stack addr<rsp (r15-in-code r15-code) =
      stack-write-preserves-code-r15 s addr addr-in-stack r15-code
    diff-helper addr addr-in-stack addr<rsp (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let addr<frame : addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = addr ; in-stack = addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq
    diff1 = diff-helper stack-addr1 write1-in-stack addr1<rsp stack-inv
    diff2 = diff-helper stack-addr2 write2-in-stack addr2<rsp stack-inv

------------------------------------------------------------------------
-- RbpInvariant address disjointness proofs
------------------------------------------------------------------------

-- | Prove (rsp - 16) and (rsp - 8) are different from rbp
rbp-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ 8) ≢ orig-rbp)
rbp-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp-diff-proof , rbp-diff-proof-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n≤m; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    rbp-diff-proof : new-rsp ≢ orig-rbp
    rbp-diff-proof = <⇒≢ new-rsp<rbp
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient
    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8
    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit
    rbp-diff-proof-2 : (new-rsp +ℕ 8) ≢ orig-rbp
    rbp-diff-proof-2 = subst (_≢ orig-rbp) (sym second-slot-eq) (<⇒≢ rsp-8<rbp)

-- | Prove (rsp - 16) and (rsp - 8) are different from (rbp + 8)
rbp+8-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp+8 = readReg (regs s) rbp +ℕ 8
  in (new-rsp ≢ orig-rbp+8) × ((new-rsp +ℕ 8) ≢ orig-rbp+8)
rbp+8-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp+8-diff-1 , rbp+8-diff-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n≤m; m≤m+n; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp
    orig-rbp+8 = orig-rbp +ℕ 8
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    new-rsp<rbp+8 : new-rsp < orig-rbp+8
    new-rsp<rbp+8 = ≤-trans new-rsp<rbp (m≤m+n orig-rbp 8)
    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 = <⇒≢ new-rsp<rbp+8
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient
    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8
    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))
    rsp-8<rbp+8 : rsp-val ∸ 8 < orig-rbp+8
    rsp-8<rbp+8 = ≤-trans rsp-8<rbp (m≤m+n orig-rbp 8)
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit
    rbp+8-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp+8
    rbp+8-diff-2 = subst (_≢ orig-rbp+8) (sym second-slot-eq) (<⇒≢ rsp-8<rbp+8)

-- | Combined rbp and rbp+8 disjointness for curry
curry-frame-disjoint-from-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ 8) ≢ orig-rbp) ×
     (new-rsp ≢ orig-rbp +ℕ 8) × ((new-rsp +ℕ 8) ≢ orig-rbp +ℕ 8)
curry-frame-disjoint-from-rbp s rbp-inv rsp-suff =
  let (d1 , d2) = rbp-addr-diff-from-invariant s rbp-inv rsp-suff
      (d3 , d4) = rbp+8-addr-diff-from-invariant s rbp-inv rsp-suff
  in d1 , d2 , d3 , d4

-- | Stack invariant frame bound update after 2-slot allocation
curry-stack-inv-frame-bound-update : ∀ (s s' : State) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 16 →
  (frame : StackPointer) →
  sp-addr frame ≥ readReg (regs s) rsp →
  sp-addr frame ≥ readReg (regs s') rsp
curry-stack-inv-frame-bound-update s s' rsp-eq frame old-bound =
  subst (sp-addr frame ≥_) (sym rsp-eq) (≤-trans (m∸n≤m (readReg (regs s) rsp) 16) old-bound)

-- | RbpInvariant preservation after 2-slot allocation
curry-rbp-inv-update : ∀ (s s' : State) →
  RbpInvariant s →
  readReg (regs s') rbp ≡ readReg (regs s) rbp →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 16 →
  RbpInvariant s'
curry-rbp-inv-update s s' rbp-inv rbp-eq rsp-eq = record
  { rbp-frame = RbpInvariant.rbp-frame rbp-inv
  ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
  ; frame-bound = curry-stack-inv-frame-bound-update s s' rsp-eq
                    (RbpInvariant.rbp-frame rbp-inv)
                    (RbpInvariant.frame-bound rbp-inv)
  }

-- | Ordering facts for curry: new-rsp < rbp and (new-rsp + 8) < rbp
curry-alloc-below-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp = readReg (regs s) rbp
  in (new-rsp < orig-rbp) × ((new-rsp +ℕ 8) < orig-rbp)
curry-alloc-below-rbp s rbp-inv rsp-sufficient = new-rsp<rbp , new-rsp+8<rbp
  where
    open import Data.Nat.Properties using (<-≤-trans; m∸n≤m; <⇒≤; +-monoʳ-<; m∸n+n≡m; ≤-<-trans; ∸-+-assoc; ∸-monoˡ-≤)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    16≤rsp : 16 ≤ rsp-val
    16≤rsp = <⇒≤ rsp-sufficient
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient
    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8
    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (n≤1+n)
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit
    new-rsp+8<rbp : (new-rsp +ℕ 8) < orig-rbp
    new-rsp+8<rbp = subst (_< orig-rbp) (sym second-slot-eq) rsp-8<rbp

-- | Prove curry allocation addresses are non-zero
curry-alloc-nonzero : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
  in (new-rsp ≢ 0) × ((new-rsp +ℕ 8) ≢ 0)
curry-alloc-nonzero s rsp-sufficient = diff-new-rsp , diff-new-rsp+8
  where
    open import Data.Nat.Properties using (<⇒≢; ∸-monoˡ-≤; <-trans; +-monoˡ-<)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    17≤rsp : 17 ≤ rsp-val
    17≤rsp = rsp-sufficient
    1≤new-rsp : 1 ≤ new-rsp
    1≤new-rsp = subst (1 ≤_) refl (∸-monoˡ-≤ 16 17≤rsp)
    0<new-rsp : 0 < new-rsp
    0<new-rsp = 1≤new-rsp
    0<new-rsp+8 : 0 < (new-rsp +ℕ 8)
    0<new-rsp+8 = <-trans (s≤s z≤n) (+-monoˡ-< 8 0<new-rsp)
    diff-new-rsp : new-rsp ≢ 0
    diff-new-rsp eq = <⇒≢ 0<new-rsp (sym eq)
    diff-new-rsp+8 : (new-rsp +ℕ 8) ≢ 0
    diff-new-rsp+8 eq = <⇒≢ 0<new-rsp+8 (sym eq)

------------------------------------------------------------------------
-- Apply helpers: 1-slot allocation (push r15)
------------------------------------------------------------------------

private
  m∸8<m : ∀ m → m > 8 → m ∸ 8 < m
  m∸8<m (suc m') (s≤s _) = s≤s (m∸n≤m m' 7)

-- | Prove 1-slot allocation address is below original rsp
apply-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s) rsp ∸ 8 < readReg (regs s) rsp
apply-alloc-below-rsp s rsp-sufficient = m∸8<m rsp-val rsp>8
  where
    rsp-val = readReg (regs s) rsp
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient

-- | Prove 1-slot allocation address is different from addresses >= rsp
apply-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  readReg (regs s) rsp ∸ 8 ≢ addr
apply-alloc-diff-from-above s rsp-sufficient addr addr≥rsp = <⇒≢ new-rsp<addr
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 8
    new-rsp<rsp = apply-alloc-below-rsp s rsp-sufficient
    new-rsp<addr : new-rsp < addr
    new-rsp<addr = <-≤-trans new-rsp<rsp addr≥rsp

-- | Prove rsp ≢ (rsp - 8) when rsp > 16
apply-rsp-diff-from-alloc : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s) rsp ≢ readReg (regs s) rsp ∸ 8
apply-rsp-diff-from-alloc s rsp-sufficient eq =
  <⇒≢ (apply-alloc-below-rsp s rsp-sufficient) (sym eq)
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Prove 2-slot allocation is below original rsp
apply-double-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  (readReg (regs s) rsp ∸ 8) ∸ 8 < readReg (regs s) rsp
apply-double-alloc-below-rsp s rsp-sufficient = ≤-<-trans rsp∸16≤rsp∸8 rsp∸8<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans)
    rsp-val = readReg (regs s) rsp
    rsp∸8<rsp = apply-alloc-below-rsp s rsp-sufficient
    rsp∸16≤rsp∸8 = m∸n≤m (rsp-val ∸ 8) 8

-- | Prove 2-slot allocation address is different from addresses >= rsp
apply-double-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ 8) ∸ 8 ≢ addr
apply-double-alloc-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (apply-double-alloc-below-rsp s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Thunk-specific Abstract Helpers
------------------------------------------------------------------------

-- | Helper: 2-slot is below 1-slot when rsp > 16
thunk-2slot-below-1slot : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 16) < (rsp-val ∸ 8)
thunk-2slot-below-1slot s rsp-sufficient = ∸-monoʳ-< 8<16 16≤rsp
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    rsp-val = readReg (regs s) rsp
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    16≤rsp : 16 ≤ rsp-val
    16≤rsp = <⇒≤ rsp-sufficient

-- | Helper: 2-slot is below orig-rsp when rsp > 16
thunk-2slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 16) < rsp-val
thunk-2slot-below-orig s rsp-sufficient = <-trans rsp∸16<rsp∸8 rsp∸8<rsp
  where
    open import Data.Nat.Properties using (<-trans)
    rsp∸16<rsp∸8 = thunk-2slot-below-1slot s rsp-sufficient
    rsp∸8<rsp = apply-alloc-below-rsp s rsp-sufficient

-- | Helper: 2-slot is different from orig-rsp when rsp > 16
thunk-2slot-diff-from-orig : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 16) ≢ rsp-val
thunk-2slot-diff-from-orig s rsp-sufficient eq =
  <⇒≢ (thunk-2slot-below-orig s rsp-sufficient) eq
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Helper: 4-slot is below orig-rsp when rsp > 16
thunk-4slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 32) < rsp-val
thunk-4slot-below-orig s rsp-sufficient = ≤-<-trans rsp∸32≤rsp∸8 rsp∸8<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    rsp-val = readReg (regs s) rsp
    rsp∸8<rsp = apply-alloc-below-rsp s rsp-sufficient
    8≤32 : 8 ≤ 32
    8≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    rsp∸32≤rsp∸8 : (rsp-val ∸ 32) ≤ (rsp-val ∸ 8)
    rsp∸32≤rsp∸8 = ∸-monoʳ-≤ rsp-val 8≤32

-- | Helper: 4-slot is different from addresses >= orig-rsp
thunk-4slot-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ 32) ≢ addr
thunk-4slot-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (thunk-4slot-below-orig s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Raw ℕ versions of thunk helpers
------------------------------------------------------------------------

-- | Raw ℕ version: 1-slot below orig when n > 16
n∸8<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 8) < n
n∸8<n-raw n n>16 = m∸8<m n (≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) n>16)

-- | Raw ℕ version: 2-slot below 1-slot when n > 16
n∸16<n∸8-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 16) < (n ∸ 8)
n∸16<n∸8-raw n n>16 = ∸-monoʳ-< 8<16 16≤n
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    16≤n : 16 ≤ n
    16≤n = <⇒≤ n>16

-- | Raw ℕ version: 2-slot below orig when n > 16
n∸16<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 16) < n
n∸16<n-raw n n>16 = <-trans (n∸16<n∸8-raw n n>16) (n∸8<n-raw n n>16)
  where
    open import Data.Nat.Properties using (<-trans)

-- | Raw ℕ version: 4-slot below orig when n > 16
n∸32<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 32) < n
n∸32<n-raw n n>16 = ≤-<-trans n∸32≤n∸8 n∸8<n
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸8<n = n∸8<n-raw n n>16
    8≤32 : 8 ≤ 32
    8≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    n∸32≤n∸8 : (n ∸ 32) ≤ (n ∸ 8)
    n∸32≤n∸8 = ∸-monoʳ-≤ n 8≤32

-- | Raw ℕ version: 3-slot below orig when n > 16
n∸24<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 24) < n
n∸24<n-raw n n>16 = ≤-<-trans n∸24≤n∸8 n∸8<n
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸8<n = n∸8<n-raw n n>16
    8≤24 : 8 ≤ 24
    8≤24 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    n∸24≤n∸8 : (n ∸ 24) ≤ (n ∸ 8)
    n∸24≤n∸8 = ∸-monoʳ-≤ n 8≤24

-- | Raw ℕ version: 3-slot below < 1-slot below when n > 24
n∸24<n∸8-raw : ∀ (n : ℕ) → n > 24 → (n ∸ 24) < (n ∸ 8)
n∸24<n∸8-raw n n>24 = ∸-monoʳ-< 8<24 24≤n
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    8<24 : 8 < 24
    8<24 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    24≤n : 24 ≤ n
    24≤n = <⇒≤ n>24

-- | Identity: (n ∸ 32) + 8 ≡ n ∸ 24 when n ≥ 32
n∸32+8≡n∸24 : ∀ (n : ℕ) → 32 ≤ n → (n ∸ 32) +ℕ 8 ≡ n ∸ 24
n∸32+8≡n∸24 n 32≤n = trans step1 step2
  where
    open import Data.Nat.Properties using (m+n∸n≡m; m∸n+n≡m)
    step1 : (n ∸ 32) +ℕ 8 ≡ ((n ∸ 32) +ℕ 8 +ℕ 24) ∸ 24
    step1 = sym (m+n∸n≡m ((n ∸ 32) +ℕ 8) 24)
    8+24≡32 : 8 +ℕ 24 ≡ 32
    8+24≡32 = refl
    lhs+24≡n : (n ∸ 32) +ℕ 8 +ℕ 24 ≡ n
    lhs+24≡n = trans (+-assoc (n ∸ 32) 8 24) (trans (cong ((n ∸ 32) +ℕ_) 8+24≡32) (m∸n+n≡m 32≤n))
    step2 : ((n ∸ 32) +ℕ 8 +ℕ 24) ∸ 24 ≡ n ∸ 24
    step2 = cong (_∸ 24) lhs+24≡n

-- | Raw ℕ version: 4-slot below orig + 8 < orig when n > 16
n∸32+8<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 32) +ℕ 8 < n
n∸32+8<n-raw n n>16 = <-≤-trans step8<step16 step16≤n
  where
    open import Data.Nat.Properties using (<-≤-trans; +-monoˡ-≤; +-monoʳ-<; ∸-monoʳ-≤; m∸n+n≡m; <⇒≤)
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    step8<step16 : (n ∸ 32) +ℕ 8 < (n ∸ 32) +ℕ 16
    step8<step16 = +-monoʳ-< (n ∸ 32) 8<16
    16≤32 : 16 ≤ 32
    16≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))
    n∸32≤n∸16 : (n ∸ 32) ≤ (n ∸ 16)
    n∸32≤n∸16 = ∸-monoʳ-≤ n 16≤32
    step16≤n∸16+16 : (n ∸ 32) +ℕ 16 ≤ (n ∸ 16) +ℕ 16
    step16≤n∸16+16 = +-monoˡ-≤ 16 n∸32≤n∸16
    16≤n : 16 ≤ n
    16≤n = <⇒≤ n>16
    n∸16+16≡n : (n ∸ 16) +ℕ 16 ≡ n
    n∸16+16≡n = m∸n+n≡m 16≤n
    step16≤n : (n ∸ 32) +ℕ 16 ≤ n
    step16≤n = subst ((n ∸ 32) +ℕ 16 ≤_) n∸16+16≡n step16≤n∸16+16
