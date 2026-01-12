------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInstantiation
--
-- X86 instantiation layer: concrete arithmetic for stack operations.
--
-- This module contains ALL computational arithmetic (∸, +ℕ, *ℕ slot-size) that
-- proves the abstract StackInvariant properties for the X86 backend.
--
-- DESIGN (D041 Architecture):
-- - StackInvariant.agda: abstract types (R15Status, RbpInvariant) - NO arithmetic
-- - StackInstantiation.agda (this file): arithmetic proofs, imports StackInvariant
-- - IR/*.agda (proof layer): imports this module for all stack operations
--
-- The proof layer should use abstract interfaces like:
--   apply-frame-1, abstract-to-rsp-slot-in-stack
-- These hide the arithmetic (rsp ∸ slot-size) behind region-based types.
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
         RbpInvariant;
         StackInvariant; FrameEvidenceFor;
         stack-write-preserves-heap-r15; stack-write-preserves-code-r15;
         stack-write-preserves-unused-r15; stack-write-preserves-instack-r15;
         stack-write-preserves-r15;
         stack-inv-preserved-unchanged; stack-inv-preserved-r15-unchanged;
         stack-inv-for-code-ptr)
open RbpInvariant public

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
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≤?_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; ∸-+-assoc; +-∸-assoc; m+n∸n≡m; ≤-trans; +-monoʳ-≤; m∸n≤m; ≤-refl; ∸-monoʳ-<; m≤n⇒m∸n≡0; ≰⇒>; <⇒≤; <⇒≢)
open import Relation.Nullary using (yes; no)

-- Import constant comparisons from Arithmetic (replaces verbose s≤s chains)
open import Once.Backend.X86.Correct.Arithmetic
  using (word<pair; word≤pair; word<regs; word≤regs; pair≤regs;
         word≤frame∸word; pair≤frame∸word; regs≤frame∸word;
         word+1≤pair; pair<regs;
         slot1-plus-word≡slot2)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Named Constants (D041: replace magic numbers with semantic names)
------------------------------------------------------------------------

-- Fundamental stack unit (x86-64 word size)
slot-size : ℕ
slot-size = 8

-- | Generic n-slot offset: n slots in bytes
-- All slot-based offsets are derived from this function
slots : ℕ → ℕ
slots n = n *ℕ slot-size

-- Stack frame offsets (derived from slots function)
push-offset : ℕ
push-offset = slots 1                      -- 8: one push instruction

two-push-offset : ℕ
two-push-offset = slots 2                  -- 16: push r15 + push rbp

three-slot-offset : ℕ
three-slot-offset = slots 3                -- 24: three slots

four-slot-offset : ℕ
four-slot-offset = slots 4                 -- 32: four slots

five-slot-offset : ℕ
five-slot-offset = slots 5                 -- 40: five slots

thunk-local-size : ℕ
thunk-local-size = slots 2                 -- 16: sub rsp, 16 in thunk

thunk-frame-size : ℕ
thunk-frame-size = four-slot-offset        -- 32: total thunk frame (2 pushes + 16 local)

pair-frame-size : ℕ
pair-frame-size = five-slot-offset         -- 40: Pair operation (5 slots)

curry-frame-size : ℕ
curry-frame-size = slots 2                 -- 16: Curry closure setup

-- Closure/Pair memory layout offsets
closure-code-offset : ℕ
closure-code-offset = slot-size            -- 8: offset to code pointer in closure
                                           -- closure layout: [env-addr, code-ptr]
                                           -- closure-addr + 0 = env-addr
                                           -- closure-addr + 8 = code-ptr

pair-snd-offset : ℕ
pair-snd-offset = slot-size                -- 8: offset to second element of pair
                                           -- pair layout: [fst, snd]
                                           -- pair-addr + 0 = fst
                                           -- pair-addr + 8 = snd

-- Minimum rsp bounds for safe operations
thunk-min-rsp : ℕ
thunk-min-rsp = thunk-frame-size +ℕ slot-size   -- 40: need > four-slot-offset with buffer

pair-min-rsp : ℕ
pair-min-rsp = pair-frame-size +ℕ slot-size     -- 48: need > five-slot-offset with buffer

apply-min-rsp : ℕ
apply-min-rsp = two-push-offset                -- 16: need > two-push-offset for apply

------------------------------------------------------------------------
-- Centralized Arithmetic Helpers (D041: define early for use throughout)
------------------------------------------------------------------------

-- | Common bound conversion: rsp > two-push-offset implies rsp > slot-size
-- Used in many proofs where we have two-slot bound but need single-slot bound
rsp>slot-from-2slot : ∀ {n} → n > two-push-offset → n > slot-size
rsp>slot-from-2slot n>2slot = ≤-trans word+1≤pair (<⇒≤ n>2slot)

-- | Generic subtraction-less-than helper (m ∸ n < m when m > n and n > 0)
-- Centralized to avoid defining this pattern in every proof
m∸n<m-when-m>n : ∀ m n → n > 0 → m > n → m ∸ n < m
m∸n<m-when-m>n (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

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
    -- rsp points to stack region
    rsp-in-stack : region-of (readReg (regs s) rsp) ≡ stack

    -- rsp has sufficient space for n slots (concrete X86 bound)
    rsp-sufficient : readReg (regs s) rsp > n *ℕ slot-size

    -- After allocating k slots (k ≤ n), still in stack region
    capacity-maintained : ∀ k → k ≤ n →
      region-of (readReg (regs s) rsp ∸ (k *ℕ slot-size)) ≡ stack

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
  ; rsp-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) (rsp-sufficient cap)
  ; capacity-maintained = λ k k≤n →
      trans (cong (λ r → region-of (r ∸ (k *ℕ slot-size))) rsp-eq)
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
    open import Data.Nat.Properties using (m+n∸n≡m; m∸n+n≡m; <⇒≤; +-monoʳ-<)

    old-rsp = readReg (regs s) rsp
    new-rsp = readReg (regs s') rsp

    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 1 (s≤s z≤n))

    rsp'-sufficient : new-rsp > n *ℕ slot-size
    rsp'-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) sub-lemma
      where
        open import Data.Nat.Properties using (≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

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

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n =
      let 1+k≤sn : (1 +ℕ k) ≤ suc n
          1+k≤sn = s≤s k≤n
          old-cap-at-1+k : region-of (old-rsp ∸ ((1 +ℕ k) *ℕ slot-size)) ≡ stack
          old-cap-at-1+k = capacity-maintained cap (1 +ℕ k) 1+k≤sn
          step1 : (old-rsp ∸ slot-size) ∸ (k *ℕ slot-size) ≡ old-rsp ∸ (slot-size +ℕ k *ℕ slot-size)
          step1 = ∸-+-assoc old-rsp slot-size (k *ℕ slot-size)
          arith-eq : slot-size +ℕ k *ℕ slot-size ≡ (1 +ℕ k) *ℕ slot-size
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ slot-size) ≡ old-rsp ∸ ((1 +ℕ k) *ℕ slot-size)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ slot-size)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-1+k

-- | After pop (rsp += slot-size), capacity increases by 1
capacity-after-pop : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ slot-size →
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

    rsp'-sufficient : new-rsp > (suc n) *ℕ slot-size
    rsp'-sufficient = subst (_> (suc n) *ℕ slot-size) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ slot-size > n *ℕ slot-size +ℕ slot-size
        step1 = +-monoˡ-< slot-size (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ slot-size > (suc n) *ℕ slot-size
        add-lemma = subst (old-rsp +ℕ slot-size >_) (+-comm (n *ℕ slot-size) slot-size) step1

    cap-maintained : ∀ k → k ≤ suc n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained (suc k) (s≤s k≤n) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ slot-size)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ slot-size) ∸ (slot-size +ℕ k *ℕ slot-size) ≡ ((old-rsp +ℕ slot-size) ∸ slot-size) ∸ (k *ℕ slot-size)
        step1 = sym (∸-+-assoc (old-rsp +ℕ slot-size) slot-size (k *ℕ slot-size))
        step2 : (old-rsp +ℕ slot-size) ∸ slot-size ≡ old-rsp
        step2 = m+n∸n≡m old-rsp slot-size
        arith-eq : (old-rsp +ℕ slot-size) ∸ ((suc k) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        arith-eq = trans step1 (cong (_∸ (k *ℕ slot-size)) step2)
        addr-eq : new-rsp ∸ ((suc k) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        addr-eq = trans (cong (λ r → r ∸ ((suc k) *ℕ slot-size)) rsp-eq) arith-eq

-- | After sub rsp, 16 (rsp -= 16), capacity decreases by 2
capacity-after-alloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s (suc (suc n)) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
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

    rsp'-sufficient : new-rsp > n *ℕ slot-size
    rsp'-sufficient = subst (_> n *ℕ slot-size) (sym rsp-eq) sub-lemma
      where
        old-bound : old-rsp > two-push-offset +ℕ n *ℕ slot-size
        old-bound = rsp-sufficient cap

        two-push≤old : two-push-offset ≤ old-rsp
        two-push≤old = <⇒≤ (≤-<-trans (m≤m+n two-push-offset (n *ℕ slot-size)) old-bound)

        old-rsp-eq : (old-rsp ∸ two-push-offset) +ℕ two-push-offset ≡ old-rsp
        old-rsp-eq = m∸n+n≡m two-push≤old

        old-bound' : old-rsp > n *ℕ slot-size +ℕ two-push-offset
        old-bound' = subst (old-rsp >_) (+-comm two-push-offset (n *ℕ slot-size)) old-bound

        sub-lemma : old-rsp ∸ two-push-offset > n *ℕ slot-size
        sub-lemma = +-cancelʳ-< two-push-offset (n *ℕ slot-size) (old-rsp ∸ two-push-offset) bound-step
          where
            bound-step : n *ℕ slot-size +ℕ two-push-offset < (old-rsp ∸ two-push-offset) +ℕ two-push-offset
            bound-step = subst (n *ℕ slot-size +ℕ two-push-offset <_) (sym old-rsp-eq) old-bound'

    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n =
      let 2+k≤ssn : (2 +ℕ k) ≤ suc (suc n)
          2+k≤ssn = s≤s (s≤s k≤n)
          old-cap-at-2+k : region-of (old-rsp ∸ ((2 +ℕ k) *ℕ slot-size)) ≡ stack
          old-cap-at-2+k = capacity-maintained cap (2 +ℕ k) 2+k≤ssn
          step1 : (old-rsp ∸ two-push-offset) ∸ (k *ℕ slot-size) ≡ old-rsp ∸ (two-push-offset +ℕ k *ℕ slot-size)
          step1 = ∸-+-assoc old-rsp two-push-offset (k *ℕ slot-size)
          arith-eq : two-push-offset +ℕ k *ℕ slot-size ≡ (2 +ℕ k) *ℕ slot-size
          arith-eq = refl
          addr-eq : new-rsp ∸ (k *ℕ slot-size) ≡ old-rsp ∸ ((2 +ℕ k) *ℕ slot-size)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ slot-size)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-2+k

-- | After add rsp, 16 (rsp += 16), capacity increases by 2
capacity-after-dealloc-2-slots : ∀ (s s' : State) (n : ℕ) →
  StackCapacity s n →
  readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ two-push-offset →
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

    rsp'-sufficient : new-rsp > (suc (suc n)) *ℕ slot-size
    rsp'-sufficient = subst (_> (suc (suc n)) *ℕ slot-size) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        step1 : old-rsp +ℕ two-push-offset > n *ℕ slot-size +ℕ two-push-offset
        step1 = +-monoˡ-< two-push-offset (rsp-sufficient cap)
        add-lemma : old-rsp +ℕ two-push-offset > (suc (suc n)) *ℕ slot-size
        add-lemma = subst (old-rsp +ℕ two-push-offset >_) (+-comm (n *ℕ slot-size) two-push-offset) step1

    cap-maintained : ∀ k → k ≤ suc (suc n) → region-of (new-rsp ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack
    cap-maintained 1 _ = stack-sub-preserves-region new-rsp slot-size new-rsp-in-stack slot-size≤new-rsp
      where
        open import Data.Nat.Properties using (<⇒≤; +-monoˡ-<; <-trans)
        rsp>0 : old-rsp > 0
        rsp>0 = ≤-trans (s≤s z≤n) (rsp-sufficient cap)
        step1 : old-rsp +ℕ two-push-offset > two-push-offset
        step1 = +-monoˡ-< two-push-offset rsp>0
        step2 : two-push-offset > slot-size
        step2 = word<pair
        new-rsp-bound : new-rsp > slot-size
        new-rsp-bound = subst (_> slot-size) (sym rsp-eq) (<-trans step2 step1)
        slot-size≤new-rsp : slot-size ≤ new-rsp
        slot-size≤new-rsp = <⇒≤ new-rsp-bound
    cap-maintained (suc (suc k)) (s≤s (s≤s k≤n)) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ slot-size)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        step1 : (old-rsp +ℕ two-push-offset) ∸ (two-push-offset +ℕ k *ℕ slot-size) ≡ ((old-rsp +ℕ two-push-offset) ∸ two-push-offset) ∸ (k *ℕ slot-size)
        step1 = sym (∸-+-assoc (old-rsp +ℕ two-push-offset) two-push-offset (k *ℕ slot-size))
        step2 : (old-rsp +ℕ two-push-offset) ∸ two-push-offset ≡ old-rsp
        step2 = m+n∸n≡m old-rsp two-push-offset
        arith-eq : (old-rsp +ℕ two-push-offset) ∸ ((suc (suc k)) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        arith-eq = trans step1 (cong (_∸ (k *ℕ slot-size)) step2)
        addr-eq : new-rsp ∸ ((suc (suc k)) *ℕ slot-size) ≡ old-rsp ∸ (k *ℕ slot-size)
        addr-eq = trans (cong (λ r → r ∸ ((suc (suc k)) *ℕ slot-size)) rsp-eq) arith-eq

------------------------------------------------------------------------
-- Deriving Address Properties from Capacity
------------------------------------------------------------------------

-- | With capacity n ≥ 2, address rsp - 16 is in stack region
slot-2-addr-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  region-of (readReg (regs s) rsp ∸ two-push-offset) ≡ stack
slot-2-addr-in-stack s cap = capacity-maintained cap 2 (s≤s (s≤s z≤n))

-- | With capacity n ≥ 1, address rsp - slot-size is in stack region
slot-1-addr-in-stack : ∀ (s : State) →
  StackCapacity s 1 →
  region-of (readReg (regs s) rsp ∸ slot-size) ≡ stack
slot-1-addr-in-stack s cap = capacity-maintained cap 1 (s≤s z≤n)

------------------------------------------------------------------------
-- Converting from rsp bounds to StackCapacity
------------------------------------------------------------------------

-- | General conversion: rsp > n*8 gives StackCapacity s n
rsp-bound-to-capacity : ∀ (n : ℕ) (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
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
    cap-maintained : ∀ k → k ≤ n → region-of (rsp-val ∸ (k *ℕ slot-size)) ≡ stack
    cap-maintained k k≤n = stack-sub-preserves-region rsp-val (k *ℕ slot-size) rsp-in-stack (k*slot≤rsp k k≤n)

-- Note: rsp-to-capacity-N wrappers have been removed.
-- Use rsp-bound-to-capacity n s rsp-in-stack rsp-bound directly.

-- | Convert StackCapacity back to concrete bound (for compatibility)
capacity-2-to-rsp-bound : ∀ (s : State) →
  StackCapacity s 2 →
  readReg (regs s) rsp > two-push-offset
capacity-2-to-rsp-bound s cap = rsp-sufficient cap

-- | rsp > two-push-offset preservation when rsp is unchanged
rsp-bound-preserved-unchanged : ∀ (s s' : State) →
  readReg (regs s) rsp > two-push-offset →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > two-push-offset
rsp-bound-preserved-unchanged s s' rsp-sufficient rsp-eq = subst (_> two-push-offset) (sym rsp-eq) rsp-sufficient

------------------------------------------------------------------------
-- Abstract Frame Creation
------------------------------------------------------------------------

-- | Create a StackPointer for a frame at offset k slots below current rsp.
make-frame-at-slot : ∀ {n} (s : State) → StackCapacity s n → (k : ℕ) → k ≤ n → StackPointer
make-frame-at-slot s cap k k≤n = record
  { addr = readReg (regs s) rsp ∸ (k *ℕ slot-size)
  ; in-stack = capacity-maintained cap k k≤n
  }

-- | The frame created at slot 0 has addr = current rsp
make-frame-at-slot-0-addr : ∀ {n} (s : State) (cap : StackCapacity s n) →
  sp-addr (make-frame-at-slot s cap 0 z≤n) ≡ readReg (regs s) rsp
make-frame-at-slot-0-addr s cap = refl

-- | Frame at slot 1 has addr = rsp - slot-size
make-frame-at-slot-1-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
  sp-addr (make-frame-at-slot s cap 1 (s≤s z≤n)) ≡ readReg (regs s) rsp ∸ slot-size
make-frame-at-slot-1-addr s cap = refl

-- | Frame at slot 2 has addr = rsp - 16
make-frame-at-slot-2-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc n))) →
  sp-addr (make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))) ≡ readReg (regs s) rsp ∸ two-push-offset
make-frame-at-slot-2-addr s cap = refl

-- | Frame at slot 3 has addr = rsp - 24
make-frame-at-slot-3-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc n)))) →
  sp-addr (make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))) ≡ readReg (regs s) rsp ∸ three-slot-offset
make-frame-at-slot-3-addr s cap = refl

-- | Frame at slot 4 has addr = rsp - 32
make-frame-at-slot-4-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc n))))) →
  sp-addr (make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ readReg (regs s) rsp ∸ four-slot-offset
make-frame-at-slot-4-addr s cap = refl

-- | Frame at slot 5 has addr = rsp - 40
make-frame-at-slot-5-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc (suc n)))))) →
  sp-addr (make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ≡ readReg (regs s) rsp ∸ five-slot-offset
make-frame-at-slot-5-addr s cap = refl

-- | Frames at lower slot indices have higher addresses (stack grows down)
frame-at-lower-slot-≥ : ∀ {n} (s : State) (cap : StackCapacity s n) (k₁ k₂ : ℕ)
  (k₁≤n : k₁ ≤ n) (k₂≤n : k₂ ≤ n) →
  k₁ ≤ k₂ →
  sp-addr (make-frame-at-slot s cap k₁ k₁≤n) ≥ sp-addr (make-frame-at-slot s cap k₂ k₂≤n)
frame-at-lower-slot-≥ s cap k₁ k₂ k₁≤n k₂≤n k₁≤k₂ = ∸-monoʳ-≤ (readReg (regs s) rsp) (*-monoˡ-≤ slot-size k₁≤k₂)
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

-- | Bridge from abstract to concrete for Apply's push address (rsp - slot-size)
abstract-to-rsp-slot-in-stack : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
                             region-of (readReg (regs s) rsp ∸ slot-size) ≡ stack
abstract-to-rsp-slot-in-stack s cap =
  subst (λ addr → region-of addr ≡ stack)
        (trans (slot-addr-0-is-base (apply-frame-1 s cap))
               (make-frame-at-slot-1-addr s cap))
        (apply-frame-slot-0-in-stack s cap)

------------------------------------------------------------------------
-- Generic slot-in-stack proof (D041: unified interface)
------------------------------------------------------------------------

-- | Generic: (rsp - slots k) is in stack when we have capacity ≥ k
-- This is the core abstraction - all specific slot proofs derive from this
rsp-minus-n-slots-in-stack : ∀ (k : ℕ) {n} (s : State) (cap : StackCapacity s n) →
                              k ≤ n →
                              region-of (readReg (regs s) rsp ∸ slots k) ≡ stack
rsp-minus-n-slots-in-stack k s cap k≤n = capacity-maintained cap k k≤n

------------------------------------------------------------------------
-- ThunkExec-specific Abstract Interface (D041-compliant)
------------------------------------------------------------------------

-- | Parameterized thunk frame at slot k
-- Alias for make-frame-at-slot with clearer naming for thunk context
thunk-frame : (k : ℕ) {n : ℕ} (s : State) (cap : StackCapacity s n) (k≤n : k ≤ n) → StackPointer
thunk-frame k s cap k≤n = make-frame-at-slot s cap k k≤n

-- | Parameterized bridge from abstract to concrete for (rsp - k*slot-size)
abstract-to-rsp-slots-in-stack : (k : ℕ) {n : ℕ} (s : State) (cap : StackCapacity s n) (k≤n : k ≤ n) →
                                 region-of (readReg (regs s) rsp ∸ slots k) ≡ stack
abstract-to-rsp-slots-in-stack k s cap k≤n = rsp-minus-n-slots-in-stack k s cap k≤n

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

-- | Pair frame 0 address equals rsp - 40
pair-frame-0-addr-eq : (s : State) (cap : StackCapacity s 5) →
                       sp-addr (pair-frame-0 s cap) ≡ readReg (regs s) rsp ∸ five-slot-offset
pair-frame-0-addr-eq s cap = refl

-- | Pair frame slot 1 address equals (rsp - five-slot-offset) + slot-size
pair-frame-slot-1-addr-eq : (s : State) (cap : StackCapacity s 5) →
                            slot-addr (pair-frame-0 s cap) 1 ≡ (readReg (regs s) rsp ∸ five-slot-offset) +ℕ slot-size
pair-frame-slot-1-addr-eq s cap =
  trans (slot-addr-1-is-base+8 (pair-frame-0 s cap))
        (cong (_+ℕ slot-size) (pair-frame-0-addr-eq s cap))

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
  region-of (readReg (regs s) rsp ∸ five-slot-offset) ≡ stack
pair-r15-in-stack s cap = capacity-maintained cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- | (rsp - five-slot-offset) + slot-size is in stack region when we have capacity 5
pair-second-slot-in-stack : ∀ (s : State) →
  StackCapacity s 5 →
  region-of ((readReg (regs s) rsp ∸ five-slot-offset) +ℕ slot-size) ≡ stack
pair-second-slot-in-stack s cap =
  subst (λ a → region-of a ≡ stack)
        (sym (alloc-5-slots-second-addr-eq rsp-val (cap-to-pair-setup-rsp-bound cap)))
        (capacity-maintained cap 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
  where
    open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <⇒≤)
    rsp-val = readReg (regs s) rsp
    cap-to-pair-setup-rsp-bound : StackCapacity s 5 → readReg (regs s) rsp ≥ five-slot-offset
    cap-to-pair-setup-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    alloc-5-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ five-slot-offset → (rsp-val ∸ five-slot-offset) +ℕ slot-size ≡ rsp-val ∸ four-slot-offset
    alloc-5-slots-second-addr-eq rsp-val rsp≥40 = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits-after-4-slots)
      where
        step1 : rsp-val ∸ five-slot-offset ≡ (rsp-val ∸ four-slot-offset) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val four-slot-offset slot-size)
        word-fits-after-4-slots : slot-size ≤ rsp-val ∸ four-slot-offset
        word-fits-after-4-slots = ∸-monoˡ-≤ four-slot-offset rsp≥40

-- | Get StackCapacity for Pair setup from runtime rsp bound
pair-stack-capacity : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > five-slot-offset →
  StackCapacity s 5
pair-stack-capacity s rsp-in-stack rsp-bound = rsp-bound-to-capacity 5 s rsp-in-stack rsp-bound

-- | Create StackInvariant for state after Pair setup
pair-setup-stack-inv : ∀ (s s-setup : State) →
  StackCapacity s 5 →
  readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ five-slot-offset →
  readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ five-slot-offset →
  StackInvariant s-setup
pair-setup-stack-inv s s-setup cap r15-eq rsp-eq =
  r15-in-stack pair-frame 0 r15-is-slot0 pair-frame-bound
  where
    base-in-stack : region-of (readReg (regs s) rsp ∸ five-slot-offset) ≡ stack
    base-in-stack = pair-r15-in-stack s cap
    pair-frame : StackPointer
    pair-frame = record
      { addr = readReg (regs s) rsp ∸ five-slot-offset
      ; in-stack = base-in-stack
      }
    r15-is-slot0 : readReg (regs s-setup) r15 ≡ slot-addr pair-frame 0
    r15-is-slot0 = trans r15-eq (sym (slot-addr-0-is-base pair-frame))
    pair-frame-bound : sp-addr pair-frame ≥ readReg (regs s-setup) rsp
    pair-frame-bound = subst (sp-addr pair-frame ≥_) (sym rsp-eq) ≤-refl

------------------------------------------------------------------------
-- Combined Region Lemmas for Stack Operations
------------------------------------------------------------------------

-- | After sub rsp 16, both write addresses (new-rsp and new-rsp+slot) are in stack
alloc-2-slots-addrs-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ two-push-offset
  in (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ slot-size) ≡ stack)
alloc-2-slots-addrs-in-stack s cap =
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ two-push-offset
      write1-in-stack : region-of new-rsp ≡ stack
      write1-in-stack = slot-2-addr-in-stack s cap
      write2-in-stack : region-of (new-rsp +ℕ slot-size) ≡ stack
      write2-in-stack = subst (λ a → region-of a ≡ stack)
                              (sym (alloc-2-slots-second-addr-eq rsp-val (cap-to-inl-inr-rsp-bound cap)))
                              (slot-1-addr-in-stack s (capacity-weaken cap))
  in write1-in-stack , write2-in-stack
  where
    open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; <-trans)
    cap-to-inl-inr-rsp-bound : StackCapacity s 2 → readReg (regs s) rsp ≥ two-push-offset
    cap-to-inl-inr-rsp-bound cap = <⇒≤ (rsp-sufficient cap)
    capacity-weaken : StackCapacity s 2 → StackCapacity s 1
    capacity-weaken cap2 = record
      { rsp-in-stack = rsp-in-stack cap2
      ; rsp-sufficient = <-trans slot<2slot (rsp-sufficient cap2)
      ; capacity-maintained = λ k k≤1 →
          capacity-maintained cap2 k (≤-trans k≤1 (s≤s z≤n))
      }
      where
        slot<2slot : slot-size < two-push-offset
        slot<2slot = word<pair
    alloc-2-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ two-push-offset → (rsp-val ∸ two-push-offset) +ℕ slot-size ≡ rsp-val ∸ slot-size
    alloc-2-slots-second-addr-eq rsp-val rsp≥16 = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits-after-1-slot)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        word-fits-after-1-slot : slot-size ≤ rsp-val ∸ slot-size
        word-fits-after-1-slot = ∸-monoˡ-≤ slot-size rsp≥16

-- | Stack writes at rsp - k*8 don't affect heap addresses
stack-write-disjoint-from-heap : ∀ (s : State) (n k : ℕ) (heap-addr : Addr) →
  StackCapacity s n →
  k ≤ n →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ (k *ℕ slot-size) ≢ heap-addr
stack-write-disjoint-from-heap s n k heap-addr cap k≤n heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ (k *ℕ slot-size)) heap-addr
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
  readReg (regs s) rsp > two-push-offset →
  AbstractStackInvariant s
from-old-invariants s stack-inv rsp-in-stack rsp-sufficient = record
  { r15-status = stack-inv
  ; capacity = rsp-bound-to-capacity 2 s rsp-in-stack rsp-sufficient
  }

------------------------------------------------------------------------
-- Address disjointness proofs using regions
------------------------------------------------------------------------

-- | Prove that stack write at (rsp - 16) doesn't affect r15
stack-write-slot-2-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ two-push-offset ≢ readReg (regs s) r15
stack-write-slot-2-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ two-push-offset
    stack-addr-in-stack = slot-2-addr-in-stack s (capacity inv)
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m-when-m>n (readReg (regs s) rsp) two-push-offset (s≤s z≤n) (rsp-sufficient (capacity inv))
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ two-push-offset
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Similarly for (rsp - slot-size)
stack-write-slot-1-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ slot-size ≢ readReg (regs s) r15
stack-write-slot-1-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (<-trans; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ slot-size
    stack-addr-in-stack = capacity-maintained (capacity inv) 1 (s≤s z≤n)
    rsp>slot : readReg (regs s) rsp > slot-size
    rsp>slot = <-trans word<pair (rsp-sufficient (capacity inv))
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m-when-m>n (readReg (regs s) rsp) slot-size (s≤s z≤n) rsp>slot
    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      let write-addr = readReg (regs s) rsp ∸ slot-size
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
  readReg (regs s) rsp ∸ two-push-offset ≢ heap-addr
stack-write-preserves-heap-data s heap-addr inv heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ two-push-offset) heap-addr
                      (slot-2-addr-in-stack s (capacity inv))
                      heap-proof

------------------------------------------------------------------------
-- Address disjointness from StackInvariant (legacy compatibility)
------------------------------------------------------------------------

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from r15
addr-diff-from-invariant : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-r15 = readReg (regs s) r15
  in (new-rsp ≢ orig-r15) × ((new-rsp +ℕ slot-size) ≢ orig-r15)
addr-diff-from-invariant s stack-inv rsp-in-stack rsp-suff = diff1 , diff2
  where
    open import Data.Nat.Properties using (<-trans; <⇒≢; <-≤-trans; ∸-monoˡ-≤)
    open import Data.Product using (proj₁; proj₂)
    rsp-val = readReg (regs s) rsp
    cap = rsp-bound-to-capacity 2 s rsp-in-stack rsp-suff
    addrs-in-stack = alloc-2-slots-addrs-in-stack s cap
    write1-in-stack = proj₁ addrs-in-stack
    write2-in-stack = proj₂ addrs-in-stack
    stack-addr1 = rsp-val ∸ two-push-offset
    stack-addr2 = (rsp-val ∸ two-push-offset) +ℕ slot-size
    addr1<rsp : stack-addr1 < rsp-val
    addr1<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-suff
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-suff
    addr2<rsp : stack-addr2 < rsp-val
    addr2<rsp = subst (_< rsp-val) (sym addr2-eq) (m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot)
      where
        open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc)
        rsp≥16 : rsp-val ≥ two-push-offset
        rsp≥16 = <⇒≤ rsp-suff
        addr2-eq : stack-addr2 ≡ rsp-val ∸ slot-size
        addr2-eq = trans (cong (_+ℕ slot-size) (sym (∸-+-assoc rsp-val slot-size slot-size)))
                         (m∸n+n≡m (∸-monoˡ-≤ slot-size rsp≥16))
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

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from rbp
rbp-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp)
rbp-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp-diff-proof , rbp-diff-proof-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    rbp-diff-proof : new-rsp ≢ orig-rbp
    rbp-diff-proof = <⇒≢ new-rsp<rbp
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    rbp-diff-proof-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp
    rbp-diff-proof-2 = subst (_≢ orig-rbp) (sym second-slot-eq) (<⇒≢ rsp-slot<rbp)

-- | Prove (rsp - two-push-offset) and (rsp - slot-size) are different from (rbp + slot-size)
rbp+slot-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp+slot = readReg (regs s) rbp +ℕ slot-size
  in (new-rsp ≢ orig-rbp+slot) × ((new-rsp +ℕ slot-size) ≢ orig-rbp+slot)
rbp+slot-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp+slot-diff-1 , rbp+slot-diff-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m≤m+n; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    orig-rbp+slot = orig-rbp +ℕ slot-size
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    new-rsp<rbp+slot : new-rsp < orig-rbp+slot
    new-rsp<rbp+slot = ≤-trans new-rsp<rbp (m≤m+n orig-rbp slot-size)
    rbp+slot-diff-1 : new-rsp ≢ orig-rbp+slot
    rbp+slot-diff-1 = <⇒≢ new-rsp<rbp+slot
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    rsp-slot<rbp+slot : rsp-val ∸ slot-size < orig-rbp+slot
    rsp-slot<rbp+slot = ≤-trans rsp-slot<rbp (m≤m+n orig-rbp slot-size)
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    rbp+slot-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp+slot
    rbp+slot-diff-2 = subst (_≢ orig-rbp+slot) (sym second-slot-eq) (<⇒≢ rsp-slot<rbp+slot)

-- | Combined rbp and rbp+slot disjointness for curry
curry-frame-disjoint-from-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp) ×
     (new-rsp ≢ orig-rbp +ℕ slot-size) × ((new-rsp +ℕ slot-size) ≢ orig-rbp +ℕ slot-size)
curry-frame-disjoint-from-rbp s rbp-inv rsp-suff =
  let (d1 , d2) = rbp-addr-diff-from-invariant s rbp-inv rsp-suff
      (d3 , d4) = rbp+slot-addr-diff-from-invariant s rbp-inv rsp-suff
  in d1 , d2 , d3 , d4

-- | Stack invariant frame bound update after 2-slot allocation
curry-stack-inv-frame-bound-update : ∀ (s s' : State) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
  (frame : StackPointer) →
  sp-addr frame ≥ readReg (regs s) rsp →
  sp-addr frame ≥ readReg (regs s') rsp
curry-stack-inv-frame-bound-update s s' rsp-eq frame old-bound =
  subst (sp-addr frame ≥_) (sym rsp-eq) (≤-trans (m∸n≤m (readReg (regs s) rsp) two-push-offset) old-bound)

-- | RbpInvariant preservation after 2-slot allocation
curry-rbp-inv-update : ∀ (s s' : State) →
  RbpInvariant s →
  readReg (regs s') rbp ≡ readReg (regs s) rbp →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ two-push-offset →
  RbpInvariant s'
curry-rbp-inv-update s s' rbp-inv rbp-eq rsp-eq = record
  { rbp-frame = RbpInvariant.rbp-frame rbp-inv
  ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
  ; frame-bound = curry-stack-inv-frame-bound-update s s' rsp-eq
                    (RbpInvariant.rbp-frame rbp-inv)
                    (RbpInvariant.frame-bound rbp-inv)
  }

-- | Ordering facts for curry: new-rsp < rbp and (new-rsp + slot-size) < rbp
curry-alloc-below-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
      orig-rbp = readReg (regs s) rbp
  in (new-rsp < orig-rbp) × ((new-rsp +ℕ slot-size) < orig-rbp)
curry-alloc-below-rbp s rbp-inv rsp-sufficient = new-rsp<rbp , new-rsp+slot<rbp
  where
    open import Data.Nat.Properties using (<-≤-trans; <⇒≤; +-monoʳ-<; m∸n+n≡m; ≤-<-trans; ∸-+-assoc; ∸-monoˡ-≤)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    orig-rbp = readReg (regs s) rbp
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m-when-m>n rsp-val two-push-offset (s≤s z≤n) rsp-sufficient
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))
    two-push≤rsp : two-push-offset ≤ rsp-val
    two-push≤rsp = <⇒≤ rsp-sufficient
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient
    rsp-slot<rsp : rsp-val ∸ slot-size < rsp-val
    rsp-slot<rsp = m∸n<m-when-m>n rsp-val slot-size (s≤s z≤n) rsp>slot
    rsp-slot<rbp : rsp-val ∸ slot-size < orig-rbp
    rsp-slot<rbp = subst (rsp-val ∸ slot-size <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-slot<rsp (frame-bound rbp-inv))
    second-slot-eq : new-rsp +ℕ slot-size ≡ rsp-val ∸ slot-size
    second-slot-eq = trans (cong (_+ℕ slot-size) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (n≤1+n)
        step1 : rsp-val ∸ two-push-offset ≡ (rsp-val ∸ slot-size) ∸ slot-size
        step1 = sym (∸-+-assoc rsp-val slot-size slot-size)
        two-slots-fit : two-push-offset ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n two-push-offset) rsp-sufficient
        word-fits : slot-size ≤ rsp-val ∸ slot-size
        word-fits = ∸-monoˡ-≤ slot-size two-slots-fit
    new-rsp+slot<rbp : (new-rsp +ℕ slot-size) < orig-rbp
    new-rsp+slot<rbp = subst (_< orig-rbp) (sym second-slot-eq) rsp-slot<rbp

-- | Prove curry allocation addresses are non-zero
curry-alloc-nonzero : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let new-rsp = readReg (regs s) rsp ∸ two-push-offset
  in (new-rsp ≢ 0) × ((new-rsp +ℕ slot-size) ≢ 0)
curry-alloc-nonzero s rsp-sufficient = diff-new-rsp , diff-new-rsp+slot
  where
    open import Data.Nat.Properties using (<⇒≢; ∸-monoˡ-≤; <-trans; +-monoˡ-<)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ two-push-offset
    17≤rsp : 17 ≤ rsp-val
    17≤rsp = rsp-sufficient
    1≤new-rsp : 1 ≤ new-rsp
    1≤new-rsp = subst (1 ≤_) refl (∸-monoˡ-≤ two-push-offset 17≤rsp)
    0<new-rsp : 0 < new-rsp
    0<new-rsp = 1≤new-rsp
    0<new-rsp+slot : 0 < (new-rsp +ℕ slot-size)
    0<new-rsp+slot = <-trans (s≤s z≤n) (+-monoˡ-< slot-size 0<new-rsp)
    diff-new-rsp : new-rsp ≢ 0
    diff-new-rsp eq = <⇒≢ 0<new-rsp (sym eq)
    diff-new-rsp+slot : (new-rsp +ℕ slot-size) ≢ 0
    diff-new-rsp+slot eq = <⇒≢ 0<new-rsp+slot (sym eq)

------------------------------------------------------------------------
-- Apply helpers: 1-slot allocation (push r15)
------------------------------------------------------------------------

private
  m∸slot<m : ∀ m → m > slot-size → m ∸ slot-size < m
  m∸slot<m (suc m') (s≤s _) = s≤s (m∸n≤m m' 7)

-- | Prove 1-slot allocation address is below original rsp
apply-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  readReg (regs s) rsp ∸ slot-size < readReg (regs s) rsp
apply-alloc-below-rsp s rsp-sufficient = m∸slot<m rsp-val rsp>slot
  where
    rsp-val = readReg (regs s) rsp
    rsp>slot : rsp-val > slot-size
    rsp>slot = rsp>slot-from-2slot rsp-sufficient

-- | Prove 1-slot allocation address is different from addresses >= rsp
apply-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  readReg (regs s) rsp ∸ slot-size ≢ addr
apply-alloc-diff-from-above s rsp-sufficient addr addr≥rsp = <⇒≢ new-rsp<addr
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)
    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ slot-size
    new-rsp<rsp = apply-alloc-below-rsp s rsp-sufficient
    new-rsp<addr : new-rsp < addr
    new-rsp<addr = <-≤-trans new-rsp<rsp addr≥rsp

-- | Prove rsp ≢ (rsp - slot-size) when rsp > two-push-offset
apply-rsp-diff-from-alloc : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  readReg (regs s) rsp ≢ readReg (regs s) rsp ∸ slot-size
apply-rsp-diff-from-alloc s rsp-sufficient eq =
  <⇒≢ (apply-alloc-below-rsp s rsp-sufficient) (sym eq)
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Prove 2-slot allocation is below original rsp
apply-double-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (readReg (regs s) rsp ∸ slot-size) ∸ slot-size < readReg (regs s) rsp
apply-double-alloc-below-rsp s rsp-sufficient = ≤-<-trans rsp∸2slot≤rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans)
    rsp-val = readReg (regs s) rsp
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient
    rsp∸2slot≤rsp∸slot = m∸n≤m (rsp-val ∸ slot-size) slot-size

-- | Prove 2-slot allocation address is different from addresses >= rsp
apply-double-alloc-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ slot-size) ∸ slot-size ≢ addr
apply-double-alloc-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (apply-double-alloc-below-rsp s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Thunk-specific Abstract Helpers
------------------------------------------------------------------------

-- | Helper: 2-slot is below 1-slot when rsp > two-push-offset
thunk-2slot-below-1slot : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) < (rsp-val ∸ slot-size)
thunk-2slot-below-1slot s rsp-sufficient = ∸-monoʳ-< word<pair (<⇒≤ rsp-sufficient)

-- | Helper: 2-slot is below orig-rsp when rsp > two-push-offset
thunk-2slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) < rsp-val
thunk-2slot-below-orig s rsp-sufficient = <-trans rsp∸2slot<rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (<-trans)
    rsp∸2slot<rsp∸slot = thunk-2slot-below-1slot s rsp-sufficient
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient

-- | Helper: 2-slot is different from orig-rsp when rsp > two-push-offset
thunk-2slot-diff-from-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ two-push-offset) ≢ rsp-val
thunk-2slot-diff-from-orig s rsp-sufficient eq =
  <⇒≢ (thunk-2slot-below-orig s rsp-sufficient) eq
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Helper: 4-slot is below orig-rsp when rsp > two-push-offset
thunk-4slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ four-slot-offset) < rsp-val
thunk-4slot-below-orig s rsp-sufficient = ≤-<-trans rsp∸4slot≤rsp∸slot rsp∸slot<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    rsp-val = readReg (regs s) rsp
    rsp∸slot<rsp = apply-alloc-below-rsp s rsp-sufficient
    rsp∸4slot≤rsp∸slot : (rsp-val ∸ four-slot-offset) ≤ (rsp-val ∸ slot-size)
    rsp∸4slot≤rsp∸slot = ∸-monoʳ-≤ rsp-val word≤frame∸word

-- | Helper: 4-slot is different from addresses >= orig-rsp
thunk-4slot-diff-from-above : ∀ (s : State) →
  readReg (regs s) rsp > two-push-offset →
  (addr : ℕ) →
  addr ≥ readReg (regs s) rsp →
  (readReg (regs s) rsp ∸ four-slot-offset) ≢ addr
thunk-4slot-diff-from-above s rsp-sufficient addr addr≥rsp =
  <⇒≢ (<-≤-trans (thunk-4slot-below-orig s rsp-sufficient) addr≥rsp)
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

------------------------------------------------------------------------
-- D041: Raw ℕ versions of thunk helpers
------------------------------------------------------------------------

-- | Raw ℕ version: 1-slot below orig when n > two-push-offset
n∸slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ slot-size) < n
n∸slot<n-raw n n>16 = m∸slot<m n (≤-trans word+1≤pair (<⇒≤ n>16))

-- | Raw ℕ version: 2-slot below 1-slot when n > two-push-offset
n∸2slot<n∸slot-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ two-push-offset) < (n ∸ slot-size)
n∸2slot<n∸slot-raw n n>16 = ∸-monoʳ-< word<pair (<⇒≤ n>16)

-- | Raw ℕ version: 2-slot below orig when n > two-push-offset
n∸2slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ two-push-offset) < n
n∸2slot<n-raw n n>16 = <-trans (n∸2slot<n∸slot-raw n n>16) (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (<-trans)

-- | Raw ℕ version: 4-slot below orig when n > two-push-offset
n∸4slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ four-slot-offset) < n
n∸4slot<n-raw n n>16 = ≤-<-trans n∸4slot≤n∸slot (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸4slot≤n∸slot : (n ∸ four-slot-offset) ≤ (n ∸ slot-size)
    n∸4slot≤n∸slot = ∸-monoʳ-≤ n word≤frame∸word

-- | Raw ℕ version: 3-slot below orig when n > two-push-offset
n∸3slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ three-slot-offset) < n
n∸3slot<n-raw n n>16 = ≤-<-trans n∸3slot≤n∸slot (n∸slot<n-raw n n>16)
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    n∸3slot≤n∸slot : (n ∸ three-slot-offset) ≤ (n ∸ slot-size)
    n∸3slot≤n∸slot = ∸-monoʳ-≤ n word≤regs

-- | Raw ℕ version: 3-slot below < 1-slot below when n > three-slot-offset
n∸3slot<n∸slot-raw : ∀ (n : ℕ) → n > three-slot-offset → (n ∸ three-slot-offset) < (n ∸ slot-size)
n∸3slot<n∸slot-raw n n>24 = ∸-monoʳ-< word<regs (<⇒≤ n>24)

-- | Identity: (n ∸ four-slot-offset) + slot-size ≡ n ∸ three-slot-offset when n ≥ 32
-- Uses slot1-plus-word≡slot2 from Arithmetic
n∸4slot+slot≡n∸3slot : ∀ (n : ℕ) → four-slot-offset ≤ n → (n ∸ four-slot-offset) +ℕ slot-size ≡ n ∸ three-slot-offset
n∸4slot+slot≡n∸3slot = slot1-plus-word≡slot2

-- | Raw ℕ version: 4-slot below orig + slot-size < orig when n > two-push-offset
n∸4slot+slot<n-raw : ∀ (n : ℕ) → n > two-push-offset → (n ∸ four-slot-offset) +ℕ slot-size < n
n∸4slot+slot<n-raw n n>16 = <-≤-trans step-slot<step-2slot step-2slot≤n
  where
    open import Data.Nat.Properties using (<-≤-trans; +-monoˡ-≤; +-monoʳ-<; ∸-monoʳ-≤; m∸n+n≡m)
    step-slot<step-2slot : (n ∸ four-slot-offset) +ℕ slot-size < (n ∸ four-slot-offset) +ℕ two-push-offset
    step-slot<step-2slot = +-monoʳ-< (n ∸ four-slot-offset) word<pair
    n∸4slot≤n∸2slot : (n ∸ four-slot-offset) ≤ (n ∸ two-push-offset)
    n∸4slot≤n∸2slot = ∸-monoʳ-≤ n pair≤frame∸word
    step-2slot≤n∸2slot+2slot : (n ∸ four-slot-offset) +ℕ two-push-offset ≤ (n ∸ two-push-offset) +ℕ two-push-offset
    step-2slot≤n∸2slot+2slot = +-monoˡ-≤ two-push-offset n∸4slot≤n∸2slot
    2slot≤n : two-push-offset ≤ n
    2slot≤n = <⇒≤ n>16
    n∸2slot+2slot≡n : (n ∸ two-push-offset) +ℕ two-push-offset ≡ n
    n∸2slot+2slot≡n = m∸n+n≡m 2slot≤n
    step-2slot≤n : (n ∸ four-slot-offset) +ℕ two-push-offset ≤ n
    step-2slot≤n = subst ((n ∸ four-slot-offset) +ℕ two-push-offset ≤_) n∸2slot+2slot≡n step-2slot≤n∸2slot+2slot

-- | Subtraction with positive n gives different result
∸-gives-different : ∀ m n → m > 0 → n > 0 → m ∸ n ≢ m
∸-gives-different zero _ () _
∸-gives-different (suc m) zero _ ()
∸-gives-different (suc m) (suc n) _ _ eq with suc n ≤? suc m
... | yes n≤m = <⇒≢ m∸n<m eq
  where
    z<s : 0 < suc n
    z<s = s≤s z≤n
    m∸n<m : suc m ∸ suc n < suc m
    m∸n<m = ∸-monoʳ-< z<s n≤m
... | no ¬n≤m = 0≢suc m∸n≡0-then-eq
  where
    -- ≰⇒> gives suc m < suc n, which is s≤s (m < n)
    -- <⇒≤ then gives suc m ≤ suc n, which is s≤s (m ≤ n)
    sucm≤sucn : suc m ≤ suc n
    sucm≤sucn = <⇒≤ (≰⇒> ¬n≤m)
    m≤n : m ≤ n
    m≤n with sucm≤sucn
    ... | s≤s le = le
    m∸n≡0 : m ∸ n ≡ 0
    m∸n≡0 = m≤n⇒m∸n≡0 m≤n
    0≢suc : 0 ≢ suc m
    0≢suc ()
    m∸n≡0-then-eq : 0 ≡ suc m
    m∸n≡0-then-eq = trans (sym m∸n≡0) eq

-- | Subtraction with positive n gives smaller result
∸-gives-smaller : ∀ m n → m > 0 → n > 0 → m ∸ n < m
∸-gives-smaller (suc m′) (suc n′) _ _ = s≤s (m∸n≤m m′ n′)

-- | Subtraction composition (wraps ∸-+-assoc from stdlib)
∸-∸-compose : ∀ m a b → (m ∸ a) ∸ b ≡ m ∸ (a +ℕ b)
∸-∸-compose m a b = ∸-+-assoc m a b

-- | Named composition: two pushes compose to two-push-offset
push-push-eq : ∀ m → (m ∸ push-offset) ∸ push-offset ≡ m ∸ two-push-offset
push-push-eq m = ∸-+-assoc m push-offset push-offset

-- | Named composition: thunk frame from two-push + local allocation
thunk-frame-eq : ∀ m → (m ∸ two-push-offset) ∸ thunk-local-size ≡ m ∸ thunk-frame-size
thunk-frame-eq m = ∸-+-assoc m two-push-offset thunk-local-size

------------------------------------------------------------------------
-- Pair/SeqExec Arithmetic Helpers (D041: migrate from SeqExec)
------------------------------------------------------------------------

-- | Different offsets give different addresses (when m is large enough)
-- If a < b and m ≥ b, then m ∸ b < m ∸ a, so they're different
∸-different-offsets : ∀ m a b → a < b → m ≥ b → m ∸ b ≢ m ∸ a
∸-different-offsets m a b a<b m≥b eq = <⇒≢ (∸-monoʳ-< a<b m≥b) eq

-- Specific instances for SeqExec pair setup
-- m ∸ two-push-offset ≢ m ∸ slot-size when m > two-push-offset
-- Note: slot-size < two-push-offset means 9 ≤ 16, requiring s≤s^9 z≤n
∸two-slot≢∸one-slot : ∀ m → m > two-push-offset → m ∸ two-push-offset ≢ m ∸ push-offset
∸two-slot≢∸one-slot m m>16 = ∸-different-offsets m push-offset two-push-offset word<pair (<⇒≤ m>16)

-- m ∸ three-slot-offset ≢ m ∸ slot-size when m > three-slot-offset
∸three-slot≢∸one-slot : ∀ m → m > three-slot-offset → m ∸ three-slot-offset ≢ m ∸ push-offset
∸three-slot≢∸one-slot m m>24 = ∸-different-offsets m push-offset three-slot-offset word<regs (<⇒≤ m>24)

-- m ∸ three-slot-offset ≢ m ∸ two-push-offset when m > three-slot-offset
∸three-slot≢∸two-slot : ∀ m → m > three-slot-offset → m ∸ three-slot-offset ≢ m ∸ two-push-offset
∸three-slot≢∸two-slot m m>24 = ∸-different-offsets m two-push-offset three-slot-offset pair<regs (<⇒≤ m>24)

