------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInvariant
--
-- Region-based stack invariants for x86-64 execution.
--
-- Uses the abstract memory regions model from D041 instead of concrete
-- address ordering.
--
-- KEY APPROACH:
-- Track region-of r15, prove disjointness from region membership
--
-- USAGE:
-- During normal execution: r15 = 0 or r15 = heap address
-- During apply thunk: r15 = code-ptr (temporarily in Code region)
-- Memory disjointness: stack writes don't touch heap or code
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInvariant where

open import Once.Type
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

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

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; ∸-+-assoc; +-∸-assoc; m+n∸n≡m; ≤-trans; +-monoʳ-≤; m∸n≤m; ≤-refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- R15 Region Tracking
------------------------------------------------------------------------

-- | Track what region r15 currently points to
-- This replaces the ordering-based StackInvariant for r15
data R15Status (s : State) : Set where
  -- r15 = 0 (unused, doesn't point to any region)
  r15-unused : readReg (regs s) r15 ≡ 0 → R15Status s

  -- r15 points to heap (e.g., closure pointer, data structure)
  r15-in-heap : region-of (readReg (regs s) r15) ≡ heap → R15Status s

  -- r15 points to code (e.g., during apply when holding code-ptr)
  r15-in-code : region-of (readReg (regs s) r15) ≡ code → R15Status s

  -- r15 points to stack (e.g., during Pair where r15 = result address)
  -- r15 is a slot in some frame, identified by frame and slot index.
  -- The frame-rsp-bound ensures writes below current rsp don't affect r15:
  --   write at (rsp - k) has frame addr < rsp ≤ frame addr → disjoint
  -- This is the key invariant for nested IR execution in Pair.
  r15-in-stack : (frame : StackPointer) →
                 (slot : ℕ) →
                 readReg (regs s) r15 ≡ slot-addr frame slot →
                 sp-addr frame ≥ readReg (regs s) rsp →  -- frame allocated at or above current rsp
                 R15Status s

------------------------------------------------------------------------
-- Stack Capacity (replaces rsp > 16)
------------------------------------------------------------------------

-- | Abstract stack capacity: stack can accommodate n more slots
-- Each slot is 8 bytes (one word on x86-64)
-- This replaces concrete bounds like `rsp > 16`
record StackCapacity (s : State) (n : ℕ) : Set where
  field
    -- rsp points to stack region
    rsp-in-stack : region-of (readReg (regs s) rsp) ≡ stack

    -- rsp has sufficient space for n slots (concrete bound)
    -- This bridges abstract capacity to concrete X86 bounds
    rsp-sufficient : readReg (regs s) rsp > n *ℕ 8

    -- After allocating n slots, still in stack region
    -- (This is the abstract version of "enough space")
    capacity-maintained : ∀ k → k ≤ n →
      region-of (readReg (regs s) rsp ∸ (k *ℕ 8)) ≡ stack

open StackCapacity public

------------------------------------------------------------------------
-- Stack Capacity Operations
------------------------------------------------------------------------

-- NOTE: initial-capacity postulate REMOVED
-- Capacity now flows from rsp-bound-to-capacity with explicit rsp-in-stack evidence,
-- or from capacity operations that preserve rsp-in-stack.
-- The initial rsp-in-stack evidence comes from the program entry precondition.

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
-- Precondition: had capacity (suc n)
-- Postcondition: have capacity n
-- PROVEN: The key is (rsp - 8) - (k*8) = rsp - ((1+k)*8)
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

    -- new-rsp is in stack (old-rsp - 8 is in stack via capacity for k=1)
    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 1 (s≤s z≤n))

    -- old-rsp > (suc n) * 8 = 8 + n*8, so old-rsp - 8 > n*8
    rsp'-sufficient : new-rsp > n *ℕ 8
    rsp'-sufficient = subst (_> n *ℕ 8) (sym rsp-eq) sub-lemma
      where
        open import Data.Nat.Properties using (≤-<-trans; m≤m+n; +-cancelʳ-<; +-comm)

        -- old-rsp > (suc n) * 8, i.e., old-rsp > 8 + n*8
        old-bound : old-rsp > 8 +ℕ n *ℕ 8
        old-bound = rsp-sufficient cap

        -- old-rsp ≥ 8 (from old-rsp > 8 + n*8 ≥ 8)
        8≤old : 8 ≤ old-rsp
        8≤old = <⇒≤ (≤-<-trans (m≤m+n 8 (n *ℕ 8)) old-bound)

        -- (old-rsp - 8) + 8 = old-rsp
        old-rsp-eq : (old-rsp ∸ 8) +ℕ 8 ≡ old-rsp
        old-rsp-eq = m∸n+n≡m 8≤old

        -- Rewrite old-bound to use n*8 + 8 instead of 8 + n*8
        old-bound' : old-rsp > n *ℕ 8 +ℕ 8
        old-bound' = subst (old-rsp >_) (+-comm 8 (n *ℕ 8)) old-bound

        -- old-rsp - 8 > n*8 follows from old-rsp > n*8 + 8
        -- Using: (old-rsp - 8) + 8 = old-rsp > n*8 + 8
        -- By +-cancelʳ-<: n + o < m + o → n < m
        sub-lemma : old-rsp ∸ 8 > n *ℕ 8
        sub-lemma = +-cancelʳ-< 8 (n *ℕ 8) (old-rsp ∸ 8) bound-step
          where
            -- Need: n*8 + 8 < (old-rsp - 8) + 8
            bound-step : n *ℕ 8 +ℕ 8 < (old-rsp ∸ 8) +ℕ 8
            bound-step = subst (n *ℕ 8 +ℕ 8 <_) (sym old-rsp-eq) old-bound'

    -- For capacity, we need: region-of (new-rsp - k*8) = stack for k ≤ n
    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n =
      let -- Show (1 + k) ≤ suc n
          1+k≤sn : (1 +ℕ k) ≤ suc n
          1+k≤sn = s≤s k≤n
          -- Use old capacity at index (1 + k)
          old-cap-at-1+k : region-of (old-rsp ∸ ((1 +ℕ k) *ℕ 8)) ≡ stack
          old-cap-at-1+k = capacity-maintained cap (1 +ℕ k) 1+k≤sn
          -- Show new-rsp - k*8 = old-rsp - (8 + k*8)
          step1 : (old-rsp ∸ 8) ∸ (k *ℕ 8) ≡ old-rsp ∸ (8 +ℕ k *ℕ 8)
          step1 = ∸-+-assoc old-rsp 8 (k *ℕ 8)
          -- Show 8 + k*8 = (1 + k) * 8
          arith-eq : 8 +ℕ k *ℕ 8 ≡ (1 +ℕ k) *ℕ 8
          arith-eq = refl
          -- Combine
          addr-eq : new-rsp ∸ (k *ℕ 8) ≡ old-rsp ∸ ((1 +ℕ k) *ℕ 8)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ 8)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-1+k

-- | After pop (rsp += 8), capacity increases by 1
-- Precondition: had capacity n, and new rsp is in stack
-- Postcondition: have capacity (suc n)
-- NOTE: new-rsp-in-stack is required because we can't derive it from old rsp.
-- At call sites, this comes from the caller's capacity before the push.
-- PROVEN: The key is (rsp + 8) - (k*8) = rsp - ((k-1)*8) for k ≥ 1
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

    -- old-rsp > n*8, so new-rsp = old-rsp + 8 > n*8 + 8 = (suc n)*8
    rsp'-sufficient : new-rsp > (suc n) *ℕ 8
    rsp'-sufficient = subst (_> (suc n) *ℕ 8) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        -- old-rsp > n*8, so old-rsp + 8 > n*8 + 8
        step1 : old-rsp +ℕ 8 > n *ℕ 8 +ℕ 8
        step1 = +-monoˡ-< 8 (rsp-sufficient cap)
        -- n*8 + 8 = 8 + n*8 = (suc n)*8
        add-lemma : old-rsp +ℕ 8 > (suc n) *ℕ 8
        add-lemma = subst (old-rsp +ℕ 8 >_) (+-comm (n *ℕ 8) 8) step1

    -- For capacity: need region-of (new-rsp - k*8) = stack for k ≤ suc n
    -- new-rsp - k*8 = (old-rsp + 8) - k*8
    -- For k = 0: new-rsp (provided by new-rsp-in-stack)
    -- For k ≥ 1: = old-rsp - (k-1)*8 (by arithmetic, use old capacity)
    cap-maintained : ∀ k → k ≤ suc n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack  -- new-rsp ∸ 0 = new-rsp by computation
    cap-maintained (suc k) (s≤s k≤n) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        -- old capacity at index k: region-of (old-rsp - k*8) = stack
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ 8)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        -- Show: (old-rsp + 8) - (suc k)*8 = old-rsp - k*8
        -- (suc k)*8 = 8 + k*8
        -- (old-rsp + 8) - (8 + k*8) = ((old-rsp + 8) - 8) - k*8 = old-rsp - k*8
        -- ∸-+-assoc gives (m ∸ n) ∸ o ≡ m ∸ (n + o), need sym for the other direction
        step1 : (old-rsp +ℕ 8) ∸ (8 +ℕ k *ℕ 8) ≡ ((old-rsp +ℕ 8) ∸ 8) ∸ (k *ℕ 8)
        step1 = sym (∸-+-assoc (old-rsp +ℕ 8) 8 (k *ℕ 8))
        step2 : (old-rsp +ℕ 8) ∸ 8 ≡ old-rsp
        step2 = m+n∸n≡m old-rsp 8
        arith-eq : (old-rsp +ℕ 8) ∸ ((suc k) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        arith-eq = trans step1 (cong (_∸ (k *ℕ 8)) step2)
        -- Combine via substitution
        addr-eq : new-rsp ∸ ((suc k) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        addr-eq = trans (cong (λ r → r ∸ ((suc k) *ℕ 8)) rsp-eq) arith-eq

-- | After sub rsp, 16 (rsp -= 16), capacity decreases by 2
-- PROVEN: The key is (rsp - 16) - (k*8) = rsp - ((2+k)*8)
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

    -- new-rsp is in stack (old-rsp - 16 is in stack via capacity for k=2)
    rsp'-in-stack : region-of new-rsp ≡ stack
    rsp'-in-stack = trans (cong region-of rsp-eq) (capacity-maintained cap 2 (s≤s (s≤s z≤n)))

    -- old-rsp > (suc (suc n)) * 8 = 16 + n*8, so old-rsp - 16 > n*8
    rsp'-sufficient : new-rsp > n *ℕ 8
    rsp'-sufficient = subst (_> n *ℕ 8) (sym rsp-eq) sub-lemma
      where
        -- old-rsp > (suc (suc n)) * 8 = 16 + n*8
        old-bound : old-rsp > 16 +ℕ n *ℕ 8
        old-bound = rsp-sufficient cap

        -- old-rsp ≥ 16
        16≤old : 16 ≤ old-rsp
        16≤old = <⇒≤ (≤-<-trans (m≤m+n 16 (n *ℕ 8)) old-bound)

        -- (old-rsp - 16) + 16 = old-rsp
        old-rsp-eq : (old-rsp ∸ 16) +ℕ 16 ≡ old-rsp
        old-rsp-eq = m∸n+n≡m 16≤old

        -- Rewrite to n*8 + 16
        old-bound' : old-rsp > n *ℕ 8 +ℕ 16
        old-bound' = subst (old-rsp >_) (+-comm 16 (n *ℕ 8)) old-bound

        -- old-rsp - 16 > n*8
        sub-lemma : old-rsp ∸ 16 > n *ℕ 8
        sub-lemma = +-cancelʳ-< 16 (n *ℕ 8) (old-rsp ∸ 16) bound-step
          where
            bound-step : n *ℕ 8 +ℕ 16 < (old-rsp ∸ 16) +ℕ 16
            bound-step = subst (n *ℕ 8 +ℕ 16 <_) (sym old-rsp-eq) old-bound'

    -- For capacity, we need: region-of (new-rsp - k*8) = stack for k ≤ n
    -- new-rsp - k*8 = (old-rsp - 16) - k*8 = old-rsp - (16 + k*8) = old-rsp - (2+k)*8
    -- Since k ≤ n, we have 2+k ≤ 2+n = suc (suc n), so by old capacity this is in stack
    cap-maintained : ∀ k → k ≤ n → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n =
      let -- Show (2 + k) ≤ suc (suc n)
          2+k≤ssn : (2 +ℕ k) ≤ suc (suc n)
          2+k≤ssn = s≤s (s≤s k≤n)
          -- Use old capacity at index (2 + k)
          old-cap-at-2+k : region-of (old-rsp ∸ ((2 +ℕ k) *ℕ 8)) ≡ stack
          old-cap-at-2+k = capacity-maintained cap (2 +ℕ k) 2+k≤ssn
          -- Show new-rsp - k*8 = old-rsp - (16 + k*8)
          -- Using ∸-+-assoc: m ∸ n ∸ o ≡ m ∸ (n + o)
          step1 : (old-rsp ∸ 16) ∸ (k *ℕ 8) ≡ old-rsp ∸ (16 +ℕ k *ℕ 8)
          step1 = ∸-+-assoc old-rsp 16 (k *ℕ 8)
          -- Show 16 + k*8 = (2 + k) * 8 = 2*8 + k*8
          -- We need: 16 + k*8 ≡ (2 + k) * 8
          -- Note: (2 + k) * 8 = 8 + 8 + k * 8 = 16 + k * 8 (by distributivity)
          arith-eq : 16 +ℕ k *ℕ 8 ≡ (2 +ℕ k) *ℕ 8
          arith-eq = refl  -- Should compute
          -- Combine: new-rsp - k*8 = old-rsp - (2+k)*8
          addr-eq : new-rsp ∸ (k *ℕ 8) ≡ old-rsp ∸ ((2 +ℕ k) *ℕ 8)
          addr-eq = trans (cong (λ r → r ∸ (k *ℕ 8)) rsp-eq)
                          (trans step1 (cong (old-rsp ∸_) arith-eq))
      in trans (cong region-of addr-eq) old-cap-at-2+k

-- | After add rsp, 16 (rsp += 16), capacity increases by 2
-- Precondition: had capacity n, and new rsp is in stack
-- Postcondition: have capacity (suc (suc n))
-- NOTE: new-rsp-in-stack is required because we can't derive it from old rsp.
-- PROVEN: The key is (rsp + 16) - (k*8) = rsp - ((k-2)*8) for k ≥ 2
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

    -- old-rsp > n*8, so new-rsp = old-rsp + 16 > n*8 + 16 = (suc (suc n))*8
    rsp'-sufficient : new-rsp > (suc (suc n)) *ℕ 8
    rsp'-sufficient = subst (_> (suc (suc n)) *ℕ 8) (sym rsp-eq) add-lemma
      where
        open import Data.Nat.Properties using (+-monoˡ-<)
        -- old-rsp > n*8, so old-rsp + 16 > n*8 + 16
        step1 : old-rsp +ℕ 16 > n *ℕ 8 +ℕ 16
        step1 = +-monoˡ-< 16 (rsp-sufficient cap)
        -- n*8 + 16 = 16 + n*8 = (suc (suc n))*8
        add-lemma : old-rsp +ℕ 16 > (suc (suc n)) *ℕ 8
        add-lemma = subst (old-rsp +ℕ 16 >_) (+-comm (n *ℕ 8) 16) step1

    -- For k = 0: new-rsp (from new-rsp-in-stack)
    -- For k = 1: new-rsp - 8 = old-rsp + 8, need separate proof
    -- For k ≥ 2: new-rsp - k*8 = old-rsp - (k-2)*8
    cap-maintained : ∀ k → k ≤ suc (suc n) → region-of (new-rsp ∸ (k *ℕ 8)) ≡ stack
    cap-maintained zero _ = new-rsp-in-stack  -- new-rsp ∸ 0 = new-rsp by computation
    cap-maintained 1 _ = stack-sub-preserves-region new-rsp 8 new-rsp-in-stack 8≤new-rsp
      where
        open import Data.Nat.Properties using (<⇒≤; +-monoˡ-<; <-trans)
        -- old-rsp > 0 follows from old-rsp > n*8 ≥ 0
        rsp>0 : old-rsp > 0
        rsp>0 = ≤-trans (s≤s z≤n) (rsp-sufficient cap)
        -- old-rsp + 16 > 0 + 16 = 16 > 8
        step1 : old-rsp +ℕ 16 > 16
        step1 = +-monoˡ-< 16 rsp>0
        -- 16 > 8
        step2 : 16 > 8
        step2 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        -- old-rsp + 16 > 8 by transitivity
        new-rsp-bound : new-rsp > 8
        new-rsp-bound = subst (_> 8) (sym rsp-eq) (<-trans step2 step1)
        8≤new-rsp : 8 ≤ new-rsp
        8≤new-rsp = <⇒≤ new-rsp-bound
    cap-maintained (suc (suc k)) (s≤s (s≤s k≤n)) = trans (cong region-of addr-eq) old-cap-at-k
      where
        open import Data.Nat.Properties using (m+n∸n≡m)
        -- old capacity at index k: region-of (old-rsp - k*8) = stack
        old-cap-at-k : region-of (old-rsp ∸ (k *ℕ 8)) ≡ stack
        old-cap-at-k = capacity-maintained cap k k≤n
        -- Show: (old-rsp + 16) - (suc (suc k))*8 = old-rsp - k*8
        -- (suc (suc k))*8 = 16 + k*8
        -- (old-rsp + 16) - (16 + k*8) = ((old-rsp + 16) - 16) - k*8 = old-rsp - k*8
        -- ∸-+-assoc gives (m ∸ n) ∸ o ≡ m ∸ (n + o), need sym for the other direction
        step1 : (old-rsp +ℕ 16) ∸ (16 +ℕ k *ℕ 8) ≡ ((old-rsp +ℕ 16) ∸ 16) ∸ (k *ℕ 8)
        step1 = sym (∸-+-assoc (old-rsp +ℕ 16) 16 (k *ℕ 8))
        step2 : (old-rsp +ℕ 16) ∸ 16 ≡ old-rsp
        step2 = m+n∸n≡m old-rsp 16
        arith-eq : (old-rsp +ℕ 16) ∸ ((suc (suc k)) *ℕ 8) ≡ old-rsp ∸ (k *ℕ 8)
        arith-eq = trans step1 (cong (_∸ (k *ℕ 8)) step2)
        -- Combine via substitution
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
  where
    open import Data.Nat using (s≤s; z≤n)

-- | With capacity n ≥ 1, address rsp - 8 is in stack region
slot-1-addr-in-stack : ∀ (s : State) →
  StackCapacity s 1 →
  region-of (readReg (regs s) rsp ∸ 8) ≡ stack
slot-1-addr-in-stack s cap = capacity-maintained cap 1 (s≤s z≤n)
  where
    open import Data.Nat using (s≤s; z≤n)

------------------------------------------------------------------------
-- Combined Region Lemmas for Stack Operations
--
-- These encapsulate arithmetic internally, providing pure region facts
-- at the API level. No arithmetic comparisons leak to callers.
------------------------------------------------------------------------

-- | After sub rsp 16, both write addresses (new-rsp and new-rsp+8) are in stack
-- This is the pure region interface for inl/inr operations
-- Internally: new-rsp = rsp - 16, new-rsp + 8 = rsp - 8 (arithmetic hidden)
alloc-2-slots-addrs-in-stack : ∀ (s : State) →
  StackCapacity s 2 →
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ 16
  in (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ 8) ≡ stack)
alloc-2-slots-addrs-in-stack s cap =
  let rsp-val = readReg (regs s) rsp
      new-rsp = rsp-val ∸ 16
      -- First write address: new-rsp = rsp - 16
      write1-in-stack : region-of new-rsp ≡ stack
      write1-in-stack = slot-2-addr-in-stack s cap
      -- Second write address: new-rsp + 8
      -- Internally we know: (rsp - 16) + 8 = rsp - 8 (when rsp ≥ 16)
      -- We use subst to connect new-rsp + 8 to rsp - 8
      write2-in-stack : region-of (new-rsp +ℕ 8) ≡ stack
      write2-in-stack = subst (λ a → region-of a ≡ stack)
                              (sym (alloc-2-slots-second-addr-eq rsp-val (cap-to-inl-inr-rsp-bound cap)))
                              (slot-1-addr-in-stack s (capacity-weaken cap))
  in write1-in-stack , write2-in-stack
  where
    open import Data.Nat using (s≤s; z≤n)
    open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤)

    -- Helper: StackCapacity 2 implies sufficient rsp for inl/inr operations
    -- PROVEN: rsp > 16 implies rsp ≥ 16
    cap-to-inl-inr-rsp-bound : StackCapacity s 2 → readReg (regs s) rsp ≥ 16
    cap-to-inl-inr-rsp-bound cap = <⇒≤ (rsp-sufficient cap)

    -- Helper: weaken capacity 2 to capacity 1
    capacity-weaken : StackCapacity s 2 → StackCapacity s 1
    capacity-weaken cap2 = record
      { rsp-in-stack = rsp-in-stack cap2
      ; rsp-sufficient = <-trans rsp>8 (rsp-sufficient cap2)
      ; capacity-maintained = λ k k≤1 →
          capacity-maintained cap2 k (≤-trans k≤1 (s≤s z≤n))
      }
      where
        open import Data.Nat.Properties using (<-trans; n<1+n)
        -- 8 < 16, i.e., 9 ≤ 16 (need 9 s≤s constructors)
        rsp>8 : 8 < 16
        rsp>8 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

    -- The key arithmetic identity (hidden from callers)
    -- After allocating 2 slots, adding 1 slot offset gives slot-1 address
    alloc-2-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ 16 → (rsp-val ∸ 16) +ℕ 8 ≡ rsp-val ∸ 8
    alloc-2-slots-second-addr-eq rsp-val rsp≥16 = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits-after-1-slot)
      where
        -- (rsp - 16) + 8 = (rsp - 8 - 8) + 8 = rsp - 8
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        -- One word fits after popping 1 slot
        word-fits-after-1-slot : 8 ≤ rsp-val ∸ 8
        word-fits-after-1-slot = ∸-monoˡ-≤ 8 rsp≥16

-- | Stack writes at rsp - k*8 don't affect heap addresses (when we have capacity)
stack-write-disjoint-from-heap : ∀ (s : State) (n k : ℕ) (heap-addr : Addr) →
  StackCapacity s n →
  k ≤ n →
  region-of heap-addr ≡ heap →
  readReg (regs s) rsp ∸ (k *ℕ 8) ≢ heap-addr
stack-write-disjoint-from-heap s n k heap-addr cap k≤n heap-proof =
  stack-heap-disjoint (readReg (regs s) rsp ∸ (k *ℕ 8)) heap-addr
                      (capacity-maintained cap k k≤n) heap-proof

------------------------------------------------------------------------
-- Pair-specific: (rsp - 40) + 8 is in stack region
--
-- During Pair setup, r15 is set to rsp - 40. Then (r15 + 8) is used for
-- storing the second element. This is (rsp - 40) + 8 = rsp - 32.
-- With capacity 5 (from rsp ≥ 40), this is in the stack region.
------------------------------------------------------------------------

-- | rsp - 40 is in stack region when we have capacity 5
-- This is the base address for pair's r15 register
pair-r15-in-stack : ∀ (s : State) →
  StackCapacity s 5 →
  region-of (readReg (regs s) rsp ∸ 40) ≡ stack
pair-r15-in-stack s cap = capacity-maintained cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  where
    open import Data.Nat using (s≤s; z≤n)

-- | (rsp - 40) + 8 is in stack region when we have capacity 5
-- This encapsulates the arithmetic: (rsp ∸ 40) +ℕ 8 ≡ rsp ∸ 32 when rsp ≥ 40
pair-second-slot-in-stack : ∀ (s : State) →
  StackCapacity s 5 →
  region-of ((readReg (regs s) rsp ∸ 40) +ℕ 8) ≡ stack
pair-second-slot-in-stack s cap =
  subst (λ a → region-of a ≡ stack)
        (sym (alloc-5-slots-second-addr-eq rsp-val (cap-to-pair-setup-rsp-bound cap)))
        (capacity-maintained cap 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
  where
    open import Data.Nat using (s≤s; z≤n)
    open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤)

    open import Data.Nat.Properties using (<⇒≤) renaming () -- for cap-to-pair-setup-rsp-bound

    rsp-val = readReg (regs s) rsp

    -- Helper: StackCapacity 5 implies sufficient rsp for pair setup
    -- PROVEN: rsp > 40 implies rsp ≥ 40
    cap-to-pair-setup-rsp-bound : StackCapacity s 5 → readReg (regs s) rsp ≥ 40
    cap-to-pair-setup-rsp-bound cap = <⇒≤ (rsp-sufficient cap)

    -- The key arithmetic identity (hidden from callers)
    -- After allocating 5 slots, adding 1 slot offset gives slot-4 address
    alloc-5-slots-second-addr-eq : ∀ (rsp-val : ℕ) → rsp-val ≥ 40 → (rsp-val ∸ 40) +ℕ 8 ≡ rsp-val ∸ 32
    alloc-5-slots-second-addr-eq rsp-val rsp≥40 = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits-after-4-slots)
      where
        -- (rsp - 40) + 8 = (rsp - 32 - 8) + 8 = rsp - 32
        step1 : rsp-val ∸ 40 ≡ (rsp-val ∸ 32) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 32 8)
        -- One word fits after 4 slots
        word-fits-after-4-slots : 8 ≤ rsp-val ∸ 32
        word-fits-after-4-slots = ∸-monoˡ-≤ 32 rsp≥40

------------------------------------------------------------------------
-- Converting from rsp bounds to StackCapacity (forward declarations)
------------------------------------------------------------------------

-- | General conversion: rsp > n*8 gives StackCapacity s n
-- Takes rsp-in-stack as explicit evidence (no new axioms)
-- Uses stack-sub-preserves-region from MemoryRegions
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

    -- Arithmetic: k ≤ n ∧ rsp > n*8 → k*8 ≤ rsp
    -- Proof: k*8 ≤ n*8 (by *-monoˡ-≤) < rsp (given), so k*8 < rsp, so k*8 ≤ rsp
    k*8≤rsp : ∀ k → k ≤ n → k *ℕ 8 ≤ rsp-val
    k*8≤rsp k k≤n = <⇒≤ (≤-<-trans (*-monoˡ-≤ 8 k≤n) rsp-bound)

    -- capacity-maintained: for all k ≤ n, region-of (rsp - k*8) = stack
    cap-maintained : ∀ k → k ≤ n → region-of (rsp-val ∸ (k *ℕ 8)) ≡ stack
    cap-maintained k k≤n = stack-sub-preserves-region rsp-val (k *ℕ 8) rsp-in-stack (k*8≤rsp k k≤n)

-- | Convert rsp > 40 to StackCapacity 5
-- Takes rsp-in-stack as explicit evidence
-- Uses rsp-bound-to-capacity with n = 5 (since 5 * 8 = 40)
rsp-to-capacity-5 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 40 →
  StackCapacity s 5
rsp-to-capacity-5 s rsp-in-stack rsp>40 = rsp-bound-to-capacity s 5 rsp-in-stack rsp>40

-- | Get StackCapacity for Pair setup from runtime rsp bound
-- Pair needs 5 slots. Encapsulates arithmetic conversion.
pair-stack-capacity : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 40 →
  StackCapacity s 5
pair-stack-capacity = rsp-to-capacity-5

------------------------------------------------------------------------
-- Abstract Frame Creation (for proof layer)
------------------------------------------------------------------------
-- These functions create StackPointers from StackCapacity, hiding arithmetic.
-- The proof layer uses these to work with frames abstractly.
-- Arithmetic is ONLY in this file (instantiation layer).

-- | Create a StackPointer for a frame at offset k slots below current rsp.
-- k=0 gives frame at current rsp
-- k=1 gives frame at rsp-8 (one slot below)
-- k=3 gives frame at rsp-24 (three slots below, used for rbp in pair)
-- k=5 gives frame at rsp-40 (five slots below, used for r15 in pair)
make-frame-at-slot : ∀ {n} (s : State) → StackCapacity s n → (k : ℕ) → k ≤ n → StackPointer
make-frame-at-slot s cap k k≤n = record
  { addr = readReg (regs s) rsp ∸ (k *ℕ 8)
  ; in-stack = capacity-maintained cap k k≤n
  }

-- | The frame created at slot 0 has addr = current rsp
make-frame-at-slot-0-addr : ∀ {n} (s : State) (cap : StackCapacity s n) →
  sp-addr (make-frame-at-slot s cap 0 z≤n) ≡ readReg (regs s) rsp
make-frame-at-slot-0-addr s cap = refl

-- | Frame at slot 3 has addr = rsp - 24 (used for rbp frame in pair)
make-frame-at-slot-3-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc n)))) →
  sp-addr (make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))) ≡ readReg (regs s) rsp ∸ 24
make-frame-at-slot-3-addr s cap = refl

-- | Frame at slot 5 has addr = rsp - 40 (used for r15 frame in pair)
make-frame-at-slot-5-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc (suc n)))))) →
  sp-addr (make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) ≡ readReg (regs s) rsp ∸ 40
make-frame-at-slot-5-addr s cap = refl

-- | Frames at lower slot indices have higher addresses (stack grows down)
-- slot k₁ ≤ slot k₂ implies (rsp - k₁*8) ≥ (rsp - k₂*8)
-- This enables frame-bound proofs without exposing arithmetic to proof layer.
frame-at-lower-slot-≥ : ∀ {n} (s : State) (cap : StackCapacity s n) (k₁ k₂ : ℕ)
  (k₁≤n : k₁ ≤ n) (k₂≤n : k₂ ≤ n) →
  k₁ ≤ k₂ →
  sp-addr (make-frame-at-slot s cap k₁ k₁≤n) ≥ sp-addr (make-frame-at-slot s cap k₂ k₂≤n)
frame-at-lower-slot-≥ s cap k₁ k₂ k₁≤n k₂≤n k₁≤k₂ = ∸-monoʳ-≤ (readReg (regs s) rsp) (*-monoˡ-≤ 8 k₁≤k₂)
  where
    open import Data.Nat.Properties using (∸-monoʳ-≤; *-monoˡ-≤)

-- | Pair-specific: frame at slot 3 (rbp) is ≥ frame at slot 5 (r15/rsp)
-- (rsp - 24) ≥ (rsp - 40) since 24 ≤ 40
pair-rbp-frame-≥-r15-frame : ∀ (s : State) (cap : StackCapacity s 5) →
  sp-addr (make-frame-at-slot s cap 3 (s≤s (s≤s (s≤s z≤n)))) ≥
  sp-addr (make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
pair-rbp-frame-≥-r15-frame s cap =
  frame-at-lower-slot-≥ s cap 3 5 (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
                        (s≤s (s≤s (s≤s z≤n)))

-- | Frame at slot 1 has addr = rsp - 8 (used for saved r15 in thunk)
make-frame-at-slot-1-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc n)) →
  sp-addr (make-frame-at-slot s cap 1 (s≤s z≤n)) ≡ readReg (regs s) rsp ∸ 8
make-frame-at-slot-1-addr s cap = refl

-- | Frame at slot 2 has addr = rsp - 16 (used for rbp in thunk)
make-frame-at-slot-2-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc n))) →
  sp-addr (make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))) ≡ readReg (regs s) rsp ∸ 16
make-frame-at-slot-2-addr s cap = refl

-- | Frame at slot 4 has addr = rsp - 32 (used for new rsp after thunk setup)
make-frame-at-slot-4-addr : ∀ {n} (s : State) (cap : StackCapacity s (suc (suc (suc (suc n))))) →
  sp-addr (make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n))))) ≡ readReg (regs s) rsp ∸ 32
make-frame-at-slot-4-addr s cap = refl

-- | Thunk-specific: frame at slot 2 (rbp) is ≥ frame at slot 4 (new rsp)
-- (rsp - 16) ≥ (rsp - 32) since 16 ≤ 32
thunk-rbp-frame-≥-new-rsp : ∀ (s : State) (cap : StackCapacity s 4) →
  sp-addr (make-frame-at-slot s cap 2 (s≤s (s≤s z≤n))) ≥
  sp-addr (make-frame-at-slot s cap 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))
thunk-rbp-frame-≥-new-rsp s cap =
  frame-at-lower-slot-≥ s cap 2 4 (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s (s≤s z≤n))))
                        (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Abstract Slot Region Interface (D041-compliant)
------------------------------------------------------------------------
-- The PROOF LAYER uses these functions. Type signatures contain NO arithmetic.
-- Proof layer should use: make-frame-at-slot + frame-slot-in-stack
-- Never use: pair-r15-in-stack, pair-second-slot-in-stack (contain rsp ∸ k)

-- | Any slot in a frame created from capacity is in stack region
-- This is the KEY abstraction: proof layer uses this, never sees ∸ arithmetic
frame-slot-in-stack : ∀ {n} (s : State) (cap : StackCapacity s n)
                      (k : ℕ) (k≤n : k ≤ n) (offset : ℕ) →
                      region-of (slot-addr (make-frame-at-slot s cap k k≤n) offset) ≡ stack
frame-slot-in-stack s cap k k≤n offset = slot-in-stack (make-frame-at-slot s cap k k≤n) offset

-- | Pair-specific: frame at slot 5, offset 0 (abstract version of pair-r15-in-stack)
-- Type signature uses StackPointer abstraction, not rsp ∸ 40
pair-frame-0 : (s : State) (cap : StackCapacity s 5) → StackPointer
pair-frame-0 s cap = make-frame-at-slot s cap 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

pair-frame-slot-0-in-stack : (s : State) (cap : StackCapacity s 5) →
                             region-of (slot-addr (pair-frame-0 s cap) 0) ≡ stack
pair-frame-slot-0-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 0

-- | Pair-specific: frame at slot 5, offset 1 (abstract version of pair-second-slot-in-stack)
-- Type signature uses StackPointer abstraction, not (rsp ∸ 40) +ℕ 8
pair-frame-slot-1-in-stack : (s : State) (cap : StackCapacity s 5) →
                             region-of (slot-addr (pair-frame-0 s cap) 1) ≡ stack
pair-frame-slot-1-in-stack s cap = slot-in-stack (pair-frame-0 s cap) 1

-- | Connection between abstract and concrete (for instantiation layer use only!)
-- Proof layer should NEVER use these - they expose arithmetic
pair-frame-0-addr-eq : (s : State) (cap : StackCapacity s 5) →
                       sp-addr (pair-frame-0 s cap) ≡ readReg (regs s) rsp ∸ 40
pair-frame-0-addr-eq s cap = refl

pair-frame-slot-1-addr-eq : (s : State) (cap : StackCapacity s 5) →
                            slot-addr (pair-frame-0 s cap) 1 ≡ (readReg (regs s) rsp ∸ 40) +ℕ 8
pair-frame-slot-1-addr-eq s cap = slot-addr-1-is-base+8 (pair-frame-0 s cap)

------------------------------------------------------------------------
-- Memory Disjointness from Region Membership
------------------------------------------------------------------------

-- | Stack writes don't affect r15 when r15 is in heap
stack-write-preserves-heap-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of (readReg (regs s) r15) ≡ heap →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-heap-r15 s stack-addr stack-region r15-heap =
  stack-heap-disjoint stack-addr (readReg (regs s) r15) stack-region r15-heap

-- | Stack writes don't affect r15 when r15 is in code
stack-write-preserves-code-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of (readReg (regs s) r15) ≡ code →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-code-r15 s stack-addr stack-region r15-code =
  stack-code-disjoint stack-addr (readReg (regs s) r15) stack-region r15-code

-- | Stack writes don't affect r15 when r15 is unused (r15 = 0)
-- Address 0 is not in stack region (zero-not-in-stack from MemoryRegions)

stack-write-preserves-unused-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  readReg (regs s) r15 ≡ 0 →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-unused-r15 s stack-addr stack-region r15≡0 eq =
  -- If stack-addr ≡ r15 and r15 ≡ 0, then stack-addr ≡ 0
  -- So region-of stack-addr ≡ region-of 0
  -- But region-of stack-addr ≡ stack, so region-of 0 ≡ stack
  -- This contradicts zero-not-in-stack
  let stack-addr≡0 : stack-addr ≡ 0
      stack-addr≡0 = trans eq r15≡0
      region-0≡stack : region-of 0 ≡ stack
      region-0≡stack = trans (cong region-of (sym stack-addr≡0)) stack-region
  in zero-not-in-stack region-0≡stack

-- | Stack writes in one frame don't affect r15 when r15 is in a different frame.
-- This is the key lemma for r15-in-stack case.
-- Uses frames-disjoint-slots: distinct frame addresses → disjoint slot addresses.
stack-write-preserves-instack-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  (write-slot : ℕ) →
  stack-addr ≡ slot-addr write-frame write-slot →
  (r15-frame : StackPointer) →
  (r15-slot : ℕ) →
  readReg (regs s) r15 ≡ slot-addr r15-frame r15-slot →
  sp-addr write-frame ≢ sp-addr r15-frame →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-instack-r15 s stack-addr write-frame write-slot addr-eq
                                  r15-frame r15-slot r15-eq frames-neq eq =
  -- stack-addr = slot-addr write-frame write-slot
  -- r15 = slot-addr r15-frame r15-slot
  -- write-frame.addr ≢ r15-frame.addr
  -- By frames-disjoint-slots: slot-addr write-frame write-slot ≢ slot-addr r15-frame r15-slot
  -- But stack-addr ≡ r15 → slot-addr write-frame write-slot ≡ slot-addr r15-frame r15-slot, contradiction
  frames-disjoint-slots write-frame r15-frame write-slot r15-slot frames-neq
    (trans (sym addr-eq) (trans eq r15-eq))

-- | Evidence needed for r15-in-stack case: write frame is different from r15 frame
-- For other R15Status cases, no additional evidence is needed.
FrameEvidenceFor : ∀ {s : State} → StackPointer → R15Status s → Set
FrameEvidenceFor write-frame (r15-unused _) = ⊤
FrameEvidenceFor write-frame (r15-in-heap _) = ⊤
FrameEvidenceFor write-frame (r15-in-code _) = ⊤
FrameEvidenceFor write-frame (r15-in-stack r15-frame r15-slot _ _) =
  sp-addr write-frame ≢ sp-addr r15-frame

-- | General: stack writes don't affect r15 based on R15Status
-- For r15-in-stack, requires frame identity and frames-neq evidence.
-- For other cases, pass tt for the frame evidence.
stack-write-preserves-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  (write-slot : ℕ) →
  stack-addr ≡ slot-addr write-frame write-slot →
  (r15-inv : R15Status s) →
  FrameEvidenceFor write-frame r15-inv →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-unused r15≡0) _ =
  stack-write-preserves-unused-r15 s stack-addr
    (subst (λ a → region-of a ≡ stack) (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15≡0
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-in-heap r15-heap) _ =
  stack-write-preserves-heap-r15 s stack-addr
    (subst (λ a → region-of a ≡ stack) (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15-heap
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-in-code r15-code) _ =
  stack-write-preserves-code-r15 s stack-addr
    (subst (λ a → region-of a ≡ stack) (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15-code
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq
                          (r15-in-stack r15-frame r15-slot r15-eq _) frames-neq =
  stack-write-preserves-instack-r15 s stack-addr write-frame write-slot addr-eq
                                    r15-frame r15-slot r15-eq frames-neq

------------------------------------------------------------------------
-- RbpInvariant (Frame Pointer Invariant)
------------------------------------------------------------------------

-- | Invariant: rbp points to a frame base (caller's frame)
-- Uses frame identity instead of arithmetic ordering.
-- rbp-frame identifies which frame rbp belongs to.
-- frame-bound ensures rbp's frame is at or above rsp (for frame distinctness).
record RbpInvariant (s : State) : Set where
  field
    rbp-frame : StackPointer
    rbp-is-base : readReg (regs s) rbp ≡ sp-addr rbp-frame
    frame-bound : sp-addr rbp-frame ≥ readReg (regs s) rsp

  -- Backward compatibility: derive rsp≤rbp from frame-bound + rbp-is-base
  rsp≤rbp : readReg (regs s) rsp ≤ readReg (regs s) rbp
  rsp≤rbp = subst (readReg (regs s) rsp ≤_) (sym rbp-is-base) frame-bound

open RbpInvariant public

------------------------------------------------------------------------
-- Type alias for backward compatibility
------------------------------------------------------------------------

-- | StackInvariant is now R15Status (region-based)
StackInvariant : State → Set
StackInvariant = R15Status

-- | Create StackInvariant when r15 holds a code pointer (address < prog-len)
stack-inv-for-code-ptr : ∀ (s : State) (prog-len : ℕ) →
  readReg (regs s) r15 < prog-len →
  StackInvariant s
stack-inv-for-code-ptr s prog-len r15<len = r15-in-code (pc-in-code (readReg (regs s) r15) prog-len r15<len)

-- | Create StackInvariant for state after Pair setup
-- After Pair setup: r15 = rsp (both point to pair base address)
-- This encapsulates all arithmetic in the instantiation layer.
--
-- Preconditions (from exec-pair-setup):
--   r15-eq: r15 in s-setup = rsp in s - 40
--   rsp-eq: rsp in s-setup = rsp in s - 40
--   cap: StackCapacity s 5 (sufficient stack space for Pair)
--
-- Returns: StackInvariant where r15 is identified as slot 0 of the pair frame
pair-setup-stack-inv : ∀ (s s-setup : State) →
  StackCapacity s 5 →
  readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ 40 →
  readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ 40 →
  StackInvariant s-setup
pair-setup-stack-inv s s-setup cap r15-eq rsp-eq =
  r15-in-stack pair-frame 0 r15-is-slot0 pair-frame-bound
  where
    -- region-of (s.rsp - 40) ≡ stack from capacity
    base-in-stack : region-of (readReg (regs s) rsp ∸ 40) ≡ stack
    base-in-stack = pair-r15-in-stack s cap

    -- The pair frame: StackPointer with addr = rsp - 40
    pair-frame : StackPointer
    pair-frame = record
      { addr = readReg (regs s) rsp ∸ 40
      ; in-stack = base-in-stack
      }

    -- r15 = slot-addr pair-frame 0
    -- By slot-addr-0-is-base: slot-addr pair-frame 0 = addr pair-frame = rsp - 40
    -- And r15 = rsp - 40 by r15-eq
    r15-is-slot0 : readReg (regs s-setup) r15 ≡ slot-addr pair-frame 0
    r15-is-slot0 = trans r15-eq (sym (slot-addr-0-is-base pair-frame))

    -- Frame bound: pair-frame.addr = rsp - 40 = s-setup.rsp (since both equal rsp - 40)
    -- So pair-frame.addr ≥ s-setup.rsp (actually =)
    pair-frame-bound : sp-addr pair-frame ≥ readReg (regs s-setup) rsp
    pair-frame-bound = subst (sp-addr pair-frame ≥_) (sym rsp-eq) ≤-refl

------------------------------------------------------------------------
-- Invariant preservation lemmas
------------------------------------------------------------------------

-- | StackInvariant preservation when rsp and r15 are unchanged
stack-inv-preserved-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-unchanged s s' (r15-unused r15≡0) r15-eq _ =
  r15-unused (trans r15-eq r15≡0)
stack-inv-preserved-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (trans (cong region-of r15-eq) r15-heap)
stack-inv-preserved-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (trans (cong region-of r15-eq) r15-code)
stack-inv-preserved-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq rsp-eq =
  -- r15 unchanged: s'.r15 = s.r15 = slot-addr frame slot
  -- Frame bound preserved: frame.addr ≥ s.rsp = s'.rsp
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (subst (sp-addr frame ≥_) (sym rsp-eq) frame-bound)

-- | Stack invariant preservation when r15 unchanged and rsp decreased/unchanged
-- With slot-based r15-in-stack, rsp ordering is no longer needed for preservation.
-- The signature is kept for backward compatibility with callers.
stack-inv-preserved-r15-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≤ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-r15-unchanged s s' (r15-unused r15≡0) r15-eq _ =
  r15-unused (trans r15-eq r15≡0)
stack-inv-preserved-r15-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (trans (cong region-of r15-eq) r15-heap)
stack-inv-preserved-r15-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (trans (cong region-of r15-eq) r15-code)
stack-inv-preserved-r15-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq rsp-ord =
  -- r15 unchanged: s'.r15 = s.r15 = slot-addr frame slot
  -- Frame bound strengthened: frame.addr ≥ s.rsp ≥ s'.rsp
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (≤-trans rsp-ord frame-bound)

-- | rsp > 16 preservation when rsp is unchanged
rsp-bound-preserved-unchanged : ∀ (s s' : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rsp > 16
rsp-bound-preserved-unchanged s s' rsp-sufficient rsp-eq = subst (_> 16) (sym rsp-eq) rsp-sufficient

-- | Convert rsp > 16 to StackCapacity 2
-- Takes rsp-in-stack as explicit evidence
rsp-to-capacity-2 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  StackCapacity s 2
rsp-to-capacity-2 s rsp-in-stack rsp-sufficient = rsp-bound-to-capacity s 2 rsp-in-stack rsp-sufficient

-- | Convert rsp > 32 to StackCapacity 4
-- Takes rsp-in-stack as explicit evidence
rsp-to-capacity-4 : ∀ (s : State) →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 32 →
  StackCapacity s 4
rsp-to-capacity-4 s rsp-in-stack rsp>32 = rsp-bound-to-capacity s 4 rsp-in-stack rsp>32

-- | Convert StackCapacity back to concrete bound (for compatibility)
-- This allows gradual migration - new proofs can use StackCapacity
-- while still producing rsp > 16 for old interfaces
-- PROVEN: trivial extraction of rsp-sufficient field
capacity-2-to-rsp-bound : ∀ (s : State) →
  StackCapacity s 2 →
  readReg (regs s) rsp > 16
capacity-2-to-rsp-bound s cap = rsp-sufficient cap

------------------------------------------------------------------------
-- Combined State Invariant (R15Status + StackCapacity)
------------------------------------------------------------------------

-- | Combined invariant for x86 execution state
-- This is the abstract replacement for (StackInvariant s × rsp > 16)
record AbstractStackInvariant (s : State) : Set where
  field
    r15-status : R15Status s
    capacity   : StackCapacity s 2  -- Need at least 2 slots for typical ops

open AbstractStackInvariant public

-- | Create AbstractStackInvariant from StackInvariant (= R15Status) and rsp bound
-- Takes rsp-in-stack as explicit evidence
from-old-invariants : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  AbstractStackInvariant s
from-old-invariants s stack-inv rsp-in-stack rsp-sufficient = record
  { r15-status = stack-inv  -- StackInvariant = R15Status, so identity
  ; capacity = rsp-to-capacity-2 s rsp-in-stack rsp-sufficient
  }

------------------------------------------------------------------------
-- Address disjointness proofs using regions
------------------------------------------------------------------------

-- | Prove that stack write at (rsp - 16) doesn't affect r15
-- This is the key lemma needed for memory preservation in IR proofs
-- PROVEN: Handles all R15Status cases using slot-based disjointness
stack-write-slot-2-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ 16 ≢ readReg (regs s) r15
stack-write-slot-2-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat.Properties using (m∸n≤m; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ 16
    stack-addr-in-stack = slot-2-addr-in-stack s (capacity inv)

    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

    -- rsp > 16, so rsp - 16 < rsp
    addr<rsp : stack-addr < readReg (regs s) rsp
    addr<rsp = m∸n<m' (readReg (regs s) rsp) 16 (s≤s z≤n) (rsp-sufficient (capacity inv))

    helper : R15Status s → stack-addr ≢ readReg (regs s) r15
    helper (r15-unused r15≡0) = stack-write-preserves-unused-r15 s stack-addr stack-addr-in-stack r15≡0
    helper (r15-in-heap r15-heap) = stack-write-preserves-heap-r15 s stack-addr stack-addr-in-stack r15-heap
    helper (r15-in-code r15-code) = stack-write-preserves-code-r15 s stack-addr stack-addr-in-stack r15-code
    helper (r15-in-stack r15-frame r15-slot r15-eq frame-bound) =
      -- stack-addr = rsp - 16 < rsp ≤ frame.addr (by frame-bound)
      -- So stack-addr < frame.addr, hence stack-addr ≢ frame.addr
      -- The slot-addr at r15 is in r15-frame, and stack-addr < frame.addr
      -- means write-frame would have addr < r15-frame.addr
      let write-addr = readReg (regs s) rsp ∸ 16
          addr<frame : write-addr < sp-addr r15-frame
          addr<frame = <-≤-trans addr<rsp frame-bound
          -- Create write-frame
          write-frame : StackPointer
          write-frame = record { addr = write-addr ; in-stack = stack-addr-in-stack }
          -- write-frame.addr < r15-frame.addr implies ≢
          frames-neq : sp-addr write-frame ≢ sp-addr r15-frame
          frames-neq = <⇒≢ addr<frame
      in stack-write-preserves-instack-r15 s stack-addr
           write-frame 0 (sym (slot-addr-0-is-base write-frame))
           r15-frame r15-slot r15-eq frames-neq

-- | Similarly for (rsp - 8)
-- PROVEN: Handles all R15Status cases using slot-based disjointness
stack-write-slot-1-preserves-r15 : ∀ (s : State) →
  AbstractStackInvariant s →
  readReg (regs s) rsp ∸ 8 ≢ readReg (regs s) r15
stack-write-slot-1-preserves-r15 s inv = helper (r15-status inv)
  where
    open import Data.Nat using (s≤s; z≤n)
    open import Data.Nat.Properties using (m∸n≤m; <-trans; <⇒≢; <-≤-trans)
    stack-addr = readReg (regs s) rsp ∸ 8
    stack-addr-in-stack = capacity-maintained (capacity inv) 1 (s≤s z≤n)

    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

    -- rsp > 16 > 8, so rsp > 8, hence rsp - 8 < rsp
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
-- This is cleaner than the old approach which required ordering proofs
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
-- Using region-based proof: stack addresses are in stack region,
-- r15 is in a different region (unused/heap/code)
-- PROVEN: Handles all R15Status cases without postulates
addr-diff-from-invariant : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) rsp) ≡ stack →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-r15 = readReg (regs s) r15
  in (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
addr-diff-from-invariant s stack-inv rsp-in-stack rsp-suff = diff1 , diff2
  where
    open import Data.Nat.Properties using (m∸n≤m; <-trans; <⇒≢; <-≤-trans)
    open import Data.Product using (proj₁; proj₂)
    rsp-val = readReg (regs s) rsp
    cap = rsp-to-capacity-2 s rsp-in-stack rsp-suff
    addrs-in-stack = alloc-2-slots-addrs-in-stack s cap
    write1-in-stack = proj₁ addrs-in-stack
    write2-in-stack = proj₂ addrs-in-stack
    stack-addr1 = rsp-val ∸ 16
    stack-addr2 = (rsp-val ∸ 16) +ℕ 8
    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')
    -- rsp > 16, so rsp - 16 < rsp
    addr1<rsp : stack-addr1 < rsp-val
    addr1<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-suff
    -- rsp > 16 > 8, so rsp - 8 < rsp; (rsp - 16) + 8 = rsp - 8 when rsp ≥ 16
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
          where
            open import Data.Nat.Properties using (∸-monoˡ-≤)
    -- Helper for each address
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

-- | Prove (rsp - 16) and (rsp - 8) are different from rbp
-- Uses frame-bound from RbpInvariant: rbp-frame addr ≥ rsp, so writes below rsp
-- are in a different frame from rbp.
rbp-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp = readReg (regs s) rbp
  in (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ 8) ≢ orig-rbp)
rbp-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp-diff-proof , rbp-diff-proof-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n≤m; ≤-trans)
    open import Data.Nat using (s≤s; z≤n)

    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp

    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

    -- new-rsp < rsp (allocation decreases stack pointer)
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient

    -- rbp = sp-addr rbp-frame (from rbp-is-base)
    -- frame-bound: sp-addr rbp-frame ≥ rsp
    -- So: new-rsp < rsp ≤ sp-addr rbp-frame = rbp

    -- new-rsp < rbp (by frame-bound and rbp-is-base)
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))

    -- PROVEN: new-rsp ≢ rbp
    rbp-diff-proof : new-rsp ≢ orig-rbp
    rbp-diff-proof = <⇒≢ new-rsp<rbp

    -- For (new-rsp + 8): need new-rsp + 8 < rbp
    -- new-rsp + 8 = rsp - 8
    -- rsp > 16 implies rsp > 8, so rsp - 8 < rsp ≤ rbp

    -- rsp > 8 (follows from rsp > 16)
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans bounds-lemma rsp-sufficient
      where
        bounds-lemma : 9 ≤ 17
        bounds-lemma = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

    -- rsp - 8 < rsp
    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8

    -- rsp - 8 < rbp
    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))

    -- new-rsp + 8 = rsp - 8
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit

    -- PROVEN: (new-rsp + 8) ≢ rbp
    rbp-diff-proof-2 : (new-rsp +ℕ 8) ≢ orig-rbp
    rbp-diff-proof-2 = subst (_≢ orig-rbp) (sym second-slot-eq) (<⇒≢ rsp-8<rbp)

-- | Prove (rsp - 16) and (rsp - 8) are different from (rbp + 8)
-- Uses frame-bound from RbpInvariant: rbp-frame addr ≥ rsp, so writes below rsp
-- are in a different frame from rbp, hence also different from rbp+8.
rbp+8-addr-diff-from-invariant : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp+8 = readReg (regs s) rbp +ℕ 8
  in (new-rsp ≢ orig-rbp+8) × ((new-rsp +ℕ 8) ≢ orig-rbp+8)
rbp+8-addr-diff-from-invariant s rbp-inv rsp-sufficient =
  rbp+8-diff-1 , rbp+8-diff-2
  where
    open import Data.Nat.Properties using (<⇒≢; <-≤-trans; m∸n≤m; ≤-trans; m≤m+n)
    open import Data.Nat using (s≤s; z≤n)

    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp
    orig-rbp+8 = orig-rbp +ℕ 8

    -- Use rbp-addr-diff-from-invariant for new-rsp < rbp and new-rsp+8 < rbp
    rbp-diffs = rbp-addr-diff-from-invariant s rbp-inv rsp-sufficient

    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

    -- new-rsp < rsp (allocation decreases stack pointer)
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient

    -- new-rsp < rbp (via frame-bound)
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))

    -- new-rsp < rbp ≤ rbp+8, so new-rsp < rbp+8
    new-rsp<rbp+8 : new-rsp < orig-rbp+8
    new-rsp<rbp+8 = ≤-trans new-rsp<rbp (m≤m+n orig-rbp 8)

    -- PROVEN: new-rsp ≢ rbp+8
    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 = <⇒≢ new-rsp<rbp+8

    -- For (new-rsp + 8): reuse rsp-8 < rbp from rbp-addr-diff-from-invariant pattern
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient

    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8

    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))

    -- (rsp - 8) < rbp ≤ rbp+8
    rsp-8<rbp+8 : rsp-val ∸ 8 < orig-rbp+8
    rsp-8<rbp+8 = ≤-trans rsp-8<rbp (m≤m+n orig-rbp 8)

    -- new-rsp + 8 = rsp - 8
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (m∸n+n≡m; ∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit

    -- PROVEN: (new-rsp + 8) ≢ rbp+8
    rbp+8-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp+8
    rbp+8-diff-2 = subst (_≢ orig-rbp+8) (sym second-slot-eq) (<⇒≢ rsp-8<rbp+8)

-- | Combined rbp and rbp+8 disjointness for curry (2-slot allocation)
-- Encapsulates all arithmetic needed for curry's frame preservation proofs
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
-- After rsp decreases by 16, the frame bound (sp-addr frame ≥ old-rsp) still holds
-- for the new rsp (since new-rsp ≤ old-rsp).
curry-stack-inv-frame-bound-update : ∀ (s s' : State) →
  readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 16 →
  (frame : StackPointer) →
  sp-addr frame ≥ readReg (regs s) rsp →
  sp-addr frame ≥ readReg (regs s') rsp
curry-stack-inv-frame-bound-update s s' rsp-eq frame old-bound =
  subst (sp-addr frame ≥_) (sym rsp-eq) (≤-trans (m∸n≤m (readReg (regs s) rsp) 16) old-bound)

-- | RbpInvariant preservation after 2-slot allocation
-- The rbp-frame and rbp-is-base are unchanged (rbp register doesn't change),
-- only the frame-bound needs updating.
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
-- Used for mem-above-final transitivity proofs
curry-alloc-below-rbp : ∀ (s : State) →
  RbpInvariant s →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
      orig-rbp = readReg (regs s) rbp
  in (new-rsp < orig-rbp) × ((new-rsp +ℕ 8) < orig-rbp)
curry-alloc-below-rbp s rbp-inv rsp-sufficient = new-rsp<rbp , new-rsp+8<rbp
  where
    open import Data.Nat.Properties using (<-≤-trans; m∸n≤m; <⇒≤; +-monoʳ-<; m∸n+n≡m; ≤-<-trans)
    open import Data.Nat using (s≤s; z≤n)

    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16
    orig-rbp = readReg (regs s) rbp

    -- Helper: m ∸ n < m when n > 0 and m > n
    m∸n<m' : ∀ m n → n > 0 → m > n → m ∸ n < m
    m∸n<m' (suc m') (suc n') _ (s≤s m'≥n') = s≤s (m∸n≤m m' n')

    -- new-rsp < rsp
    new-rsp<rsp : new-rsp < rsp-val
    new-rsp<rsp = m∸n<m' rsp-val 16 (s≤s z≤n) rsp-sufficient

    -- new-rsp < rbp (via frame-bound)
    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = subst (new-rsp <_) (sym (rbp-is-base rbp-inv))
                        (<-≤-trans new-rsp<rsp (frame-bound rbp-inv))

    -- For (new-rsp + 8) < rbp
    16≤rsp : 16 ≤ rsp-val
    16≤rsp = <⇒≤ rsp-sufficient

    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient

    rsp-8<rsp : rsp-val ∸ 8 < rsp-val
    rsp-8<rsp = m∸n<m' rsp-val 8 (s≤s z≤n) rsp>8

    rsp-8<rbp : rsp-val ∸ 8 < orig-rbp
    rsp-8<rbp = subst (rsp-val ∸ 8 <_) (sym (rbp-is-base rbp-inv))
                      (<-≤-trans rsp-8<rsp (frame-bound rbp-inv))

    -- new-rsp + 8 = rsp - 8
    second-slot-eq : new-rsp +ℕ 8 ≡ rsp-val ∸ 8
    second-slot-eq = trans (cong (_+ℕ 8) step1) (m∸n+n≡m word-fits)
      where
        open import Data.Nat.Properties using (∸-+-assoc; ∸-monoˡ-≤; n≤1+n)
        step1 : rsp-val ∸ 16 ≡ (rsp-val ∸ 8) ∸ 8
        step1 = sym (∸-+-assoc rsp-val 8 8)
        two-slots-fit : 16 ≤ rsp-val
        two-slots-fit = ≤-trans (n≤1+n 16) rsp-sufficient
        word-fits : 8 ≤ rsp-val ∸ 8
        word-fits = ∸-monoˡ-≤ 8 two-slots-fit

    new-rsp+8<rbp : (new-rsp +ℕ 8) < orig-rbp
    new-rsp+8<rbp = subst (_< orig-rbp) (sym second-slot-eq) rsp-8<rbp

-- | Prove curry allocation addresses are non-zero (for mem-at-0 preservation)
-- When rsp > 16, the allocation addresses (rsp-16) and (rsp-8) are both > 0
curry-alloc-nonzero : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let new-rsp = readReg (regs s) rsp ∸ 16
  in (new-rsp ≢ 0) × ((new-rsp +ℕ 8) ≢ 0)
curry-alloc-nonzero s rsp-sufficient = diff-new-rsp , diff-new-rsp+8
  where
    open import Data.Nat.Properties using (<⇒≢; ∸-monoˡ-≤; <-trans; +-monoˡ-<)
    open import Data.Nat using (s≤s; z≤n)

    rsp-val = readReg (regs s) rsp
    new-rsp = rsp-val ∸ 16

    -- rsp > 16 means rsp ≥ 17, so rsp ∸ 16 ≥ 1 > 0
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

-- | Helper: (m - 8) < m when m > 8
-- Used repeatedly in Apply.agda for 1-slot allocation proofs
private
  m∸8<m : ∀ m → m > 8 → m ∸ 8 < m
  m∸8<m (suc m') (s≤s _) = s≤s (m∸n≤m m' 7)

-- | Prove 1-slot allocation address is below original rsp
-- When rsp > 16, we have rsp > 8, so (rsp - 8) < rsp
apply-alloc-below-rsp : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s) rsp ∸ 8 < readReg (regs s) rsp
apply-alloc-below-rsp s rsp-sufficient = m∸8<m rsp-val rsp>8
  where
    rsp-val = readReg (regs s) rsp
    rsp>8 : rsp-val > 8
    rsp>8 = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) rsp-sufficient

-- | Prove 1-slot allocation address is different from addresses >= rsp
-- When addr >= rsp > rsp - 8, we have (rsp - 8) ≢ addr
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
-- The original and allocated addresses are different
apply-rsp-diff-from-alloc : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  readReg (regs s) rsp ≢ readReg (regs s) rsp ∸ 8
apply-rsp-diff-from-alloc s rsp-sufficient eq =
  <⇒≢ (apply-alloc-below-rsp s rsp-sufficient) (sym eq)
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Prove 2-slot allocation ((rsp - 8) - 8) is below original rsp
-- Used in apply when both push and call happen
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
--
-- ThunkExec allocates 4 slots: push r15, push rbp, sub rsp 16
-- These helpers encapsulate the arithmetic for 2-slot and 4-slot relations.
------------------------------------------------------------------------

-- | Helper: 2-slot is below 1-slot when rsp > 16
-- Proves: (rsp ∸ 16) < (rsp ∸ 8)
-- Uses ∸-monoʳ-< : o < n → n ≤ m → m ∸ n < m ∸ o
-- With o = 8, n = 16, m = rsp: 8 < 16 → 16 ≤ rsp → rsp ∸ 16 < rsp ∸ 8
thunk-2slot-below-1slot : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 16) < (rsp-val ∸ 8)
thunk-2slot-below-1slot s rsp-sufficient = ∸-monoʳ-< 8<16 16≤rsp
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    open import Data.Nat using (s≤s; z≤n)
    rsp-val = readReg (regs s) rsp
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    16≤rsp : 16 ≤ rsp-val
    16≤rsp = <⇒≤ rsp-sufficient

-- | Helper: 2-slot is below orig-rsp when rsp > 16
-- Proves: (rsp ∸ 16) < rsp
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
-- Proves: (rsp ∸ 16) ≢ rsp
thunk-2slot-diff-from-orig : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 16) ≢ rsp-val
thunk-2slot-diff-from-orig s rsp-sufficient eq =
  <⇒≢ (thunk-2slot-below-orig s rsp-sufficient) eq
  where
    open import Data.Nat.Properties using (<⇒≢)

-- | Helper: 4-slot is below orig-rsp when rsp > 16
-- Proves: (rsp ∸ 32) < rsp
-- ThunkExec: new-rsp = ((rsp ∸ 8) ∸ 8) ∸ 16 = rsp ∸ 32
thunk-4slot-below-orig : ∀ (s : State) →
  readReg (regs s) rsp > 16 →
  let rsp-val = readReg (regs s) rsp
  in (rsp-val ∸ 32) < rsp-val
thunk-4slot-below-orig s rsp-sufficient = ≤-<-trans rsp∸32≤rsp∸8 rsp∸8<rsp
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    open import Data.Nat using (s≤s; z≤n)
    rsp-val = readReg (regs s) rsp
    rsp∸8<rsp = apply-alloc-below-rsp s rsp-sufficient
    -- ∸-monoʳ-≤ : m → x ≤ y → m ∸ y ≤ m ∸ x (subtracting more gives less)
    -- With m = rsp, x = 8, y = 32: 8 ≤ 32 → rsp ∸ 32 ≤ rsp ∸ 8
    8≤32 : 8 ≤ 32
    8≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    rsp∸32≤rsp∸8 : (rsp-val ∸ 32) ≤ (rsp-val ∸ 8)
    rsp∸32≤rsp∸8 = ∸-monoʳ-≤ rsp-val 8≤32

-- | Helper: 4-slot is different from addresses >= orig-rsp
-- Proves: (rsp ∸ 32) ≢ addr when addr ≥ rsp
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
--
-- These take a raw ℕ value instead of State, making them usable
-- when the rsp value is in a local binding (like in ThunkExec.agda).
------------------------------------------------------------------------

-- | Raw ℕ version: 1-slot below orig when n > 16
-- Proves: (n ∸ 8) < n
n∸8<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 8) < n
n∸8<n-raw n n>16 = m∸8<m n (≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) n>16)

-- | Raw ℕ version: 2-slot below 1-slot when n > 16
-- Proves: (n ∸ 16) < (n ∸ 8)
n∸16<n∸8-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 16) < (n ∸ 8)
n∸16<n∸8-raw n n>16 = ∸-monoʳ-< 8<16 16≤n
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    open import Data.Nat using (s≤s; z≤n)
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    16≤n : 16 ≤ n
    16≤n = <⇒≤ n>16

-- | Raw ℕ version: 2-slot below orig when n > 16
-- Proves: (n ∸ 16) < n
n∸16<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 16) < n
n∸16<n-raw n n>16 = <-trans (n∸16<n∸8-raw n n>16) (n∸8<n-raw n n>16)
  where
    open import Data.Nat.Properties using (<-trans)

-- | Raw ℕ version: 4-slot below orig when n > 16
-- Proves: (n ∸ 32) < n
n∸32<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 32) < n
n∸32<n-raw n n>16 = ≤-<-trans n∸32≤n∸8 n∸8<n
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    open import Data.Nat using (s≤s; z≤n)
    n∸8<n = n∸8<n-raw n n>16
    -- ∸-monoʳ-≤ : m → x ≤ y → m ∸ y ≤ m ∸ x (subtracting more gives less)
    8≤32 : 8 ≤ 32
    8≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    n∸32≤n∸8 : (n ∸ 32) ≤ (n ∸ 8)
    n∸32≤n∸8 = ∸-monoʳ-≤ n 8≤32

-- | Raw ℕ version: 3-slot below orig when n > 16
-- Proves: (n ∸ 24) < n
n∸24<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 24) < n
n∸24<n-raw n n>16 = ≤-<-trans n∸24≤n∸8 n∸8<n
  where
    open import Data.Nat.Properties using (≤-<-trans; ∸-monoʳ-≤)
    open import Data.Nat using (s≤s; z≤n)
    n∸8<n = n∸8<n-raw n n>16
    8≤24 : 8 ≤ 24
    8≤24 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
    n∸24≤n∸8 : (n ∸ 24) ≤ (n ∸ 8)
    n∸24≤n∸8 = ∸-monoʳ-≤ n 8≤24

-- | Raw ℕ version: 3-slot below < 1-slot below when n > 24
-- Proves: (n ∸ 24) < (n ∸ 8)
-- Used for new-rsp+8 < rsp-after-push-r15 in thunk
n∸24<n∸8-raw : ∀ (n : ℕ) → n > 24 → (n ∸ 24) < (n ∸ 8)
n∸24<n∸8-raw n n>24 = ∸-monoʳ-< 8<24 24≤n
  where
    open import Data.Nat.Properties using (∸-monoʳ-<; <⇒≤)
    open import Data.Nat using (s≤s; z≤n)
    8<24 : 8 < 24
    8<24 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    24≤n : 24 ≤ n
    24≤n = <⇒≤ n>24

-- | Identity: (n ∸ 32) + 8 ≡ n ∸ 24 when n ≥ 32
-- Used for connecting new-rsp+8 to old-rsp∸24
n∸32+8≡n∸24 : ∀ (n : ℕ) → 32 ≤ n → (n ∸ 32) +ℕ 8 ≡ n ∸ 24
n∸32+8≡n∸24 n 32≤n = trans step1 step2
  where
    open import Data.Nat.Properties using (m+n∸n≡m; m∸n+n≡m)
    -- (n ∸ 32) + 8 = ((n ∸ 32) + 8 + 24) ∸ 24
    step1 : (n ∸ 32) +ℕ 8 ≡ ((n ∸ 32) +ℕ 8 +ℕ 24) ∸ 24
    step1 = sym (m+n∸n≡m ((n ∸ 32) +ℕ 8) 24)
    -- (n ∸ 32) + 8 + 24 = (n ∸ 32) + 32 = n
    8+24≡32 : 8 +ℕ 24 ≡ 32
    8+24≡32 = refl
    lhs+24≡n : (n ∸ 32) +ℕ 8 +ℕ 24 ≡ n
    lhs+24≡n = trans (+-assoc (n ∸ 32) 8 24) (trans (cong ((n ∸ 32) +ℕ_) 8+24≡32) (m∸n+n≡m 32≤n))
    -- Therefore ((n ∸ 32) + 8 + 24) ∸ 24 = n ∸ 24
    step2 : ((n ∸ 32) +ℕ 8 +ℕ 24) ∸ 24 ≡ n ∸ 24
    step2 = cong (_∸ 24) lhs+24≡n

-- | Raw ℕ version: 4-slot below orig + 8 < orig when n > 16
-- Proves: (n ∸ 32) + 8 < n
-- Used for new-rsp+8 < old-rsp in thunk (eliminates with pattern)
n∸32+8<n-raw : ∀ (n : ℕ) → n > 16 → (n ∸ 32) +ℕ 8 < n
n∸32+8<n-raw n n>16 = <-≤-trans step8<step16 step16≤n
  where
    open import Data.Nat.Properties using (<-≤-trans; +-monoˡ-≤; +-monoʳ-<; ∸-monoʳ-≤; m∸n+n≡m; <⇒≤)
    open import Data.Nat using (s≤s; z≤n)
    -- (n ∸ 32) + 8 < (n ∸ 32) + 16
    8<16 : 8 < 16
    8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
    step8<step16 : (n ∸ 32) +ℕ 8 < (n ∸ 32) +ℕ 16
    step8<step16 = +-monoʳ-< (n ∸ 32) 8<16
    -- (n ∸ 32) + 16 ≤ (n ∸ 16) + 16 = n
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
