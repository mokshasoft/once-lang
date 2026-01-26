------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IRStarDerived
--
-- Derived lemmas from ir-mem-preserved field of IRStarResult.
--
-- Key insight: ir-mem-preserved proves addresses ≥ entry-rsp are preserved.
-- We derive heap/code preservation from this + region ordering/disjointness.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IRStarDerived where

open import Data.Nat using (ℕ; _≥_; _<_; _≤_; _>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Data.Nat.Properties using (<⇒≤; ≤-trans)
open import Once.Backend.Common.Memory using (Memory; Word; readMem)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; heap-addr-≥-stack-addr;
         stack-heap-addr-disjoint; stack-code-addr-disjoint)
open import Once.Backend.X86.Correct.StackInvariant using (RbpInvariant)

------------------------------------------------------------------------
-- Derive heap preservation from ir-mem-preserved
------------------------------------------------------------------------

-- | Heap addresses are preserved when addresses ≥ entry-rsp are preserved
-- Derivation: InHeap addr ∧ InStack entry-rsp → addr ≥ entry-rsp (by ordering)
derive-heap-preserved :
  ∀ {mem1 mem2 : Memory} {entry-rsp : Word} →
  InStack entry-rsp →
  (∀ addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr) →
  (∀ addr → InHeap addr → readMem mem2 addr ≡ readMem mem1 addr)
derive-heap-preserved entry-in-stack mem-preserved addr addr-in-heap =
  mem-preserved addr (heap-addr-≥-stack-addr addr-in-heap entry-in-stack)

------------------------------------------------------------------------
-- Derive stack preservation for addresses ≥ entry-rsp
------------------------------------------------------------------------

-- | Stack addresses ≥ entry-rsp are preserved (trivial from ir-mem-preserved)
-- This is for CALLER'S stack addresses (≥ entry-rsp), not our frame's writes
derive-stack-above-entry :
  ∀ {mem1 mem2 : Memory} {entry-rsp : Word} →
  (∀ addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr) →
  (∀ addr → InStack addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr)
derive-stack-above-entry mem-preserved addr _ addr≥entry = mem-preserved addr addr≥entry

------------------------------------------------------------------------
-- For valid-subst-region-preserved compatibility
------------------------------------------------------------------------

-- | Create heap-eq and stack-eq functions for valid-subst-region-preserved
-- The stack-eq requires the additional bound proof (addr ≥ entry-rsp)
--
-- Usage: For caller-provided ValidAt values, the Stack addresses are in
-- the caller's frame (≥ entry-rsp), so the bound holds by construction.
derive-region-preservation :
  ∀ {mem1 mem2 : Memory} {entry-rsp : Word} →
  InStack entry-rsp →
  (∀ addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr) →
  (∀ addr → InHeap addr → readMem mem2 addr ≡ readMem mem1 addr) ×
  (∀ addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr)
derive-region-preservation entry-in-stack mem-preserved =
  derive-heap-preserved entry-in-stack mem-preserved , mem-preserved

------------------------------------------------------------------------
-- Derive ir-mem-above from ir-mem-preserved + RbpInvariant
------------------------------------------------------------------------

-- | Memory above rbp is preserved when addresses ≥ entry-rsp are preserved
-- Derivation: addr > rbp ≥ rsp = entry-rsp (by RbpInvariant)
-- Therefore addr > entry-rsp, so addr ≥ entry-rsp
derive-mem-above :
  ∀ {mem1 mem2 : Memory} {entry-rsp rbp : Word} →
  entry-rsp ≤ rbp →  -- From RbpInvariant: rsp ≤ rbp
  (∀ addr → addr ≥ entry-rsp → readMem mem2 addr ≡ readMem mem1 addr) →
  (∀ addr → addr > rbp → readMem mem2 addr ≡ readMem mem1 addr)
derive-mem-above rsp≤rbp mem-preserved addr addr>rbp =
  mem-preserved addr (≤-trans rsp≤rbp (<⇒≤ addr>rbp))

------------------------------------------------------------------------
-- Caller-provided input invariant
------------------------------------------------------------------------

-- INVARIANT: Caller-provided ValidAt values have all Stack addresses
-- in the caller's frame (≥ entry-rsp).
--
-- This invariant holds because:
-- 1. Heap addresses: always ≥ entry-rsp (via heap-addr-≥-stack-addr)
-- 2. Caller's Stack addresses: in caller's frame which is ≥ entry-rsp
--
-- The existing caller-stack-preserved-* postulates express this invariant.
-- They state: for caller-provided inputs, InStack addresses are preserved.
-- This is TRUE because such addresses are ≥ entry-rsp.
--
-- Future work: Track this invariant type-theoretically in ValidAt.
-- For now, the postulates correctly capture the semantic invariant.
