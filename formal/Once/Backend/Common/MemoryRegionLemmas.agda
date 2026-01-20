------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegionLemmas
--
-- Lemmas and theorems derived from the memory layout semantics.
--
-- This module re-exports MemoryLayoutSemantics and provides:
--   1. Derived disjointness theorems
--   2. Stack/heap/code region properties
--   3. Memory preservation lemmas
--
-- TODO: Some items here are still postulates that should be
-- converted to definitions or proven from capacity.
------------------------------------------------------------------------

module Once.Backend.Common.MemoryRegionLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; ≤-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- Re-export foundational semantics
open import Once.Backend.Common.MemoryLayoutSemantics public

-- Import Memory operations
open import Once.Backend.Common.Memory using (Memory; readMem; writeMem)

------------------------------------------------------------------------
-- Derived Disjointness THEOREMS
------------------------------------------------------------------------

stack-heap-disjoint : ∀ a → InStack a → InHeap a → ⊥
stack-heap-disjoint a in-s in-h = proj₁ (intervals-disjoint a) (in-s , in-h)

stack-code-disjoint : ∀ a → InStack a → InCode a → ⊥
stack-code-disjoint a in-s in-c = proj₁ (proj₂ (intervals-disjoint a)) (in-s , in-c)

-- | Two addresses in different regions are distinct
stack-heap-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InHeap a₂ → a₁ ≢ a₂
stack-heap-addr-disjoint a₁ a₂ in-s in-h a₁≡a₂ =
  stack-heap-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-h

stack-code-addr-disjoint : ∀ a₁ a₂ → InStack a₁ → InCode a₂ → a₁ ≢ a₂
stack-code-addr-disjoint a₁ a₂ in-s in-c a₁≡a₂ =
  stack-code-disjoint a₂ (subst InStack a₁≡a₂ in-s) in-c

------------------------------------------------------------------------
-- Stack Subtraction
--
-- TODO: Convert to proof from capacity
------------------------------------------------------------------------

postulate
  stack-sub-preserves : ∀ a k →
    InStack a →
    k ≤ a →
    InStack (a ∸ k)

------------------------------------------------------------------------
-- Abstract Stack/Heap Pointers (aliases for Semantics types)
------------------------------------------------------------------------

-- StackPointer = StackAddr from Semantics (re-exported)
StackPointer : Set
StackPointer = StackAddr

-- HeapPointer = HeapAddr from Semantics (re-exported)
HeapPointer : Set
HeapPointer = HeapAddr

------------------------------------------------------------------------
-- Stack Slot Addressing
--
-- TODO: Convert slot-addr to definition (slot-addr sp k = addr sp + k * 8)
-- Then most of these become trivially provable.
------------------------------------------------------------------------

postulate
  slot-addr : StackPointer → ℕ → Addr
  slot-in-stack : ∀ sp k → InStack (slot-addr sp k)
  slot-addr-0-is-base : ∀ sp → slot-addr sp 0 ≡ addr sp
  slot-addr-1-is-base+8 : ∀ sp → slot-addr sp 1 ≡ addr sp + 8
  sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
  offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
  frames-disjoint-slots : ∀ sp₁ sp₂ k₁ k₂ → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k₁ ≢ slot-addr sp₂ k₂
  slot-addr-≥-base : ∀ sp k → slot-addr sp k ≥ addr sp
  slot-addr-above-thunk-rbp : ∀ sp k rsp thunk-rbp →
    addr sp ≡ rsp + 8 → thunk-rbp ≡ rsp ∸ 16 → rsp > 16 → slot-addr sp k > thunk-rbp

------------------------------------------------------------------------
-- Heap Region Properties
--
-- TODO: Determine if these can be proven or must remain postulates
------------------------------------------------------------------------

postulate
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)

------------------------------------------------------------------------
-- Code Region Properties
--
-- TODO: Determine if this can be proven from code-bounds
------------------------------------------------------------------------

postulate
  pc-in-code : ∀ (pc : Addr) (prog-len : ℕ) → pc < prog-len → InCode pc

------------------------------------------------------------------------
-- Abstract Frame Operations
--
-- TODO: Convert frameSlot to definition
------------------------------------------------------------------------

postulate
  frameSlot : Memory → StackPointer → ℕ → Maybe Word

------------------------------------------------------------------------
-- Memory Preservation
--
-- TODO: Prove from disjointness + writeMem semantics
------------------------------------------------------------------------

postulate
  stackAddr-write-preserves-heap : ∀ mem addr val heap-addr →
    InStack addr → InHeap heap-addr →
    readMem (writeMem mem addr val) heap-addr ≡ readMem mem heap-addr

  stackAddr-write-preserves-code : ∀ mem addr val code-addr →
    InStack addr → InCode code-addr →
    readMem (writeMem mem addr val) code-addr ≡ readMem mem code-addr

------------------------------------------------------------------------
-- INTERNAL: Abstraction Boundary Glue
------------------------------------------------------------------------

module FrameSlotInternal where
  postulate
    frameSlot-0-is-top : ∀ mem sp → frameSlot mem sp 0 ≡ readMem mem (addr sp)
    frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
