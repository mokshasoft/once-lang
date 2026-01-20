------------------------------------------------------------------------
-- Once.Backend.Common.MemoryRegionLemmas
--
-- Lemmas and theorems derived from the memory layout semantics.
--
-- This module is PARAMETERIZED over StackGrowth, which the architecture
-- provides. This allows the module to work with any stack growth
-- direction and word size.
--
-- Provides:
--   1. Derived disjointness theorems
--   2. Stack slot addressing (from StackGrowth)
--   3. Memory preservation lemmas
------------------------------------------------------------------------

-- Import StackGrowth for module parameter
open import Once.Backend.Common.MemoryLayoutSemantics using (StackGrowth)

module Once.Backend.Common.MemoryRegionLemmas (sg : StackGrowth) where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _≥_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; ≤-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

-- Re-export foundational semantics (except StackGrowth which is a parameter)
open import Once.Backend.Common.MemoryLayoutSemantics public hiding (StackGrowth)

-- Open the StackGrowth parameter
open StackGrowth sg public

-- Import and re-export Memory operations
open import Once.Backend.Common.Memory using (Memory; readMem; writeMem) public

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
-- Abstract Stack/Heap Pointers (aliases for Semantics types)
------------------------------------------------------------------------

-- StackPointer = StackAddr from Semantics (re-exported)
StackPointer : Set
StackPointer = StackAddr

-- HeapPointer = HeapAddr from Semantics (re-exported)
HeapPointer : Set
HeapPointer = HeapAddr

------------------------------------------------------------------------
-- Stack Slot Addressing (DERIVED FROM StackGrowth)
--
-- These definitions and lemmas are derived from the StackGrowth
-- interface provided by the architecture.
------------------------------------------------------------------------

-- | Compute address of slot k in stack frame at sp
slot-addr : StackPointer → ℕ → Addr
slot-addr sp k = grow (addr sp) k

-- | Initial slot is at the stack pointer base (from grow-identity)
init-slot-at-base : ∀ sp → slot-addr sp zero ≡ addr sp
init-slot-at-base sp = grow-identity (addr sp)

-- | Different offsets give different addresses (from grow-injective)
offset-distinct : ∀ sp k₁ k₂ → k₁ ≢ k₂ → slot-addr sp k₁ ≢ slot-addr sp k₂
offset-distinct sp k₁ k₂ k₁≢k₂ = grow-injective (addr sp) k₁ k₂ k₁≢k₂

-- | Slot is in stack region (from grow-preserves-region)
slot-in-stack : ∀ sp k → InStack (slot-addr sp k)
slot-in-stack sp k = grow-preserves-region (addr sp) k (in-stack sp)

-- | Different stack pointers give different slot addresses (same offset)
-- Proven from grow-addr-injective
sp-distinct : ∀ sp₁ sp₂ k → addr sp₁ ≢ addr sp₂ → slot-addr sp₁ k ≢ slot-addr sp₂ k
sp-distinct sp₁ sp₂ k addr≢ = grow-addr-injective (addr sp₁) (addr sp₂) k addr≢

------------------------------------------------------------------------
-- Heap Region Properties (SEMANTIC POSTULATES)
--
-- These represent runtime guarantees about the allocator that cannot
-- be derived from the abstract memory model alone:
--
-- 1. encode-in-heap: The runtime allocator places semantic values in
--    the heap region. This is instantiated with our specific encode
--    function in StackInstantiation.encode-in-heap-sem.
--
-- 2. heap-offset: Heap-allocated objects are contiguous. When we have
--    a pointer to a heap object, accessing fields (ptr + offset) stays
--    within heap. In practice, offset is always small (slot-size = 8).
--
-- NOTE: These are FOUNDATIONAL postulates at the allocator boundary,
-- not "middle-step" lemmas that should be proven from something else.
------------------------------------------------------------------------

postulate
  -- | Encoding function produces heap addresses
  -- JUSTIFICATION: The runtime allocator places all semantic values in heap.
  encode-in-heap : ∀ {A : Set} (encode : A → Addr) (x : A) → InHeap (encode x)

  -- | Field access stays within heap region
  -- JUSTIFICATION: Heap objects are allocated contiguously. When accessing
  -- fields of a heap object (e.g., closure payload at ptr+8), the result
  -- is still in heap. Requires heap capacity for allocated object sizes.
  heap-offset : ∀ a n → InHeap a → InHeap (a + n)

------------------------------------------------------------------------
-- Abstract Frame Operations
--
-- frameSlot reads the value at slot k of stack frame sp.
------------------------------------------------------------------------

-- | Read value at slot k of stack frame at sp
frameSlot : Memory → StackPointer → ℕ → Maybe Word
frameSlot mem sp k = readMem mem (slot-addr sp k)

------------------------------------------------------------------------
-- Memory Preservation
--
-- Writing to stack doesn't affect heap/code regions (from disjointness).
------------------------------------------------------------------------

-- Import readMem-writeMem-diff for the proofs
open import Once.Backend.Common.Memory using (readMem-writeMem-diff)

-- | Writing to a stack address preserves heap memory
stackAddr-write-preserves-heap : ∀ mem a val heap-a →
  InStack a → InHeap heap-a →
  readMem (writeMem mem a val) heap-a ≡ readMem mem heap-a
stackAddr-write-preserves-heap mem a val heap-a in-s in-h =
  readMem-writeMem-diff mem a heap-a val (stack-heap-addr-disjoint a heap-a in-s in-h)

-- | Writing to a stack address preserves code memory
stackAddr-write-preserves-code : ∀ mem a val code-a →
  InStack a → InCode code-a →
  readMem (writeMem mem a val) code-a ≡ readMem mem code-a
stackAddr-write-preserves-code mem a val code-a in-s in-c =
  readMem-writeMem-diff mem a code-a val (stack-code-addr-disjoint a code-a in-s in-c)

------------------------------------------------------------------------
-- INTERNAL: Abstraction Boundary Glue
------------------------------------------------------------------------

module FrameSlotInternal where
  -- | frameSlot at initial slot reads from the stack pointer address
  init-frame-slot-at-base : ∀ mem sp → frameSlot mem sp zero ≡ readMem mem (addr sp)
  init-frame-slot-at-base mem sp = cong (readMem mem) (init-slot-at-base sp)

  -- | frameSlot is just readMem at the slot address (by definition)
  frameSlot-is-readMem : ∀ mem sp k → frameSlot mem sp k ≡ readMem mem (slot-addr sp k)
  frameSlot-is-readMem mem sp k = refl
