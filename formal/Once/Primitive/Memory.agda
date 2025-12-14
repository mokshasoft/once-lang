------------------------------------------------------------------------
-- Once.Primitive.Memory
--
-- Axiomatic specification of memory allocation primitives.
--
-- This module provides an abstract model of heap memory, independent
-- of any particular implementation (C, x86-64, ARM64, etc.).
--
-- The axioms capture the essential properties that any correct
-- implementation must satisfy, without specifying implementation details.
--
-- KEY INSIGHT: Memory allocation is orthogonal to the type system.
-- These axioms don't affect type checking or IR semantics - they only
-- constrain how effectful primitives behave at runtime.
--
------------------------------------------------------------------------

module Once.Primitive.Memory where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _>_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

------------------------------------------------------------------------
-- Abstract Types
--
-- These types are abstract - we don't specify their representation.
-- Any implementation that satisfies the axioms is correct.
------------------------------------------------------------------------

-- | Abstract pointer type
--
-- Pointers are opaque values that can be compared for equality.
-- We don't expose their numeric representation.
postulate
  Ptr : Set

-- | Pointer equality is decidable
postulate
  _≟Ptr_ : (p q : Ptr) → Dec (p ≡ q)

-- | Null pointer constant
postulate
  nullPtr : Ptr

-- | Abstract heap type
--
-- A heap maps pointers to allocated regions.
-- We model it abstractly without exposing internal structure.
postulate
  Heap : Set

-- | Empty heap (initial state)
postulate
  emptyHeap : Heap

------------------------------------------------------------------------
-- Heap Membership
--
-- We track which pointers are "live" (allocated but not freed).
------------------------------------------------------------------------

-- | Pointer is live in heap
postulate
  _∈_ : Ptr → Heap → Set

-- | Pointer is not in heap (derived)
_∉_ : Ptr → Heap → Set
p ∉ h = ¬ (p ∈ h)

-- | Membership is decidable
postulate
  _∈?_ : (p : Ptr) (h : Heap) → Dec (p ∈ h)

-- | Null pointer is never live
postulate
  null-not-live : ∀ h → nullPtr ∉ h

-- | Empty heap has no live pointers
postulate
  empty-no-live : ∀ p → p ∉ emptyHeap

------------------------------------------------------------------------
-- Allocation
--
-- alloc n h = (ptr, h')
--   Allocate n bytes, returning a fresh pointer and updated heap.
------------------------------------------------------------------------

postulate
  alloc : ℕ → Heap → Ptr × Heap

-- | Freshness: allocated pointer was not in the original heap
postulate
  alloc-fresh : ∀ n h →
    let (p , h') = alloc n h
    in p ∉ h

-- | Non-null: allocated pointer is never null (for n > 0)
postulate
  alloc-non-null : ∀ n h →
    n > 0 →
    let (p , _) = alloc n h
    in p ≢ nullPtr

-- | Presence: allocated pointer is live in new heap
postulate
  alloc-live : ∀ n h →
    let (p , h') = alloc n h
    in p ∈ h'

-- | Preservation: existing live pointers remain live
postulate
  alloc-preserves : ∀ n h p →
    p ∈ h →
    let (_ , h') = alloc n h
    in p ∈ h'

-- | Determinism: same inputs produce same outputs
-- (for reasoning in a pure context)
postulate
  alloc-deterministic : ∀ n h →
    alloc n h ≡ alloc n h

------------------------------------------------------------------------
-- Deallocation
--
-- free p h = h'
--   Free the memory at pointer p, returning updated heap.
------------------------------------------------------------------------

postulate
  free : Ptr → Heap → Heap

-- | Removal: freed pointer is no longer live
postulate
  free-removes : ∀ p h →
    p ∉ free p h

-- | Preservation: other pointers remain unaffected
postulate
  free-preserves : ∀ p q h →
    p ≢ q →
    q ∈ h →
    q ∈ free p h

-- | Idempotence: freeing non-live pointer is identity
postulate
  free-idempotent : ∀ p h →
    p ∉ h →
    free p h ≡ h

------------------------------------------------------------------------
-- Buffer Contents (Optional - for reasoning about data)
--
-- These axioms model reading/writing buffer contents.
-- They're more detailed and may be added incrementally.
------------------------------------------------------------------------

-- | Buffer size tracking
postulate
  sizeOf : Ptr → Heap → Maybe ℕ

-- | Allocated buffers have known size
postulate
  alloc-has-size : ∀ n h →
    let (p , h') = alloc n h
    in sizeOf p h' ≡ just n

-- | Non-live pointers have no size
postulate
  dead-no-size : ∀ p h →
    p ∉ h →
    sizeOf p h ≡ nothing

------------------------------------------------------------------------
-- Derived Properties
------------------------------------------------------------------------

-- | Allocation returns distinct pointers on successive calls
-- (This follows from freshness + preservation)
alloc-distinct : ∀ n₁ n₂ h →
  let (p₁ , h₁) = alloc n₁ h
      (p₂ , h₂) = alloc n₂ h₁
  in p₁ ≢ p₂
alloc-distinct n₁ n₂ h p₁≡p₂ =
  let (p₁ , h₁) = alloc n₁ h
      (p₂ , h₂) = alloc n₂ h₁
      p₁-live : p₁ ∈ h₁
      p₁-live = alloc-live n₁ h
      p₂-fresh : p₂ ∉ h₁
      p₂-fresh = alloc-fresh n₂ h₁
  in p₂-fresh (Relation.Binary.PropositionalEquality.subst (λ x → x ∈ h₁) p₁≡p₂ p₁-live)

------------------------------------------------------------------------
-- Reallocation (combines alloc + copy + free)
------------------------------------------------------------------------

postulate
  realloc : Ptr → ℕ → Heap → Ptr × Heap

-- | Realloc of null is equivalent to alloc
postulate
  realloc-null : ∀ n h →
    realloc nullPtr n h ≡ alloc n h

-- | Realloc returns live pointer
postulate
  realloc-live : ∀ p n h →
    p ∈ h →
    let (p' , h') = realloc p n h
    in p' ∈ h'

-- | Realloc frees old pointer (if different)
postulate
  realloc-frees-old : ∀ p n h →
    p ∈ h →
    let (p' , h') = realloc p n h
    in p ≢ p' → p ∉ h'

------------------------------------------------------------------------
-- Summary of Trusted Axioms
------------------------------------------------------------------------

-- This module introduces the following postulates:
--
-- Types:
--   Ptr, Heap, emptyHeap, nullPtr
--
-- Membership:
--   _∈_, _∈?_, null-not-live, empty-no-live
--
-- Allocation:
--   alloc, alloc-fresh, alloc-non-null, alloc-live,
--   alloc-preserves, alloc-deterministic
--
-- Deallocation:
--   free, free-removes, free-preserves, free-idempotent
--
-- Buffer info:
--   sizeOf, alloc-has-size, dead-no-size
--
-- Reallocation:
--   realloc, realloc-null, realloc-live, realloc-frees-old
--
-- These axioms are validated by the C, x86-64, ARM64, and RISC-V64
-- implementations in Strata/Interpretations/Linux/memory.*.
--

