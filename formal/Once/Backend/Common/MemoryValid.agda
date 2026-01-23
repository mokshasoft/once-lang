------------------------------------------------------------------------
-- Once.Backend.Common.MemoryValid
--
-- Common memory validity predicates shared by all backend architectures.
--
-- This module provides:
-- - AtS records: PairAtS, InlAtS, InrAtS, ClosureAtS
-- - Allocation lemmas: alloc-*-creates-valid-s
-- - NoOverlap record
-- - AtS preservation under memory equality
--
-- Each architecture imports this module for the core infrastructure
-- and adds architecture-specific extensions (e.g., ValidAt for x86).
--
-- Usage:
--   open import Once.Backend.Common.MemoryValid public
------------------------------------------------------------------------

module Once.Backend.Common.MemoryValid where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

-- Re-export common memory types and lemmas
open import Once.Memory public
  using (Word; Memory; readMem; writeMem; word-size;
         mem-read-write; mem-read-other; n≢n+word-size)

------------------------------------------------------------------------
-- Slot Size
--
-- All 64-bit backends use 8-byte slots for allocation.
-- This equals word-size from Once.Memory.
------------------------------------------------------------------------

slot-size : ℕ
slot-size = word-size  -- 8

------------------------------------------------------------------------
-- Stateful Validity Predicates (AtS Records)
--
-- These predicates use explicit addresses instead of the abstract
-- `encode` function. This breaks the circular dependency on postulates
-- and allows validity to be proven from stateful allocation theorems.
------------------------------------------------------------------------

-- | Pair validity with explicit component addresses
-- Memory at addr-pair contains [addr-a, addr-b]
record PairAtS (addr-a addr-b addr-pair : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr-pair ≡ just addr-a
    snd-valid : readMem m (addr-pair +ℕ slot-size) ≡ just addr-b

open PairAtS public using () renaming (fst-valid to fst-valid-s; snd-valid to snd-valid-s)

-- | Left sum validity with explicit value address
-- Memory at addr-sum contains [0, addr-val]
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

open InlAtS public using () renaming (tag-valid to tag-valid-inl-s; val-valid to val-valid-inl-s)

-- | Right sum validity with explicit value address
-- Memory at addr-sum contains [1, addr-val]
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ slot-size) ≡ just addr-val

open InrAtS public using () renaming (tag-valid to tag-valid-inr-s; val-valid to val-valid-inr-s)

-- | Closure validity with explicit addresses
-- Memory at addr-closure contains [env-addr, code-ptr]
record ClosureAtS (env-addr code-ptr addr-closure : Word) (m : Memory) : Set where
  constructor closure-at-s
  field
    env-valid : readMem m addr-closure ≡ just env-addr
    code-valid : readMem m (addr-closure +ℕ slot-size) ≡ just code-ptr

open ClosureAtS public using () renaming (env-valid to env-valid-s; code-valid to code-valid-s)

------------------------------------------------------------------------
-- Stateful Allocation Proofs
--
-- These lemmas prove that writing two words creates a valid AtS record.
------------------------------------------------------------------------

-- | Create PairAtS from two writes
alloc-pair-creates-valid-s : ∀ (addr-a addr-b addr-pair : Word) (m : Memory) →
  let m₁ = writeMem m addr-pair addr-a
      m₂ = writeMem m₁ (addr-pair +ℕ slot-size) addr-b
  in PairAtS addr-a addr-b addr-pair m₂
alloc-pair-creates-valid-s addr-a addr-b addr-pair m = pair-at-s fst-proof snd-proof
  where
    m₁ = writeMem m addr-pair addr-a
    m₂ = writeMem m₁ (addr-pair +ℕ slot-size) addr-b

    fst-proof : readMem m₂ addr-pair ≡ just addr-a
    fst-proof = trans
      (mem-read-other {m₁} {addr-pair +ℕ slot-size} {addr-pair} {addr-b} (λ eq → n≢n+word-size addr-pair (sym eq)))
      (mem-read-write {m} {addr-pair} {addr-a})

    snd-proof : readMem m₂ (addr-pair +ℕ slot-size) ≡ just addr-b
    snd-proof = mem-read-write {m₁} {addr-pair +ℕ slot-size} {addr-b}

-- | Create InlAtS from two writes
alloc-inl-creates-valid-s : ∀ (addr-val addr-sum : Word) (m : Memory) →
  let m₁ = writeMem m addr-sum 0
      m₂ = writeMem m₁ (addr-sum +ℕ slot-size) addr-val
  in InlAtS addr-val addr-sum m₂
alloc-inl-creates-valid-s addr-val addr-sum m = inl-at-s tag-proof val-proof
  where
    m₁ = writeMem m addr-sum 0
    m₂ = writeMem m₁ (addr-sum +ℕ slot-size) addr-val

    tag-proof : readMem m₂ addr-sum ≡ just 0
    tag-proof = trans
      (mem-read-other {m₁} {addr-sum +ℕ slot-size} {addr-sum} {addr-val} (λ eq → n≢n+word-size addr-sum (sym eq)))
      (mem-read-write {m} {addr-sum} {0})

    val-proof : readMem m₂ (addr-sum +ℕ slot-size) ≡ just addr-val
    val-proof = mem-read-write {m₁} {addr-sum +ℕ slot-size} {addr-val}

-- | Create InrAtS from two writes
alloc-inr-creates-valid-s : ∀ (addr-val addr-sum : Word) (m : Memory) →
  let m₁ = writeMem m addr-sum 1
      m₂ = writeMem m₁ (addr-sum +ℕ slot-size) addr-val
  in InrAtS addr-val addr-sum m₂
alloc-inr-creates-valid-s addr-val addr-sum m = inr-at-s tag-proof val-proof
  where
    m₁ = writeMem m addr-sum 1
    m₂ = writeMem m₁ (addr-sum +ℕ slot-size) addr-val

    tag-proof : readMem m₂ addr-sum ≡ just 1
    tag-proof = trans
      (mem-read-other {m₁} {addr-sum +ℕ slot-size} {addr-sum} {addr-val} (λ eq → n≢n+word-size addr-sum (sym eq)))
      (mem-read-write {m} {addr-sum} {1})

    val-proof : readMem m₂ (addr-sum +ℕ slot-size) ≡ just addr-val
    val-proof = mem-read-write {m₁} {addr-sum +ℕ slot-size} {addr-val}

-- | Create ClosureAtS from two writes
alloc-closure-creates-valid-s : ∀ (env-addr code-ptr addr-closure : Word) (m : Memory) →
  let m₁ = writeMem m addr-closure env-addr
      m₂ = writeMem m₁ (addr-closure +ℕ slot-size) code-ptr
  in ClosureAtS env-addr code-ptr addr-closure m₂
alloc-closure-creates-valid-s env-addr code-ptr addr-closure m = closure-at-s env-proof code-proof
  where
    m₁ = writeMem m addr-closure env-addr
    m₂ = writeMem m₁ (addr-closure +ℕ slot-size) code-ptr

    env-proof : readMem m₂ addr-closure ≡ just env-addr
    env-proof = trans
      (mem-read-other {m₁} {addr-closure +ℕ slot-size} {addr-closure} {code-ptr} (λ eq → n≢n+word-size addr-closure (sym eq)))
      (mem-read-write {m} {addr-closure} {env-addr})

    code-proof : readMem m₂ (addr-closure +ℕ slot-size) ≡ just code-ptr
    code-proof = mem-read-write {m₁} {addr-closure +ℕ slot-size} {code-ptr}

------------------------------------------------------------------------
-- AtS Preservation under Memory Equality
--
-- If memory reads are equal, AtS structures are preserved.
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under memory equality
PairAtS-preserved-under-mem-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-mem-eq {addr-a} {addr-b} {addr} pairS mem-eq =
  pair-at-s (trans (mem-eq addr) (fst-valid-s pairS))
            (trans (mem-eq (addr +ℕ slot-size)) (snd-valid-s pairS))

-- | Helper: InlAtS preserved under memory equality
InlAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-mem-eq {addr-val} {addr-sum} inlS mem-eq =
  inl-at-s (trans (mem-eq addr-sum) (tag-valid-inl-s inlS))
           (trans (mem-eq (addr-sum +ℕ slot-size)) (val-valid-inl-s inlS))

-- | Helper: InrAtS preserved under memory equality
InrAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-mem-eq {addr-val} {addr-sum} inrS mem-eq =
  inr-at-s (trans (mem-eq addr-sum) (tag-valid-inr-s inrS))
           (trans (mem-eq (addr-sum +ℕ slot-size)) (val-valid-inr-s inrS))

-- | Helper: ClosureAtS preserved under memory equality
ClosureAtS-preserved-under-mem-eq :
  ∀ {env-addr code-ptr addr-closure : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr-closure m2
ClosureAtS-preserved-under-mem-eq {env-addr} {code-ptr} {addr-closure} closS mem-eq =
  closure-at-s (trans (mem-eq addr-closure) (env-valid-s closS))
               (trans (mem-eq (addr-closure +ℕ slot-size)) (code-valid-s closS))

------------------------------------------------------------------------
-- NoOverlap Record
--
-- Asserts that one address doesn't overlap with a two-word structure.
------------------------------------------------------------------------

-- | Helper: addr₁ ≠ addr₂ and addr₁ ≠ addr₂ + slot-size (doesn't overlap)
record NoOverlap (addr₁ addr₂ : Word) : Set where
  constructor no-overlap
  field
    neq-base : addr₁ ≢ addr₂
    neq-snd  : addr₁ ≢ addr₂ +ℕ slot-size

------------------------------------------------------------------------
-- Re-export n≢n+8 for compatibility
--
-- AArch64's MemoryValid uses n≢n+8 instead of n≢n+word-size.
------------------------------------------------------------------------

n≢n+8 : ∀ (n : ℕ) → n ≢ n +ℕ 8
n≢n+8 = n≢n+word-size  -- word-size = 8

