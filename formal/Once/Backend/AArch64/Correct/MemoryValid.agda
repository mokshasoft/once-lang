{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.MemoryValid
--
-- Memory validity predicates for AArch64 execution.
-- Tracks which values are properly encoded in memory.
--
-- Key insight: The encoding axioms in Postulates.agda claim to hold
-- for ANY memory m. This is too strong. They should only hold for
-- memory where values were properly allocated.
--
-- MemoryValid captures the invariant that values in memory are
-- properly encoded at their expected addresses.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.MemoryValid where

open import Once.Type
open import Once.Semantics using (⟦_⟧; encode)
open import Once.Backend.AArch64.Semantics using (State; Memory; Word; readMem; writeMem)

-- Import proven memory theorems from Once.Memory
open import Once.Memory public
  using (mem-read-write; mem-read-other; n≢n+8)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

------------------------------------------------------------------------
-- ValueAt: A value is properly encoded at an address in memory
------------------------------------------------------------------------

-- | A pair value (a, b) is encoded at address addr in memory m
-- This means: m[addr] = encode a, m[addr+8] = encode b
record PairAt {A B : Type} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) : Set where
  constructor pair-at
  field
    fst-valid : readMem m addr ≡ just (encode a)
    snd-valid : readMem m (addr +ℕ 8) ≡ just (encode b)

open PairAt public

-- | A left sum value (inj₁ a) is encoded at address addr in memory m
-- This means: m[addr] = 0 (tag), m[addr+8] = encode a
record InlAt {A B : Type} (a : ⟦ A ⟧) (addr : Word) (m : Memory) : Set where
  constructor inl-at
  field
    tag-valid : readMem m addr ≡ just 0
    val-valid : readMem m (addr +ℕ 8) ≡ just (encode a)

open InlAt public

-- | A right sum value (inj₂ b) is encoded at address addr in memory m
-- This means: m[addr] = 1 (tag), m[addr+8] = encode b
record InrAt {A B : Type} (b : ⟦ B ⟧) (addr : Word) (m : Memory) : Set where
  constructor inr-at
  field
    tag-valid : readMem m addr ≡ just 1
    val-valid : readMem m (addr +ℕ 8) ≡ just (encode b)

open InrAt public

------------------------------------------------------------------------
-- Stateful Validity Predicates (no reference to abstract encode)
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
    snd-valid : readMem m (addr-pair +ℕ 8) ≡ just addr-b

open PairAtS public using () renaming (fst-valid to fst-valid-s; snd-valid to snd-valid-s)

-- | Left sum validity with explicit value address
-- Memory at addr-sum contains [0, addr-val]
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val

open InlAtS public using () renaming (tag-valid to tag-valid-inl-s; val-valid to val-valid-inl-s)

-- | Right sum validity with explicit value address
-- Memory at addr-sum contains [1, addr-val]
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ 8) ≡ just addr-val

open InrAtS public using () renaming (tag-valid to tag-valid-inr-s; val-valid to val-valid-inr-s)

-- | Closure validity with explicit component addresses
-- Memory at addr-closure contains [env-val, code-ptr]
-- This is the same structure as PairAtS, but with semantic meaning for closures
record ClosureAtS (env-val code-ptr addr-closure : Word) (m : Memory) : Set where
  constructor closure-at-s
  field
    is-pair : PairAtS env-val code-ptr addr-closure m

open ClosureAtS public using (is-pair)

------------------------------------------------------------------------
-- Creating validity proofs from allocation
------------------------------------------------------------------------

-- | Allocate a pair and create validity proof
-- Uses proven mem-read-write and mem-read-other
alloc-pair-creates-valid : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr (encode a)
      m₂ = writeMem m₁ (addr +ℕ 8) (encode b)
  in PairAt a b addr m₂
alloc-pair-creates-valid a b addr m = pair-at fst-proof snd-proof
  where
    m₁ = writeMem m addr (encode a)
    m₂ = writeMem m₁ (addr +ℕ 8) (encode b)

    -- m₂[addr] = m₁[addr] (by mem-read-other, since addr ≠ addr+8)
    --          = encode a (by mem-read-write)
    fst-proof : readMem m₂ addr ≡ just (encode a)
    fst-proof = trans
      (mem-read-other {m₁} {addr +ℕ 8} {addr} {encode b} (λ eq → n≢n+8 addr (sym eq)))
      (mem-read-write {m} {addr} {encode a})

    -- m₂[addr+8] = encode b (by mem-read-write)
    snd-proof : readMem m₂ (addr +ℕ 8) ≡ just (encode b)
    snd-proof = mem-read-write {m₁} {addr +ℕ 8} {encode b}

-- | Allocate left sum and create validity proof
alloc-inl-creates-valid : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr 0
      m₂ = writeMem m₁ (addr +ℕ 8) (encode a)
  in InlAt {A} {B} a addr m₂
alloc-inl-creates-valid a addr m = inl-at tag-proof val-proof
  where
    m₁ = writeMem m addr 0
    m₂ = writeMem m₁ (addr +ℕ 8) (encode a)

    tag-proof : readMem m₂ addr ≡ just 0
    tag-proof = trans
      (mem-read-other {m₁} {addr +ℕ 8} {addr} {encode a} (λ eq → n≢n+8 addr (sym eq)))
      (mem-read-write {m} {addr} {0})

    val-proof : readMem m₂ (addr +ℕ 8) ≡ just (encode a)
    val-proof = mem-read-write {m₁} {addr +ℕ 8} {encode a}

-- | Allocate right sum and create validity proof
alloc-inr-creates-valid : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  let m₁ = writeMem m addr 1
      m₂ = writeMem m₁ (addr +ℕ 8) (encode b)
  in InrAt {A} {B} b addr m₂
alloc-inr-creates-valid b addr m = inr-at tag-proof val-proof
  where
    m₁ = writeMem m addr 1
    m₂ = writeMem m₁ (addr +ℕ 8) (encode b)

    tag-proof : readMem m₂ addr ≡ just 1
    tag-proof = trans
      (mem-read-other {m₁} {addr +ℕ 8} {addr} {encode b} (λ eq → n≢n+8 addr (sym eq)))
      (mem-read-write {m} {addr} {1})

    val-proof : readMem m₂ (addr +ℕ 8) ≡ just (encode b)
    val-proof = mem-read-write {m₁} {addr +ℕ 8} {encode b}

------------------------------------------------------------------------
-- Stateful allocation proofs (with explicit addresses)
------------------------------------------------------------------------

-- | Create PairAtS from two writes
alloc-pair-creates-valid-s : ∀ (addr-a addr-b addr-pair : Word) (m : Memory) →
  let m₁ = writeMem m addr-pair addr-a
      m₂ = writeMem m₁ (addr-pair +ℕ 8) addr-b
  in PairAtS addr-a addr-b addr-pair m₂
alloc-pair-creates-valid-s addr-a addr-b addr-pair m = pair-at-s fst-proof snd-proof
  where
    m₁ = writeMem m addr-pair addr-a
    m₂ = writeMem m₁ (addr-pair +ℕ 8) addr-b

    fst-proof : readMem m₂ addr-pair ≡ just addr-a
    fst-proof = trans
      (mem-read-other {m₁} {addr-pair +ℕ 8} {addr-pair} {addr-b} (λ eq → n≢n+8 addr-pair (sym eq)))
      (mem-read-write {m} {addr-pair} {addr-a})

    snd-proof : readMem m₂ (addr-pair +ℕ 8) ≡ just addr-b
    snd-proof = mem-read-write {m₁} {addr-pair +ℕ 8} {addr-b}

-- | Create InlAtS from two writes
alloc-inl-creates-valid-s : ∀ (addr-val addr-sum : Word) (m : Memory) →
  let m₁ = writeMem m addr-sum 0
      m₂ = writeMem m₁ (addr-sum +ℕ 8) addr-val
  in InlAtS addr-val addr-sum m₂
alloc-inl-creates-valid-s addr-val addr-sum m = inl-at-s tag-proof val-proof
  where
    m₁ = writeMem m addr-sum 0
    m₂ = writeMem m₁ (addr-sum +ℕ 8) addr-val

    tag-proof : readMem m₂ addr-sum ≡ just 0
    tag-proof = trans
      (mem-read-other {m₁} {addr-sum +ℕ 8} {addr-sum} {addr-val} (λ eq → n≢n+8 addr-sum (sym eq)))
      (mem-read-write {m} {addr-sum} {0})

    val-proof : readMem m₂ (addr-sum +ℕ 8) ≡ just addr-val
    val-proof = mem-read-write {m₁} {addr-sum +ℕ 8} {addr-val}

-- | Create InrAtS from two writes
alloc-inr-creates-valid-s : ∀ (addr-val addr-sum : Word) (m : Memory) →
  let m₁ = writeMem m addr-sum 1
      m₂ = writeMem m₁ (addr-sum +ℕ 8) addr-val
  in InrAtS addr-val addr-sum m₂
alloc-inr-creates-valid-s addr-val addr-sum m = inr-at-s tag-proof val-proof
  where
    m₁ = writeMem m addr-sum 1
    m₂ = writeMem m₁ (addr-sum +ℕ 8) addr-val

    tag-proof : readMem m₂ addr-sum ≡ just 1
    tag-proof = trans
      (mem-read-other {m₁} {addr-sum +ℕ 8} {addr-sum} {addr-val} (λ eq → n≢n+8 addr-sum (sym eq)))
      (mem-read-write {m} {addr-sum} {1})

    val-proof : readMem m₂ (addr-sum +ℕ 8) ≡ just addr-val
    val-proof = mem-read-write {m₁} {addr-sum +ℕ 8} {addr-val}

------------------------------------------------------------------------
-- Deriving encoding properties from validity proofs
--
-- These replace the axioms in Postulates.agda with derived lemmas.
-- The key difference: they require a validity proof as input.
------------------------------------------------------------------------

-- | Derived: reading first component of a valid pair
-- Replaces: encode-pair-fst axiom
encode-pair-fst-derived : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  PairAt a b addr m →
  readMem m addr ≡ just (encode a)
encode-pair-fst-derived a b addr m valid = fst-valid valid

-- | Derived: reading second component of a valid pair
-- Replaces: encode-pair-snd axiom
encode-pair-snd-derived : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  PairAt a b addr m →
  readMem m (addr +ℕ 8) ≡ just (encode b)
encode-pair-snd-derived a b addr m valid = snd-valid valid

-- | Derived: reading tag of a valid left sum
encode-inl-tag-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m addr ≡ just 0
encode-inl-tag-derived a addr m valid = tag-valid valid

-- | Derived: reading value of a valid left sum
encode-inl-val-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m (addr +ℕ 8) ≡ just (encode a)
encode-inl-val-derived a addr m valid = val-valid valid

-- | Derived: reading tag of a valid right sum
encode-inr-tag-derived : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  InrAt {A} {B} b addr m →
  readMem m addr ≡ just 1
encode-inr-tag-derived b addr m valid = tag-valid valid

-- | Derived: reading value of a valid right sum
encode-inr-val-derived : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  InrAt {A} {B} b addr m →
  readMem m (addr +ℕ 8) ≡ just (encode b)
encode-inr-val-derived b addr m valid = val-valid valid

------------------------------------------------------------------------
-- Preservation: validity survives writes to other addresses
------------------------------------------------------------------------

-- | Helper: addr₁ ≠ addr₂ and addr₁ ≠ addr₂ + 8 (pair doesn't overlap)
record NoOverlap (addr₁ addr₂ : Word) : Set where
  constructor no-overlap
  field
    neq-base : addr₁ ≢ addr₂
    neq-snd  : addr₁ ≢ addr₂ +ℕ 8

-- | Writing to a non-overlapping address preserves pair validity
pair-valid-preserved : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (pair-addr write-addr : Word) (v : Word) (m : Memory) →
  PairAt a b pair-addr m →
  NoOverlap write-addr pair-addr →
  write-addr ≢ pair-addr +ℕ 8 →
  PairAt a b pair-addr (writeMem m write-addr v)
pair-valid-preserved a b pair-addr write-addr v m valid no-over neq-snd =
  pair-at fst-preserved snd-preserved
  where
    m' = writeMem m write-addr v

    fst-preserved : readMem m' pair-addr ≡ just (encode a)
    fst-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr} {v} (NoOverlap.neq-base no-over))
      (fst-valid valid)

    snd-preserved : readMem m' (pair-addr +ℕ 8) ≡ just (encode b)
    snd-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr +ℕ 8} {v} neq-snd)
      (snd-valid valid)

-- | Writing to a non-overlapping address preserves PairAtS validity
pair-valid-preserved-s : ∀ (addr-a addr-b pair-addr write-addr : Word) (v : Word) (m : Memory) →
  PairAtS addr-a addr-b pair-addr m →
  NoOverlap write-addr pair-addr →
  write-addr ≢ pair-addr +ℕ 8 →
  PairAtS addr-a addr-b pair-addr (writeMem m write-addr v)
pair-valid-preserved-s addr-a addr-b pair-addr write-addr v m valid no-over neq-snd =
  pair-at-s fst-preserved snd-preserved
  where
    m' = writeMem m write-addr v

    fst-preserved : readMem m' pair-addr ≡ just addr-a
    fst-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr} {v} (NoOverlap.neq-base no-over))
      (fst-valid-s valid)

    snd-preserved : readMem m' (pair-addr +ℕ 8) ≡ just addr-b
    snd-preserved = trans
      (mem-read-other {m} {write-addr} {pair-addr +ℕ 8} {v} neq-snd)
      (snd-valid-s valid)

------------------------------------------------------------------------
-- Summary: How to use this module
--
-- OLD (using axioms from Postulates.agda):
--   mem-eq = encode-pair-fst a b (memory s)
--
-- NEW (using derived lemmas with validity proof):
--   mem-eq = encode-pair-fst-derived a b addr (memory s) valid
--   where valid : PairAt a b addr (memory s) is a precondition
--
-- The validity proof can be:
-- 1. Created by alloc-*-creates-valid when allocating
-- 2. Preserved through writes using *-valid-preserved
-- 3. Threaded as a precondition like StackInvariant
------------------------------------------------------------------------
