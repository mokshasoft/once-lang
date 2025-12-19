------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MemoryValid
--
-- Memory validity predicates for x86-64 execution.
-- Tracks which values are properly encoded in memory.
--
-- Key insight: The encoding axioms in Postulates.agda claim to hold
-- for ANY memory m. This is too strong. They should only hold for
-- memory where values were properly allocated.
--
-- MemoryValid captures the invariant that values in memory are
-- properly encoded at their expected addresses.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MemoryValid where

open import Once.Type
open import Once.Semantics using (⟦_⟧; encode)
open import Once.Backend.X86.Semantics using (State; Memory; Word; readMem; writeMem)
open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+8)

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
-- Replaces: encode-inl-tag axiom
encode-inl-tag-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m addr ≡ just 0
encode-inl-tag-derived a addr m valid = tag-valid valid

-- | Derived: reading value of a valid left sum
-- Replaces: encode-inl-val axiom
encode-inl-val-derived : ∀ {A B} (a : ⟦ A ⟧) (addr : Word) (m : Memory) →
  InlAt {A} {B} a addr m →
  readMem m (addr +ℕ 8) ≡ just (encode a)
encode-inl-val-derived a addr m valid = val-valid valid

-- | Derived: reading tag of a valid right sum
-- Replaces: encode-inr-tag axiom
encode-inr-tag-derived : ∀ {A B} (b : ⟦ B ⟧) (addr : Word) (m : Memory) →
  InrAt {A} {B} b addr m →
  readMem m addr ≡ just 1
encode-inr-tag-derived b addr m valid = tag-valid valid

-- | Derived: reading value of a valid right sum
-- Replaces: encode-inr-val axiom
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

------------------------------------------------------------------------
-- Connection to encode function
--
-- Key bridge: if encode (a, b) = addr and PairAt a b addr m,
-- then the encoding axioms hold.
------------------------------------------------------------------------

-- | Bridge axiom: encode returns the address where value is allocated
-- This connects abstract encode to concrete validity.
-- TODO: This could be eliminated by making encode stateful.
postulate
  encode-pair-is-addr : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
    ∃[ addr ] (encode {A * B} (a , b) ≡ addr)
    -- The addr here should be the allocation address

  encode-inl-is-addr : ∀ {A B} (a : ⟦ A ⟧) →
    ∃[ addr ] (encode {A + B} (inj₁ a) ≡ addr)

  encode-inr-is-addr : ∀ {A B} (b : ⟦ B ⟧) →
    ∃[ addr ] (encode {A + B} (inj₂ b) ≡ addr)


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
