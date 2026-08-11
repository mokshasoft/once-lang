-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory
--
-- Shared memory model for semantics and backend proofs.
--
-- This module provides:
-- - Word type (machine words)
-- - Memory type (word → maybe word)
-- - Concrete readMem and writeMem operations
-- - AllocState for allocation tracking
-- - Memory theorems (mem-read-write, mem-read-other)
--
-- By centralizing the memory model here, both Once.Semantics and
-- Once.Target.X86.Encoding can share the same definitions and proofs.
------------------------------------------------------------------------

module Once.Memory where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat using (_≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Word Type
------------------------------------------------------------------------

Word : Set
Word = ℕ

-- Size of a word in bytes (8 bytes = 64 bits)
word-size : ℕ
word-size = 8

-- Size of two words (for pair/sum allocation)
two-words : ℕ
two-words = word-size +ℕ word-size

------------------------------------------------------------------------
-- Memory Type
------------------------------------------------------------------------

Memory : Set
Memory = Word → Maybe Word

------------------------------------------------------------------------
-- Memory Operations (Concrete Definitions)
------------------------------------------------------------------------

readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- Concrete writeMem using boolean equality
-- This enables proofs by computation!
writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

------------------------------------------------------------------------
-- Helper: ≡ᵇ is reflexive
------------------------------------------------------------------------

≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

------------------------------------------------------------------------
-- THEOREM: Read after write (same address)
------------------------------------------------------------------------

mem-read-write : ∀ {m : Memory} {addr v : Word} →
  readMem (writeMem m addr v) addr ≡ just v
mem-read-write {m} {addr} {v} = lemma
  where
    lemma : (if addr ≡ᵇ addr then just v else m addr) ≡ just v
    lemma rewrite ≡ᵇ-refl addr = refl

------------------------------------------------------------------------
-- THEOREM: Frame rule (different addresses)
------------------------------------------------------------------------

-- Helper: if n ≡ᵇ m = true, then n ≡ m
≡ᵇ-true→≡ : ∀ {n m : ℕ} → (n ≡ᵇ m) ≡ true → n ≡ m
≡ᵇ-true→≡ {zero} {zero} _ = refl
≡ᵇ-true→≡ {suc n} {suc m} p = cong suc (≡ᵇ-true→≡ p)

mem-read-other : ∀ {m : Memory} {addr₁ addr₂ v : Word} →
  addr₁ ≢ addr₂ →
  readMem (writeMem m addr₁ v) addr₂ ≡ readMem m addr₂
mem-read-other {m} {addr₁} {addr₂} {v} neq = lemma
  where
    addr₂≢addr₁ : addr₂ ≢ addr₁
    addr₂≢addr₁ eq = neq (sym eq)

    ≡ᵇ-false : (addr₂ ≡ᵇ addr₁) ≡ false
    ≡ᵇ-false with addr₂ ≡ᵇ addr₁ in eq
    ... | false = refl
    ... | true = ⊥-elim (addr₂≢addr₁ (≡ᵇ-true→≡ eq))

    lemma : (if addr₂ ≡ᵇ addr₁ then just v else m addr₂) ≡ m addr₂
    lemma rewrite ≡ᵇ-false = refl

------------------------------------------------------------------------
-- Allocation State
------------------------------------------------------------------------

record AllocState : Set where
  constructor alloc-state
  field
    mem : Memory
    heap-ptr : Word

open AllocState public

-- Initial allocation state (empty memory, heap starts at 1000)
init-alloc-state : AllocState
init-alloc-state = alloc-state (λ _ → nothing) 1000

------------------------------------------------------------------------
-- Allocation Primitives
------------------------------------------------------------------------

-- Allocate two words (for pairs, sums, closures)
alloc-two-words : AllocState → Word → Word → AllocState × Word
alloc-two-words st v₁ v₂ = (st' , base)
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base v₁
    m₂ = writeMem m₁ (base +ℕ word-size) v₂
    st' = alloc-state m₂ (base +ℕ two-words)

------------------------------------------------------------------------
-- Helper: n ≢ n + word-size
------------------------------------------------------------------------

n≢n+suc-m : ∀ (n m : ℕ) → n ≢ n +ℕ suc m
n≢n+suc-m zero m ()
n≢n+suc-m (suc n) m eq = n≢n+suc-m n m (suc-injective eq)
  where
    suc-injective : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
    suc-injective refl = refl

n≢n+word-size : ∀ (n : ℕ) → n ≢ n +ℕ word-size
n≢n+word-size n = n≢n+suc-m n 7

------------------------------------------------------------------------
-- Allocation Theorems
------------------------------------------------------------------------

-- Reading first word of allocated pair
alloc-two-words-fst : ∀ (st : AllocState) (v₁ v₂ : Word) →
  let (st' , base) = alloc-two-words st v₁ v₂
  in readMem (mem st') base ≡ just v₁
alloc-two-words-fst st v₁ v₂ = trans step1 step2
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base v₁
    m₂ = writeMem m₁ (base +ℕ word-size) v₂

    step1 : readMem m₂ base ≡ readMem m₁ base
    step1 = mem-read-other {m₁} {base +ℕ 8} {base} {v₂} (λ eq → n≢n+word-size base (sym eq))

    step2 : readMem m₁ base ≡ just v₁
    step2 = mem-read-write {mem st} {base} {v₁}

-- Reading second word of allocated pair
alloc-two-words-snd : ∀ (st : AllocState) (v₁ v₂ : Word) →
  let (st' , base) = alloc-two-words st v₁ v₂
  in readMem (mem st') (base +ℕ word-size) ≡ just v₂
alloc-two-words-snd st v₁ v₂ =
  mem-read-write {writeMem (mem st) (heap-ptr st) v₁} {heap-ptr st +ℕ 8} {v₂}

------------------------------------------------------------------------
-- Export for use by other modules
------------------------------------------------------------------------

-- Re-export everything for convenience