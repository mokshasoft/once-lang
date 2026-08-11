-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.Memory
--
-- Common helper lemmas for memory proofs shared by all backends.
-- These are pure lemmas about natural numbers and boolean equality
-- that are used in memory-related proofs.
--
-- Usage in backend Correct.agda:
--   open import Once.Memory.Memory public
------------------------------------------------------------------------

module Once.Memory.Memory where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; _≢_; inspect) renaming ([_] to ⟦_⟧)

------------------------------------------------------------------------
-- Boolean equality lemmas
------------------------------------------------------------------------

-- | n ≡ᵇ n is always true
≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

------------------------------------------------------------------------
-- Address inequality helpers
------------------------------------------------------------------------

-- | n ≢ n + suc k (used for proving disjoint stack addresses)
n≢n+suc : ∀ (n k : ℕ) → n ≢ (n + suc k)
n≢n+suc n k eq = helper n k (sym eq)
  where
    suc-injective : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    helper : ∀ n k → (n + suc k) ≢ n
    helper zero k ()
    helper (suc n) k eq = helper n k (suc-injective eq)

-- | n ≡ᵇ (n + 8) is false (used for word-size aligned stack operations)
n≢n+word-size-bool : ∀ (n : ℕ) → (n ≡ᵇ (n + 8)) ≡ false
n≢n+word-size-bool zero = refl
n≢n+word-size-bool (suc n) = n≢n+word-size-bool n

-- | (n + 8) ≡ᵇ n is false (swapped version)
n+word-size≢n-bool : ∀ (n : ℕ) → ((n + 8) ≡ᵇ n) ≡ false
n+word-size≢n-bool zero = refl
n+word-size≢n-bool (suc n) = n+word-size≢n-bool n

-- | n ≡ᵇ (n + 16) is false
n≢n+16-bool : ∀ (n : ℕ) → (n ≡ᵇ (n + 16)) ≡ false
n≢n+16-bool zero = refl
n≢n+16-bool (suc n) = n≢n+16-bool n

-- | (n + 16) ≡ᵇ n is false
n+16≢n-bool : ∀ (n : ℕ) → ((n + 16) ≡ᵇ n) ≡ false
n+16≢n-bool zero = refl
n+16≢n-bool (suc n) = n+16≢n-bool n

-- | Boolean equality implies propositional equality
≡ᵇ⇒≡ : ∀ (m n : ℕ) → (m ≡ᵇ n) ≡ true → m ≡ n
≡ᵇ⇒≡ zero zero _ = refl
≡ᵇ⇒≡ (suc m) (suc n) eq = cong suc (≡ᵇ⇒≡ m n eq)

------------------------------------------------------------------------
-- Memory Model
------------------------------------------------------------------------

-- All backends use identical memory model: Word = ℕ, Memory = Word → Maybe Word
-- These definitions mirror those in Backend/*/Semantics.agda

-- | 64-bit word (represented as ℕ)
Word : Set
Word = ℕ

-- | Memory is a partial function from addresses to values
Memory : Set
Memory = Word → Maybe Word

-- | Read from memory
readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- | Write to memory (identical to all backend definitions)
writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

------------------------------------------------------------------------
-- Memory Read/Write Lemmas
------------------------------------------------------------------------

-- | Reading from the address we just wrote returns the written value
readMem-writeMem-same : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m addr v) addr ≡ just v
readMem-writeMem-same m addr v with addr ≡ᵇ addr | ≡ᵇ-refl addr
... | true | _ = refl

-- | Reading from a different address after a write returns the old value
-- (propositional inequality version - used by X86 and RiscV64)
readMem-writeMem-diff : ∀ (m : Memory) (addr1 addr2 : Word) (v : Word) →
  addr1 ≢ addr2 →
  readMem (writeMem m addr1 v) addr2 ≡ readMem m addr2
readMem-writeMem-diff m addr1 addr2 v addr1≢addr2 with addr2 ≡ᵇ addr1 | inspect (_≡ᵇ addr1) addr2
... | false | _ = refl
... | true | ⟦ eq ⟧ = ⊥-elim (addr1≢addr2 (sym (≡ᵇ⇒≡ addr2 addr1 eq)))

-- | Reading from a different address after a write returns the old value
-- (boolean version - used by AArch64)
readMem-writeMem-diff-bool : ∀ (m : Memory) (addr1 addr2 : Word) (v : Word) →
  (addr2 ≡ᵇ addr1) ≡ false →
  readMem (writeMem m addr1 v) addr2 ≡ readMem m addr2
readMem-writeMem-diff-bool m addr1 addr2 v neq rewrite neq = refl