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

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; _≡ᵇ_; _≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Bool using (T)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Data.Maybe using (Maybe; just)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; _≢_; inspect) renaming ([_] to ⟦_⟧)

------------------------------------------------------------------------
-- Boolean equality: `n ≡ᵇ n` is `does (n ≟ n)` by definition (stdlib).
------------------------------------------------------------------------

≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl n = dec-true (n ≟ n) refl

≢⇒≡ᵇfalse : ∀ (m n : ℕ) → m ≢ n → (m ≡ᵇ n) ≡ false
≢⇒≡ᵇfalse m n ¬p = dec-false (m ≟ n) ¬p

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
... | true | ⟦ eq ⟧ = ⊥-elim (addr1≢addr2 (sym (≡ᵇ⇒≡ addr2 addr1 (subst T (sym eq) tt))))

-- | Reading from a different address after a write returns the old value
-- (boolean version - used by AArch64)
readMem-writeMem-diff-bool : ∀ (m : Memory) (addr1 addr2 : Word) (v : Word) →
  (addr2 ≡ᵇ addr1) ≡ false →
  readMem (writeMem m addr1 v) addr2 ≡ readMem m addr2
readMem-writeMem-diff-bool m addr1 addr2 v neq rewrite neq = refl