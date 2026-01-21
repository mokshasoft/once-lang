------------------------------------------------------------------------
-- Once.Backend.Common.Validity
--
-- Architecture-independent validity structures.
--
-- This module defines the STRUCTURE of memory validity predicates
-- using the shared Word/Memory types from Once.Memory.
--
-- Key abstractions:
--   - PairAtS, InlAtS, InrAtS, ClosureAtS: memory layout records
--   - ValidAtInterface: what validity implementations must provide
--   - Preservation lemmas for memory layout structures
------------------------------------------------------------------------

module Once.Backend.Common.Validity where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Once.Type using (Type; Unit; _*_; _+_; _⇒_; Eff; Fix)
open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧; wrap)
open import Once.Memory using (Word; Memory; readMem; word-size)
open ⟦Fix⟧

------------------------------------------------------------------------
-- Memory Layout Structures
--
-- These records describe how compound values are laid out in memory.
-- Shared across all architectures (all use Word = ℕ, word-size = 8).
------------------------------------------------------------------------

-- | Pair memory layout: [addr-a, addr-b] at addr
record PairAtS (addr-a addr-b addr : Word) (m : Memory) : Set where
  constructor pair-at-s
  field
    fst-valid : readMem m addr ≡ just addr-a
    snd-valid : readMem m (addr +ℕ word-size) ≡ just addr-b

open PairAtS public using () renaming (fst-valid to fst-valid-s; snd-valid to snd-valid-s)

-- | Left sum layout: [0, addr-val] at addr
record InlAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inl-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 0
    val-valid : readMem m (addr-sum +ℕ word-size) ≡ just addr-val

open InlAtS public using () renaming (tag-valid to tag-valid-inl-s; val-valid to val-valid-inl-s)

-- | Right sum layout: [1, addr-val] at addr
record InrAtS (addr-val addr-sum : Word) (m : Memory) : Set where
  constructor inr-at-s
  field
    tag-valid : readMem m addr-sum ≡ just 1
    val-valid : readMem m (addr-sum +ℕ word-size) ≡ just addr-val

open InrAtS public using () renaming (tag-valid to tag-valid-inr-s; val-valid to val-valid-inr-s)

-- | Closure layout: [env-addr, code-ptr] at addr
record ClosureAtS (env-addr code-ptr addr : Word) (m : Memory) : Set where
  constructor closure-at-s
  field
    env-valid : readMem m addr ≡ just env-addr
    code-valid : readMem m (addr +ℕ word-size) ≡ just code-ptr

open ClosureAtS public using () renaming (env-valid to env-valid-s; code-valid to code-valid-s)

------------------------------------------------------------------------
-- Structure Preservation under Memory Equality
--
-- These lemmas show that memory layout is preserved when memory
-- reads return the same values. Shared across architectures.
------------------------------------------------------------------------

PairAtS-preserved-under-mem-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-mem-eq {addr-a} {addr-b} {addr} pairS mem-eq =
  pair-at-s (trans (mem-eq addr) (fst-valid-s pairS))
            (trans (mem-eq (addr +ℕ word-size)) (snd-valid-s pairS))

InlAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-mem-eq {addr-val} {addr-sum} inlS mem-eq =
  inl-at-s (trans (mem-eq addr-sum) (tag-valid-inl-s inlS))
           (trans (mem-eq (addr-sum +ℕ word-size)) (val-valid-inl-s inlS))

InrAtS-preserved-under-mem-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-mem-eq {addr-val} {addr-sum} inrS mem-eq =
  inr-at-s (trans (mem-eq addr-sum) (tag-valid-inr-s inrS))
           (trans (mem-eq (addr-sum +ℕ word-size)) (val-valid-inr-s inrS))

ClosureAtS-preserved-under-mem-eq :
  ∀ {env-addr code-ptr addr : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr m1 →
  (∀ a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr m2
ClosureAtS-preserved-under-mem-eq {env-addr} {code-ptr} {addr} closS mem-eq =
  closure-at-s (trans (mem-eq addr) (env-valid-s closS))
               (trans (mem-eq (addr +ℕ word-size)) (code-valid-s closS))

------------------------------------------------------------------------
-- ValidAt Interface
--
-- This describes WHAT validity means abstractly. Each architecture
-- can provide its own implementation or use the shared data type.
------------------------------------------------------------------------

record ValidAtInterface : Set₁ where
  field
    -- The validity predicate
    ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set

    -- Validity of unit (always at address 0)
    valid-unit : ∀ {m} → ValidAt {Unit} tt 0 m

    -- Validity of pairs
    valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr-a addr-b addr : Word} {m : Memory} →
      ValidAt a addr-a m →
      ValidAt b addr-b m →
      PairAtS addr-a addr-b addr m →
      ValidAt (a , b) addr m

    -- Validity of left sum
    valid-inl : ∀ {A B} {a : ⟦ A ⟧} {addr-a addr : Word} {m : Memory} →
      ValidAt a addr-a m →
      InlAtS addr-a addr m →
      ValidAt {A + B} (inj₁ a) addr m

    -- Validity of right sum
    valid-inr : ∀ {A B} {b : ⟦ B ⟧} {addr-b addr : Word} {m : Memory} →
      ValidAt b addr-b m →
      InrAtS addr-b addr m →
      ValidAt {A + B} (inj₂ b) addr m

    -- Validity of closures
    valid-closure : ∀ {A B} {cl : Closure A B} {code-ptr addr : Word} {m : Memory} →
      ClosureAtS (Closure.env-addr cl) code-ptr addr m →
      ValidAt {A ⇒ B} cl addr m

    -- Validity of Fix (wrapper is transparent)
    valid-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory} →
      ValidAt x addr m →
      ValidAt {Fix F} (wrap x) addr m

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. Memory layout records (PairAtS, InlAtS, InrAtS, ClosureAtS)
--   2. Preservation lemmas for layouts under memory equality
--   3. ValidAtInterface - abstract validity predicate interface
--
-- Each architecture can:
--   1. Use these layout records directly
--   2. Implement ValidAtInterface or define its own ValidAt data type
--   3. Use the preservation lemmas for memory reasoning
------------------------------------------------------------------------
