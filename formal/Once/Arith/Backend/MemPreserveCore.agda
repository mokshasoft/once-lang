-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.MemPreserveCore  (Plan 0.54 Phase B / Option 2)
--
-- The arch-generic MEMORY CCC-preservation framework: the arith scratch write
-- (below the entry stack frontier) preserves every CCC read (at/above it). The
-- memory model is the same `Word(=ℕ) → Maybe Word` on every arch, so the only
-- per-arch input is `readMem-writeMem-other` (a one-address update leaves other
-- addresses alone — a 3-line proof, identical per arch).
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (<-transˡ; <⇒≢)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)

module Once.Arith.Backend.MemPreserveCore
  {Memory : Set}
  (readMem  : Memory → ℕ → Maybe ℕ)
  (writeMem : Memory → ℕ → ℕ → Memory)
  (readMem-writeMem-other : ∀ m addr val a → a ≢ addr →
                            readMem (writeMem m addr val) a ≡ readMem m a)
  where

-- Two memories agree on every address at/above the frontier `fr`.
AgreeMemFrom : ℕ → Memory → Memory → Set
AgreeMemFrom fr m m' = ∀ a → fr ≤ a → readMem m a ≡ readMem m' a

AgreeMemFrom-refl : ∀ fr m → AgreeMemFrom fr m m
AgreeMemFrom-refl fr m a _ = refl

AgreeMemFrom-trans : ∀ {fr m₁ m₂ m₃} →
                     AgreeMemFrom fr m₁ m₂ → AgreeMemFrom fr m₂ m₃ → AgreeMemFrom fr m₁ m₃
AgreeMemFrom-trans {fr} p q a fr≤a rewrite p a fr≤a = q a fr≤a

-- A write strictly BELOW the frontier preserves everything at/above it.
writeMem-below-preserves : ∀ m fr addr val → addr < fr →
                           AgreeMemFrom fr m (writeMem m addr val)
writeMem-below-preserves m fr addr val addr<fr a fr≤a =
  sym (readMem-writeMem-other m addr val a a≢addr)
  where
    a≢addr : a ≢ addr
    a≢addr a≡addr = <⇒≢ (<-transˡ addr<fr fr≤a) (sym a≡addr)
