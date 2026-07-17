-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.MemPreserve  (Plan 0.54 Phase B / Option 2)
--
-- The memory analog of register-confinement, over the REAL x86-64 memory
-- model (`Once.CCC.Target.X86-64.Semantics.Memory = Word → Maybe Word`).
--
-- The arith block's scratch slots live BELOW `%rsp` (`-N(%rsp)`); CCC's live
-- data is at/above `%rsp`. So a scratch write (address `< rsp`) preserves every
-- CCC read (address `≥ rsp`) — the memory-region twin of `owner`-disjointness.
-- `writeMem` is a one-address update, so this is a clean `≢`-argument.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.MemPreserve where

open import Data.Bool using (true; false; T)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; _<_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; <-transˡ; <⇒≢)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; _≢_)

open import Once.CCC.Target.X86-64.Semantics using (Memory; readMem; writeMem; Word)

------------------------------------------------------------------------
-- A write to a DIFFERENT address preserves a read.
------------------------------------------------------------------------

readMem-writeMem-other : ∀ m addr val a → a ≢ addr →
                         readMem (writeMem m addr val) a ≡ readMem m a
readMem-writeMem-other m addr val a neq with a ≡ᵇ addr in eq
... | false = refl
... | true  = ⊥-elim (neq (≡ᵇ⇒≡ a addr (subst T (sym eq) tt)))

------------------------------------------------------------------------
-- Region agreement: two memories agree on every address at/above `fr`.
------------------------------------------------------------------------

AgreeMemFrom : Word → Memory → Memory → Set
AgreeMemFrom fr m m' = ∀ a → fr ≤ a → readMem m a ≡ readMem m' a

-- A write strictly BELOW the frontier preserves everything at/above it.
--   addr < fr ≤ a  ⇒  addr < a  ⇒  a ≢ addr.
writeMem-below-preserves : ∀ m fr addr val → addr < fr →
                           AgreeMemFrom fr m (writeMem m addr val)
writeMem-below-preserves m fr addr val addr<fr a fr≤a =
  sym (readMem-writeMem-other m addr val a a≢addr)
  where
    a≢addr : a ≢ addr
    a≢addr a≡addr = <⇒≢ (<-transˡ addr<fr fr≤a) (sym a≡addr)
