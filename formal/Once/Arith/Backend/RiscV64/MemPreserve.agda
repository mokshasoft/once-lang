-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.MemPreserve  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 memory CCC-preservation: only the per-arch base — that a one-address
-- `writeMem` leaves other addresses alone — over the real riscv64 `Memory`. The
-- framework (`AgreeMemFrom`, `writeMem-below-preserves`) is the arch-generic
-- `Once.Arith.Backend.MemPreserveCore`, re-exported.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.MemPreserve where

open import Data.Bool using (true; false; T)
open import Data.Unit using (tt)
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; _≢_)

open import Once.CCC.Target.RiscV64.Semantics using (Memory; readMem; writeMem)

-- BASE: a write to a different address preserves a read.
readMem-writeMem-other : ∀ m addr val a → a ≢ addr →
                         readMem (writeMem m addr val) a ≡ readMem m a
readMem-writeMem-other m addr val a neq with a ≡ᵇ addr in eq
... | false = refl
... | true  = ⊥-elim (neq (≡ᵇ⇒≡ a addr (subst T (sym eq) tt)))

open import Once.Arith.Backend.MemPreserveCore readMem writeMem readMem-writeMem-other public
