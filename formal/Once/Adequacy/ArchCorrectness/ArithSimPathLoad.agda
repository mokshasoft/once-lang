-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoad  (Plan 0.54 rung B / B2.3)
--
-- The arch-generic INPUT-POINTER chase and its memory-congruence lemma, shared
-- by every arith-sim instance (x86-64 / riscv64 / x86-32). The concrete memory
-- model is the SAME `ℕ → Maybe ℕ` on every arch, so `path-load-go` and
-- `plg-mem-cong` differ only in the per-arch `def` / `side-off` — taken as
-- parameters. `plg-mem-cong` (needed because `path-load-go` is stuck on the path
-- variable) inducts on the path; each instance discharges its `pl-inv` from it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import Once.Arith.Machine.Shape using (InputPath; Side)

module Once.Adequacy.ArchCorrectness.ArithSimPathLoad
  (St : Set)
  (mem : St → ℕ → Maybe ℕ)          -- the arch's memory accessor (Memory = ℕ → Maybe ℕ)
  (def : Maybe ℕ → ℕ)
  (side-off : Side → ℕ)
  where

path-load-go : St → ℕ → InputPath → ℕ
path-load-go s addr []          = def (mem s addr)
path-load-go s addr (sd ∷ rest) = path-load-go s (def (mem s (addr + side-off sd))) rest

-- path-load-go depends on the state ONLY through its memory (proved by induction
-- on the path). Every `pl-inv` non-spill case rides this with a `refl` memory-eq.
plg-mem-cong : ∀ A B addr p → mem A ≡ mem B → path-load-go A addr p ≡ path-load-go B addr p
plg-mem-cong A B addr []          meq = cong (λ m → def (m addr)) meq
plg-mem-cong A B addr (sd ∷ rest) meq =
  trans (cong (λ m → path-load-go A (def (m (addr + side-off sd))) rest) meq)
        (plg-mem-cong A B (def (mem B (addr + side-off sd))) rest meq)
