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
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Data.List using ([]; _∷_)

open import Once.Arith.Machine.Shape using (InputPath; flat-addr)

module Once.Adequacy.ArchCorrectness.ArithSimPathLoad
  (St : Set)
  (mem : St → ℕ → Maybe ℕ)          -- the arch's memory accessor (Memory = ℕ → Maybe ℕ)
  (def : Maybe ℕ → ℕ)
  (word : ℕ)                         -- the arch's word, in bytes
  where

-- D385: a leaf of the flat input (D375) is one read, at `flat-addr`. D390: the
-- empty path is the input ITSELF — a scalar block's input is register-resident,
-- and the emitted load is a register move (`movq %rdi` / `movl %ecx` / `mv t0`).
path-load-go : St → ℕ → InputPath → ℕ → ℕ
path-load-go s base []      k = base
path-load-go s base (x ∷ p) k = def (mem s (flat-addr word base (x ∷ p) k))

-- path-load-go depends on the state ONLY through its memory. Every `pl-inv`
-- non-spill case rides this with a `refl` memory-eq.
plg-mem-cong : ∀ A B base p k → mem A ≡ mem B → path-load-go A base p k ≡ path-load-go B base p k
plg-mem-cong A B base []      k meq = refl
plg-mem-cong A B base (x ∷ p) k meq = cong (λ m → def (m (flat-addr word base (x ∷ p) k))) meq
