-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.WordSem
--
-- The machine-level (modular `Word`) denotation of an arith tree,
-- parameterised by the word width `bits` (D054). The ARCHITECTURE
-- instantiation supplies `bits` (x86-64 / riscv64 → 64); no width is
-- hard-coded here. Extracted from `Once.Arith.Machine.IR` so that the
-- IR (`MArithIR`/`ArithBlock`) stays width-AGNOSTIC.
--
-- `bits` lives on a nested module (`Sem`) because a top-level Agda
-- module can't take a `ℕ` parameter — same idiom as `Once.Word.Width`.
------------------------------------------------------------------------

module Once.Arith.Machine.WordSem where

open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.Maybe using (just; nothing)
import Once.Word as W
open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S; InputPath; project)
open import Once.Arith.Machine.IR using (MArithIR; alit; ainput; aadd; asub; amul; adiv; amod; aneg)

module Sem (bits : ℕ) where
  open W.Width bits using (Word; fromℤ; _⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_)

  -- | Mirrors `IR.eval-arith` op-for-op with `Once.Word`'s modular
  -- operations, applying `fromℤ` at the leaves. The target of the
  -- abstract machine's Validity proof (`Once.Arith.Machine.Compile`).
  eval-arith-W : ∀ {sh} → MArithIR sh → ⟦ sh ⟧S → Word
  eval-arith-W {sh} (alit z)   _   = fromℤ z
  eval-arith-W {sh} (ainput p) inp with project sh p inp
  ... | just z   = fromℤ z
  ... | nothing  = fromℤ (+ 0)
  eval-arith-W (aadd a b) inp = eval-arith-W a inp ⊕ eval-arith-W b inp
  eval-arith-W (asub a b) inp = eval-arith-W a inp ⊖ eval-arith-W b inp
  eval-arith-W (amul a b) inp = eval-arith-W a inp ⊗ eval-arith-W b inp
  eval-arith-W (adiv a b) inp = eval-arith-W a inp /ˢ eval-arith-W b inp
  eval-arith-W (amod a b) inp = eval-arith-W a inp %ˢ eval-arith-W b inp
  eval-arith-W (aneg a)   inp = ⊝ eval-arith-W a inp
