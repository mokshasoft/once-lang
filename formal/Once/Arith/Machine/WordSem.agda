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
open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S; InputPath; project; projectF)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Float.Dyadic using (FloatFormat)
open import Once.Float.Decimal using (round)
import Once.Float.Arith as FA

-- PLAN 0.75 F4: the FORMAT joins the width. Both are target facts and both
-- arrive from the architecture — `bits` narrows an `Int` leaf, `F` rounds a
-- float one, and neither is hard-coded here. A float result IS a bit pattern
-- (D113), and a `Word` IS `Carrier` (`ℕ`), so the two kinds share a result
-- type and `eval-arith-W` stays a single function.
module Sem (bits : ℕ) (F : FloatFormat) where
  open W.Width bits using (Word; fromℤ; toℤ; _⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_)

  -- | Mirrors `IR.eval-arith` op-for-op with `Once.Word`'s modular
  -- operations, applying `fromℤ` at the leaves. The target of the
  -- abstract machine's Validity proof (`Once.Arith.Machine.Compile`).
  -- The `Int` leaves narrow with `fromℤ`; the float ones are ALREADY patterns
  -- and need no conversion, which is D113 showing through: there is no exact
  -- value to narrow from.
  eval-arith-W : ∀ {sh n} → MArithIR sh n → ⟦ sh ⟧S → Word
  eval-arith-W {sh} (alit z)   _   = fromℤ z
  eval-arith-W {sh} (aflit d)  _   = round F d
  eval-arith-W {sh} {NInt}   (ainput p) inp with project sh p inp
  ... | just z   = fromℤ z
  ... | nothing  = fromℤ (+ 0)
  eval-arith-W {sh} {NFloat} (ainput p) inp with projectF sh p inp
  ... | just w   = w
  ... | nothing  = 0
  -- The op DISPATCHES ON THE KIND. `Once.Word`'s modular ops for `Int`,
  -- `Once.Float.Arith`'s for `Float` — and both are DEFINITIONS reading the
  -- target out of a parameter, which is D054's shape and D113's extension of
  -- it to the second type.
  eval-arith-W {n = NInt}   (aadd a b) inp = eval-arith-W a inp ⊕ eval-arith-W b inp
  eval-arith-W {n = NFloat} (aadd a b) inp = FA.fadd F (eval-arith-W a inp) (eval-arith-W b inp)
  eval-arith-W {n = NInt}   (asub a b) inp = eval-arith-W a inp ⊖ eval-arith-W b inp
  eval-arith-W {n = NFloat} (asub a b) inp = FA.fsub F (eval-arith-W a inp) (eval-arith-W b inp)
  eval-arith-W {n = NInt}   (amul a b) inp = eval-arith-W a inp ⊗ eval-arith-W b inp
  eval-arith-W {n = NFloat} (amul a b) inp = FA.fmul F (eval-arith-W a inp) (eval-arith-W b inp)
  eval-arith-W {n = NInt}   (adiv a b) inp = eval-arith-W a inp /ˢ eval-arith-W b inp
  -- The float quotient is `FA.fdiv` — correctly rounded via the sticky bit, and
  -- TOTAL like its integer sibling (D055): `x/0` is a signed infinity, `0/0`
  -- the canonical NaN. Neither traps, so neither needs a guard.
  eval-arith-W {n = NFloat} (adiv a b) inp = FA.fdiv F (eval-arith-W a inp) (eval-arith-W b inp)
  eval-arith-W (amod a b) inp = eval-arith-W a inp %ˢ eval-arith-W b inp
  eval-arith-W {n = NInt}   (aneg a)   inp = ⊝ eval-arith-W a inp
  -- Float negation is a SIGN-BIT FLIP, not `0 − x`: the latter turns `−0` into
  -- `+0` and canonicalises a NaN, neither of which negation may do.
  eval-arith-W {n = NFloat} (aneg a)   inp = FA.fneg F (eval-arith-W a inp)
  -- D125's widening reads the operand at its SIGNED value before rounding.
  eval-arith-W (ai2f a) inp = FA.i2f F (toℤ (eval-arith-W a inp))
