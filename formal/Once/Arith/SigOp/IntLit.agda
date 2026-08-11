-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.IntLit
--
-- Integer-literal family: for each integer `n : ℤ`, produces a
-- `SigOpInfo Unit Int` with:
--   - name  = "lit.int.<n>"
--   - semI  = λ _ → n              (frontend, ℤ)
--   - semM  = λ _ → |n|            (machine, ℕ; uses absolute value
--                                   for now — negative literals will
--                                   be handled properly in 0.2.4.2)
--
-- Integer literals are **compiler-intrinsic**, not user-imported.
-- Writing `42` in Once source produces a `SigOp (lit-int-info 42)`
-- node; no `import Math.Int` required.
--
-- This module lives under `formal/Once/Arith/` (the ArithCompiler
-- subtree), not under `Strata/Interpretations/`, because literal
-- handling is part of the language's base arithmetic machinery
-- rather than a user-selectable interpretation.
------------------------------------------------------------------------

module Once.Arith.SigOp.IntLit where

open import Data.Integer using (ℤ; ∣_∣)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)

open import Once.Type using (Type; Unit; Int)
open import Once.SigOp.Info using (SigOpInfo; mk-info; Pure)
open import Once.Functor.Translate using (base-Unit; base-Int; con-base)
open import Once.CanonicalName using (bare)

------------------------------------------------------------------------
-- The literal-family builder
------------------------------------------------------------------------

-- | Name for a literal integer SigOp: `"lit.int.<n>"`.
lit-int-name : ℤ → String
lit-int-name n = "lit.int." ++ showℤ n

-- | SigOpInfo for the constant-`n` morphism Unit → Int.
--
-- Both semantic layers ignore the input (it's Unit) and return
-- the integer constant.  At the frontend (ℤ) layer we return `n`
-- directly; at the machine (ℕ) layer we return |n|.  Negative
-- integer literals are tracked properly once arithmetic migrates
-- to this framework in plan 0.2.4.2.
lit-int-info : ℤ → SigOpInfo Unit Int
lit-int-info n = mk-info
  (bare (lit-int-name n))
  (λ _ → ∣ n ∣)  -- semM : ⊤ → ℕ (the value; ℕ/Word)
  Pure           -- effect: constants are observably pure
  base-Unit (con-base base-Int)
