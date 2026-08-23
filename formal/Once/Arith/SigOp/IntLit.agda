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
import Once.Word as OnceWord
open import Once.Target.Arch using (TargetNum; int-bits)

------------------------------------------------------------------------
-- The literal-family builder
------------------------------------------------------------------------

-- | Name for a literal integer SigOp: `"lit.int.<n>"`.
lit-int-name : ℤ → String
lit-int-name n = "lit.int." ++ showℤ n

-- | SigOpInfo for the constant-`n` morphism Unit → Int.
--
-- PLAN 0.74 J5 — THIS CARRIED THE `absℤ` BUG AND WAS MISSED. Its machine
-- semantics was `λ _ → ∣ n ∣`, the ABSOLUTE VALUE, so `-5` meant 5. That is
-- the same defect the negative-literal fix (2026-08-20) removed from five
-- other sites; this one survived because it is currently UNREFERENCED —
-- `Surface/Elaborate.agda` imports the name and never uses it, and literals
-- go through the IR's `const` instead.
--
-- Fixed rather than left alone, for the reason the retired-constructor trap
-- teaches: dead code with a refuted semantics is the code that gets revived.
-- It now agrees with `Denotation/Meaning`'s `⟦ t-int n ⟧ᵢ` — `fromℤ` at the
-- TARGET's width, two's complement, no absolute value.
lit-int-info : ℤ → SigOpInfo Unit Int
lit-int-info n = mk-info
  (bare (lit-int-name n))
  (λ tn _ → OnceWord.Width.fromℤ (int-bits tn) n)
  Pure           -- effect: constants are observably pure
  base-Unit (con-base base-Int)
