-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Show — THE IR AS TEXT, for the CLI's `elaborate` and `optimize`
-- stages (plan 0.39).
--
-- One line per term, types left out: `g . f` composes, `<f, g>` pairs,
-- `[f, g]` is `case`, a scheme shows its algebra in parentheses. A SigOp and
-- a call show their canonical names, a constant its value. Read only by
-- people and by the optimizer tests; nothing is proved about it.
------------------------------------------------------------------------

module Once.IR.Show where

open import Data.Integer using (ℤ)
import Data.Integer.Show as ℤS
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import Once.IR
open import Once.IRTy using (fits-int; fits-float)
open import Once.Name using (showCanonical)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Spec.Float.Decimal using (Decimal)

private
  showDecimal : Decimal → String
  showDecimal d = ℤS.show (Decimal.sig d) ++ "e-" ++ showℕ (Decimal.exp10 d)

-- | A term, compositions in parentheses unless at the top.
showIR  : ∀ {A B} → IR A B → String
-- | A term as an operand of `.`: a composition in parentheses.
showArg : ∀ {A B} → IR A B → String

showIR id              = "id"
showIR (g ∘ f)         = showArg g ++ " . " ++ showArg f
showIR ⟨ f , g ⟩       = "<" ++ showIR f ++ ", " ++ showIR g ++ ">"
showIR fst             = "fst"
showIR snd             = "snd"
showIR inl             = "inl"
showIR inr             = "inr"
showIR (case f g)      = "[" ++ showIR f ++ ", " ++ showIR g ++ "]"
showIR terminal        = "terminal"
showIR initial         = "initial"
showIR (curry f)       = "curry(" ++ showIR f ++ ")"
showIR apply           = "apply"
showIR (In _)          = "In"
showIR (out-μ _)       = "out-mu"
showIR (Cata _ alg)    = "cata(" ++ showIR alg ++ ")"
showIR (Out _)         = "Out"
showIR (in-ν _)        = "in-nu"
showIR (Ana _ c)       = "ana(" ++ showIR c ++ ")"
showIR (Iter b)        = "iter(" ++ showIR b ++ ")"
showIR (const fits-int v)   = ℤS.show v
showIR (const fits-float v) = showDecimal v
showIR (SigOp si)      = "sigop " ++ showCanonical (SigOpInfo.name si)
showIR (Call f)        = "call " ++ showCanonical f

showArg (g ∘ f) = "(" ++ showIR (g ∘ f) ++ ")"
{-# CATCHALL #-}
showArg ir      = showIR ir
