-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Numeric — the typed surface terms of the numeric rules
-- (plan 0.150 N10).
--
-- The Spec's `s-binop` means `prim (num h o) (pair t₁ t₂)`, its `s-toFloat`
-- the conversion. These build the surface terms, once: the checker
-- (`TypeCheck.Elaborate`) and the realization of a Spec derivation
-- (`Denotation.RealizeS`) both call them, so the two agree by definition.
------------------------------------------------------------------------

module Once.Surface.Numeric where

open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Once.Spec.Type using (Int; Float)
open import Once.Spec.Context using (Ctx; Usage; _+ᵘ_)
open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ; Has; Rounded; Sym; symCod; float-rounded)
open import Once.Spec.Surface.Operator using (BinOp; BinSym; binSym; _∶_∶_)
open BinSym
open import Once.Surface.Syntax using (Expr; num; pair)
open import Once.IR using (IR; SigOp)
open import Once.IRTy using (⌊_⌋)
open import Once.Arith.SigOp.Builders using (i2f-info)
open import Once.TypeCheck.NumTable using (binDom)

-- | `toFloat` (D408), lowered: the conversion's primitive.
toFloatIR : IR (⌊ Int {0} ⌋) (⌊ Float {0} ⌋)
toFloatIR = SigOp i2f-info

-- | `e₁ op e₂` at one number type `a` that has the operator's theory.
numBin : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} op (a : NumTy) → Has a (theory (binSym op))
       → Expr Γ Ψ₁ ⌜ a ⌝ⁿ → Expr Γ Ψ₂ ⌜ a ⌝ⁿ → Expr Γ (Ψ₁ +ᵘ Ψ₂) (symCod a (shape (binSym op)))
numBin {Γ = Γ} {Ψ₁} {Ψ₂} op a h e₁ e₂ =
  num h (symbol (binSym op)) (subst (Expr Γ (Ψ₁ +ᵘ Ψ₂)) (sym (binDom op a)) (pair e₁ e₂))
