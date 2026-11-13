-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Numeric — the typed surface terms of the numeric rules
-- (plan 0.150 N10).
--
-- The Spec's `s-binop` means `prim (num h o) (pair t₁ t₂)`, its
-- `s-binop-mixed` the same at `Float` with the `Int` operand widened. These
-- build the surface terms of the same shape, once: the checker
-- (`TypeCheck.Elaborate`) and the realization of a Spec derivation
-- (`Denotation.RealizeS`) both call them, so the two agree by definition.
------------------------------------------------------------------------

module Once.Surface.Numeric where

open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Once.Spec.Type using (Float)
open import Once.Spec.Context using (Ctx; Usage; _+ᵘ_)
open import Once.Spec.Theory using (NumTy; int; float; ⌜_⌝ⁿ; Has; Rounded; Sym; symCod; float-rounded)
open import Once.Spec.Surface.Operator using (BinOp; BinSym; binSym; _∶_∶_)
open BinSym
open import Once.Surface.Syntax using (Expr; num; pair; i2f)
open import Once.TypeCheck.NumTable using (binDom; mixedDom)

-- | An operand, widened to `Float` (D125's `i2f` node).
widen : ∀ {m n} {Γ : Ctx m n} {Ψ} (a : NumTy) → Expr Γ Ψ ⌜ a ⌝ⁿ → Expr Γ Ψ Float
widen int   e = i2f e
widen float e = e

-- | `e₁ op e₂` at one number type `a` that has the operator's theory.
numBin : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} op (a : NumTy) → Has a (theory (binSym op))
       → Expr Γ Ψ₁ ⌜ a ⌝ⁿ → Expr Γ Ψ₂ ⌜ a ⌝ⁿ → Expr Γ (Ψ₁ +ᵘ Ψ₂) (symCod a (shape (binSym op)))
numBin {Γ = Γ} {Ψ₁} {Ψ₂} op a h e₁ e₂ =
  num h (symbol (binSym op)) (subst (Expr Γ (Ψ₁ +ᵘ Ψ₂)) (sym (binDom op a)) (pair e₁ e₂))

-- | A dotted operator on operands of the two number types, widened.
numMixed : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} op {k} {o : Sym Rounded k} → binSym op ≡ (Rounded ∶ k ∶ o)
         → (a₁ a₂ : NumTy) → Expr Γ Ψ₁ ⌜ a₁ ⌝ⁿ → Expr Γ Ψ₂ ⌜ a₂ ⌝ⁿ → Expr Γ (Ψ₁ +ᵘ Ψ₂) (symCod float k)
numMixed {Γ = Γ} {Ψ₁} {Ψ₂} op {o = o} eq a₁ a₂ e₁ e₂ =
  num float-rounded o (subst (Expr Γ (Ψ₁ +ᵘ Ψ₂)) (sym (mixedDom eq)) (pair (widen a₁ e₁) (widen a₂ e₂)))
