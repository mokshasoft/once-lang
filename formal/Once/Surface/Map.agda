{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Map — a structure map, as the generator table's entry
-- (plan 0.146 B1.7, D459).
--
-- The elaborated expression (`Surface.Syntax.Expr`) names a structure map by
-- its entry in the table (`Spec.Surface.Generators.Morphism`, without the
-- Spec's term, and `toFloat`), not by its IR: its IR is a function of the
-- entry (`TypeCheck.Table.mapIR`), and the linear core's bridge translates
-- each entry (`LinCore.FromExpr`).
------------------------------------------------------------------------

module Once.Surface.Map where

open import Once.Spec.Grade using (Purity; Finite; fin; Many; mk-kind)
open import Once.Spec.Type using (Ty; KCtx; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun)
open import Once.Spec.Core.Derived using (𝕋)

data Map {m} : Ty m → Ty m → Set where
  mp-id       : ∀ {A} → Map A A
  mp-fst      : ∀ {A B} → Map (A * B) A
  mp-snd      : ∀ {A B} → Map (A * B) B
  mp-terminal : ∀ {A} → Map A Unit
  mp-inl      : ∀ {A B} → Map A (A + B)
  mp-inr      : ∀ {A B} → Map B (A + B)
  mp-initial  : ∀ {B} → Map Void B
  -- `apply` and `Out`: running them gives `𝕋` of their grade
  mp-apply    : ∀ A B ρ → Map ((A ⇒[ mk-kind Many ρ ] B) * A) (𝕋 ρ B)
  mp-In       : ∀ {Δ : KCtx m} F → WFFun Δ F → Map (⟦ F ⟧F (μ F)) (μ F)
  mp-Out      : ∀ {Δ : KCtx m} F f → WFFun Δ F → Map (ν F f) (𝕋 (fin f) (⟦ F ⟧F (ν F f)))
  -- `Int` → `Float`, correctly rounded (D408)
  mp-toFloat  : Map Int Float
