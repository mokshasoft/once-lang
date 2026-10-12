-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Witness.NoSelfRef — no definition can name itself or a
-- later one (`Spec.Metatheory.Totality`, D241, D311).
--
-- The first definition is typed in the EMPTY scope (`Spec.Module.ModTele`), so
-- its body's `f` must be typed by a variable rule, and every one of them needs
-- `f` in the scope: as a local, an interpretation operation, or an earlier
-- telescope definition.
------------------------------------------------------------------------

module Once.Metatheory.Witness.NoSelfRef where

open import Relation.Nullary using (¬_)
open import Data.List using ([]; _∷_)
open import Once.Spec.Syntax using (RVar)
open import Once.Spec.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; module _⊢ᵢ_∶_⨾_; module _⊢ᶜ_∶_⨾_)
open _⊢ᵢ_∶_⨾_
open _⊢ᶜ_∶_⨾_
open import Once.Spec.Module using (ModTele; mono; ffi; ctxOf; emptyScope)
open import Once.Spec.Totality using (selfRef; forwardRef; defF)

-- Nothing is in the empty scope.
no-var-i : ∀ {T Ψ} → ¬ (ctxOf emptyScope ⊢ᵢ RVar "f" ∶ T ⨾ Ψ)
no-var-i (t-var-local ())
no-var-i (t-var-import _ _ () _)
no-var-i (t-var-poly-instantiate-infer _ _ () _ _)

no-var : ∀ {T Ψ} → ¬ (ctxOf emptyScope ⊢ᶜ RVar "f" ∶ T ⨾ Ψ)
no-var (t-sub d _)                          = no-var-i d
no-var (t-var-poly-instantiate _ _ () _ _)

no-self-reference : ¬ ModTele emptyScope (selfRef ∷ [])
no-self-reference (mono _ _ _ d _) = no-var d
no-self-reference (ffi () _ _ _ _ _)

no-forward-reference : ¬ ModTele emptyScope (forwardRef ∷ defF ∷ [])
no-forward-reference (mono _ _ _ d _) = no-var d
no-forward-reference (ffi () _ _ _ _ _)
