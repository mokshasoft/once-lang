-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A NORMAL TYPE KEEPS ITS SHAPE under conversion.
--                      (PLAN-BIDI §3a, step C2)
--
-- ★ WHAT IT IS FOR.  The checker reads a function's type off its NORMAL
--   form (`CheckA.viewΠ`); when that form is not a `Π`, the "no" must
--   refute every typing at a `Π`.  It does: a normal type convertible to
--   `Π A B` IS literally a `Π` (likewise `Σ'`).
--
-- ★ HOW.  Church–Rosser gives a common reduct; a normal type reduces only
--   to itself (`nf-stuck`); a reduct of a `Π` is a `Π` (`Π-reduct`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.NormalShape where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; Σ; _,_; ⊥-elim )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.Injectivity
  using ( church-rosserᵀ; Π-reduct; mkΠRed; Σ-reduct; mkΣRed )
open import DirectedHoTT.Metatheory.NormTy using ( IsNormalᵀ )

private
  variable
    Γ : Cx

-- a normal type reduces only to itself
nf-stuck : {N C : RTy Γ} → IsNormalᵀ N → N ⟶ᵀ* C → N ≡ C
nf-stuck n doneᵀ          = refl
nf-stuck n (stepᵀ r rest) = ⊥-elim (n r)

-- ★ a normal type convertible to a `Π` is a `Π`
nf-Π : {N A : RTy Γ} {B : RTy (Γ ∙)} → IsNormalᵀ N → N ≅ᵀ Π A B →
       Σ (RTy Γ) (λ F → Σ (RTy (Γ ∙)) (λ G → N ≡ Π F G))
nf-Π n c with church-rosserᵀ c
... | C , (r₁ , r₂) with Π-reduct r₂
...   | mkΠRed F G eqC _ _ = F , (G , trans (nf-stuck n r₁) eqC)

-- …a `Σ'`
nf-Σ : {N A : RTy Γ} {B : RTy (Γ ∙)} → IsNormalᵀ N → N ≅ᵀ Σ' A B →
       Σ (RTy Γ) (λ F → Σ (RTy (Γ ∙)) (λ G → N ≡ Σ' F G))
nf-Σ n c with church-rosserᵀ c
... | C , (r₁ , r₂) with Σ-reduct r₂
...   | mkΣRed F G eqC _ _ = F , (G , trans (nf-stuck n r₁) eqC)
