{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.LayerTy — `layerᶜ F` maps at the type
-- `⟦ F ⟨ shiftᵗ ⟩F ⟧F (var zero)`; at `X` that type is `⟦ F ⟧F X`.
------------------------------------------------------------------------

module Once.Metatheory.Laws.LayerTy where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Type using (Ty; Fun; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_;
                                  ⟦_⟧F; _⟨_⟩; _⟨_⟩F; at₀; shiftᵗ)

-- Making room for a variable, then filling it: nothing changed.
mutual
  shift-at₀ : ∀ {m} (C : Ty m) (X : Ty m) → C ⟨ shiftᵗ ⟩ ⟨ at₀ X ⟩ ≡ C
  shift-at₀ (var i)        X = refl
  shift-at₀ Unit           X = refl
  shift-at₀ Void           X = refl
  shift-at₀ Int            X = refl
  shift-at₀ Float          X = refl
  shift-at₀ (A * B)        X = cong₂ _*_ (shift-at₀ A X) (shift-at₀ B X)
  shift-at₀ (A + B)        X = cong₂ _+_ (shift-at₀ A X) (shift-at₀ B X)
  shift-at₀ (A ⇒[ k ] B)   X = cong₂ (λ P Q → P ⇒[ k ] Q) (shift-at₀ A X) (shift-at₀ B X)
  shift-at₀ (μ F)          X = cong μ (shift-at₀F F X)
  shift-at₀ (ν F f)        X = cong (λ G → ν G f) (shift-at₀F F X)

  shift-at₀F : ∀ {m} (F : Fun m) (X : Ty m) → F ⟨ shiftᵗ ⟩F ⟨ at₀ X ⟩F ≡ F
  shift-at₀F (K C)   X = cong K (shift-at₀ C X)
  shift-at₀F Id      X = refl
  shift-at₀F (F ⊕ G) X = cong₂ _⊕_ (shift-at₀F F X) (shift-at₀F G X)
  shift-at₀F (F ⊗ G) X = cong₂ _⊗_ (shift-at₀F F X) (shift-at₀F G X)

-- The type `layerᶜ F` maps at.
layerT : ∀ {m} → Fun m → Ty (suc m)
layerT F = ⟦ F ⟨ shiftᵗ ⟩F ⟧F (var zero)

layerTy : ∀ {m} (F : Fun m) (X : Ty m) → layerT F ⟨ at₀ X ⟩ ≡ ⟦ F ⟧F X
layerTy (K C)   X = shift-at₀ C X
layerTy Id      X = refl
layerTy (F ⊕ G) X = cong₂ _+_ (layerTy F X) (layerTy G X)
layerTy (F ⊗ G) X = cong₂ _*_ (layerTy F X) (layerTy G X)
