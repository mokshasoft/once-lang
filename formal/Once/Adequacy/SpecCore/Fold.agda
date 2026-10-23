{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Fold — the fold means related computations (plan
-- 0.121 §3.5; plan 0.122: both sides are the Spec's `foldM`).
--
-- At each node, the children folded left to right (`layerM`), then the
-- algebra. Related algebras on related data run related computations: by
-- induction on the related data (`fold-R`), layer by layer (`layer-R`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Fold (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Spec.Polynomial as SPoly
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ

-- A value returned at a grade.
return-R : ∀ π {X Y : Set} {R : X → Y → Set} {x y} → R x y → MR (pr π) R (SE.return π x) (SE.return π y)
return-R LG.pure r = r
return-R LG.act  r = ret r
return-R LG.eff  r = return∞-R r

module _ {F₀ F₀′ : ST.Fun 0} (f₀ : GF F₀ F₀′) (π : LG.Purity) {X X′ : Set} {R : X → X′ → Set}
         {a  : SPoly.⟦ SD.code F₀ ⟧SF X → SE.M π X}
         {a′ : SPoly.⟦ SD.code F₀′ ⟧SF X′ → SE.M π X′}
         (ralg : ∀ {l l′} → LayerR f₀ R l l′ → MR (pr π) R (a l) (a′ l′)) where

  fold-R  : ∀ {v w} → μR f₀ v w → MR (pr π) R (SD.foldM π (SD.code F₀) a v) (SD.foldM π (SD.code F₀′) a′ w)
  layer-R : ∀ {H H′} (h : GF H H′) {x y}
          → LayerR h (μR f₀) x y
          → MR (pr π) (LayerR h R) (SD.layerM π (SD.code F₀) (SD.code H) a x) (SD.layerM π (SD.code F₀′) (SD.code H′) a′ y)

  fold-R (inR l) = bind-R (pr π) (layer-R f₀ l) ralg

  layer-R (g-K b)   r = return-R π r
  layer-R g-Id      r = fold-R r
  layer-R (g-⊕ h k) {inj₁ _} {inj₁ _} r = fmap-R (pr π) (layer-R h r) (λ x → x)
  layer-R (g-⊕ h k) {inj₂ _} {inj₂ _} r = fmap-R (pr π) (layer-R k r) (λ x → x)
  layer-R (g-⊕ h k) {inj₁ _} {inj₂ _} ()
  layer-R (g-⊕ h k) {inj₂ _} {inj₁ _} ()
  layer-R (g-⊗ h k) {_ , _} {_ , _} (r , r′) =
    bind-R (pr π) (layer-R h r) (λ u → bind-R (pr π) (layer-R k r′) (λ v → return-R π (u , v)))
