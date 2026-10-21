{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Unfold — the unfold means related streams (plan
-- 0.121 §3.5).
--
-- Both sides unfold a coalgebra the same way: forcing a layer runs the
-- coalgebra (a value at `pure`, a block at `act`) and its children become
-- the unfold of the next seeds. Related coalgebras on related seeds give
-- related streams: a copattern step over the (inductive) block and layer.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Unfold (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Grade as SG
import Once.Internal.GradedOps as LOps
import Once.Internal.Stream as LSt
import Once.Internal.Trace as LTr
import Once.Internal.Polynomial as LPoly
import Once.Spec.Polynomial as SPoly
open import Once.Internal.FunctorMeaning using (translateF)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open νpR
open νdR

module _ {F₀ F₀′} (f₀ : GF F₀ F₀′) {X X′ : Set} {RA : X → X′ → Set} where

  private
    H = translateF Carrier Carrier F₀
    G = SD.code F₀′

  -- at `pure`
  module _ {c : X → LPoly.⟦ H ⟧SF X} {c′ : X′ → SPoly.⟦ G ⟧SF X′}
           (h : ∀ {x x′} → RA x x′ → LayerR f₀ RA (c x) (c′ x′)) where

    anaP-R : ∀ {x x′} → RA x x′ → νpR f₀ (LOps.anaᵖ H c x) (SE.anaP G c′ x′)
    mapP-R : ∀ {F F′} (f : GF F F′) {l l′} → LayerR f RA l l′
           → LayerR f (νpR f₀) (LOps.mapAnaᵖ H (translateF Carrier Carrier F) c l) (SE.mapP G (SD.code F′) c′ l′)
    forceᵖR (anaP-R r) = mapP-R f₀ (h r)
    mapP-R (g-K a)   r = r
    mapP-R g-Id      r = anaP-R r
    mapP-R (g-⊕ f g) {inj₁ _} {inj₁ _} r = mapP-R f r
    mapP-R (g-⊕ f g) {inj₂ _} {inj₂ _} r = mapP-R g r
    mapP-R (g-⊕ f g) {inj₁ _} {inj₂ _} ()
    mapP-R (g-⊕ f g) {inj₂ _} {inj₁ _} ()
    mapP-R (g-⊗ f g) {_ , _} {_ , _} (r , r′) = mapP-R f r , mapP-R g r′

  -- at `act`
  module _ {c : X → LTr.T (LPoly.⟦ H ⟧SF X)} {c′ : X′ → SE.T (SPoly.⟦ G ⟧SF X′)}
           (h : ∀ {x x′} → RA x x′ → TR (LayerR f₀ RA) (c x) (c′ x′)) where

    anaA-R : ∀ {x x′} → RA x x′ → νdR f₀ (LSt.anaᵈ H c x) (SE.anaA G c′ x′)
    treeA-R : ∀ {t t′} → TR (LayerR f₀ RA) t t′ → TR (LayerR f₀ (νdR f₀)) (LSt.anaTree H c t) (SE.treeA G c′ t′)
    mapA-R : ∀ {F F′} (f : GF F F′) {l l′} → LayerR f RA l l′
           → LayerR f (νdR f₀) (LSt.mapAnaᵈ H (translateF Carrier Carrier F) c l) (SE.mapA G (SD.code F′) c′ l′)
    forceᵈR (anaA-R r) = treeA-R (h r)
    treeA-R (ret r)      = ret (mapA-R f₀ r)
    treeA-R (call o a k) = call o a (λ b → treeA-R (k b))
    treeA-R (halt x a)   = halt x a
    mapA-R (g-K a)   r = r
    mapA-R g-Id      r = anaA-R r
    mapA-R (g-⊕ f g) {inj₁ _} {inj₁ _} r = mapA-R f r
    mapA-R (g-⊕ f g) {inj₂ _} {inj₂ _} r = mapA-R g r
    mapA-R (g-⊕ f g) {inj₁ _} {inj₂ _} ()
    mapA-R (g-⊕ f g) {inj₂ _} {inj₁ _} ()
    mapA-R (g-⊗ f g) {_ , _} {_ , _} (r , r′) = mapA-R f r , mapA-R g r′
