{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Layer — one layer of a recursive type, on both
-- sides (plan 0.121 §3.5; plan 0.122: both are the Spec's).
--
-- A layer is held as a value of the type `⟦F⟧F C` and as its polynomial's
-- layer (`code`); the Spec converts by `toL`/`fromL`, the instance at no
-- variable along the instantiated functor, the Spec at the instance. A base
-- constant is the same as a value and as a layer's constant (`BR`), so both
-- conversions keep layers related.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Layer (Σ : Signature) where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

import Once.Spec.Type as ST
open ST using (Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; WFFun; wf-K; wf-Id; wf-⊕; wf-⊗)
import Once.Spec.Domain Σ as SD
open import Once.Spec.Core.Program Σ using (noVars)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ

------------------------------------------------------------------------
-- Base values
------------------------------------------------------------------------

val→br : ∀ {A A′} (g : GR A A′) {x y} → ValR g x y → BR g x y
val→br g-unit  r = tt
val→br g-void  r = tt
val→br g-int   r = r
val→br g-float r = r
val→br (g-* a b) {_ , _} {_ , _} (r , r′) = val→br a r , val→br b r′
val→br (g-+ a b) {inj₁ _} {inj₁ _} r = val→br a r
val→br (g-+ a b) {inj₂ _} {inj₂ _} r = val→br b r
val→br (g-+ a b) {inj₁ _} {inj₂ _} ()
val→br (g-+ a b) {inj₂ _} {inj₁ _} ()
val→br (g-⇒ _ _) r = tt
val→br (g-μ _)   r = tt
val→br (g-ν _)   r = tt

br→val : ∀ {X} (b : Base ST.∅ₖ X) {x y} → BR (g⟨⟩ noVars X) x y → ValR (g⟨⟩ noVars X) x y
br→val (b-var {i = ()} _)
br→val b-Unit  r = tt
br→val b-Void  r = tt
br→val b-Int   r = r
br→val b-Float r = r
br→val (b-* a b) {_ , _} {_ , _} (r , r′) = br→val a r , br→val b r′
br→val (b-+ a b) {inj₁ _} {inj₁ _} r = br→val a r
br→val (b-+ a b) {inj₂ _} {inj₂ _} r = br→val b r
br→val (b-+ a b) {inj₁ _} {inj₂ _} ()
br→val (b-+ a b) {inj₂ _} {inj₁ _} ()

------------------------------------------------------------------------
-- The layer of an instantiated functor
------------------------------------------------------------------------

module _ {m} (σ : ST.TySub m 0) where

  GR-⟦⟧σ : ∀ (F : ST.Fun m) {Xs X′} → GR (Xs ST.⟨ noVars ⟩) (X′ ST.⟨ σ ⟩)
         → GR (ST.⟦ F ST.⟨ σ ⟩F ⟧F Xs ST.⟨ noVars ⟩) (ST.⟦ F ⟧F X′ ST.⟨ σ ⟩)
  GR-⟦⟧σ (ST.K A)   gX = g⟨⟩ noVars (A ST.⟨ σ ⟩)
  GR-⟦⟧σ ST.Id      gX = gX
  GR-⟦⟧σ (F ST.⊕ H) gX = g-+ (GR-⟦⟧σ F gX) (GR-⟦⟧σ H gX)
  GR-⟦⟧σ (F ST.⊗ H) gX = g-* (GR-⟦⟧σ F gX) (GR-⟦⟧σ H gX)

  toL-R : ∀ (F : ST.Fun m) {Xs X′} (gX : GR (Xs ST.⟨ noVars ⟩) (X′ ST.⟨ σ ⟩)) {x x′}
        → ValR (GR-⟦⟧σ F gX) x x′
        → LayerR (gf⟨⟩ noVars (F ST.⟨ σ ⟩F)) (ValR gX) (SD.toL noVars (F ST.⟨ σ ⟩F) Xs x) (SD.toL σ F X′ x′)
  toL-R (ST.K A)   gX r = val→br (g⟨⟩ noVars (A ST.⟨ σ ⟩)) r
  toL-R ST.Id      gX r = r
  toL-R (F ST.⊕ H) gX {inj₁ _} {inj₁ _} r = toL-R F gX r
  toL-R (F ST.⊕ H) gX {inj₂ _} {inj₂ _} r = toL-R H gX r
  toL-R (F ST.⊕ H) gX {inj₁ _} {inj₂ _} ()
  toL-R (F ST.⊕ H) gX {inj₂ _} {inj₁ _} ()
  toL-R (F ST.⊗ H) gX {_ , _} {_ , _} (r , r′) = toL-R F gX r , toL-R H gX r′

  fromL-R : ∀ (F : ST.Fun m) (wf : WFFun ST.∅ₖ (F ST.⟨ σ ⟩F)) {Xs X′} (gX : GR (Xs ST.⟨ noVars ⟩) (X′ ST.⟨ σ ⟩)) {l l′}
          → LayerR (gf⟨⟩ noVars (F ST.⟨ σ ⟩F)) (ValR gX) l l′
          → ValR (GR-⟦⟧σ F gX) (SD.fromL noVars (F ST.⟨ σ ⟩F) Xs l) (SD.fromL σ F X′ l′)
  fromL-R (ST.K A)   (wf-K b) gX r = br→val b r
  fromL-R ST.Id      wf-Id    gX r = r
  fromL-R (F ST.⊕ H) (wf-⊕ wf wh) gX {inj₁ _} {inj₁ _} r = fromL-R F wf gX r
  fromL-R (F ST.⊕ H) (wf-⊕ wf wh) gX {inj₂ _} {inj₂ _} r = fromL-R H wh gX r
  fromL-R (F ST.⊕ H) (wf-⊕ wf wh) gX {inj₁ _} {inj₂ _} ()
  fromL-R (F ST.⊕ H) (wf-⊕ wf wh) gX {inj₂ _} {inj₁ _} ()
  fromL-R (F ST.⊗ H) (wf-⊗ wf wh) gX {_ , _} {_ , _} (r , r′) = fromL-R F wf gX r , fromL-R H wh gX r′
