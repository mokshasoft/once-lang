{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Fold — the fold means related computations (plan
-- 0.121 §3.5).
--
-- The compiler folds by `cataS` — at each node, the children's folds as
-- computations, sequenced left to right (`seqM`), then the algebra — and the
-- Spec by `foldM` — at each node, the children folded left to right
-- (`layerM`), then the algebra. Both run the same computations in the same
-- order: by induction on the related data (`fold-R`), layer by layer
-- (`layer-R`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
import Once.Spec.Grade as LG
import Once.Internal.Type.Sub as LS
import Once.Spec.Sub as LS
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Spec.Type as ST
open import Once.Adequacy.SpecCore.Index using (gr; gf)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Fold (Σ : Signature)
  {m} (σ : ST.TySub m 0)
  (F : ST.Fun m) (A : ST.Ty m) (wf : LW.WellFormedF (F ST.⟨ σ ⟩F))
  {π} (u : LG.pure Once.Spec.Grade.⊑π π) where

open import Data.Product using (_×_; _,_)
import Data.Sum as SPolyS
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as V
import Once.Internal.Graded as LGr
import Once.Internal.GradedOps as LOps
import Once.Internal.Polynomial as LPoly
open import Once.Internal.FunctorMeaning using (translateF)
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Spec.Polynomial as SPoly
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Type as LT
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Layer Σ

private
  Fg = F ST.⟨ σ ⟩F
  Ag = A ST.⟨ σ ⟩
  G  = SD.code Fg
  f₀ = gf Fg
  gA = gr Ag

-- One layer of computations, sequenced on both sides: the injections and the
-- pairing, at each grade a fold may have.
private
  module _ {X Y : Set} where
    inl-R : ∀ {π₀} (u₀ : LG.pure Once.Spec.Grade.⊑π π₀) {F₁ F₂ : LT.Fun 0} {Y₂ : Set} {R : V.⟦ F₁ ⟧F X → Y → Set}
            {R′ : V.⟦ F₁ LT.⊕ F₂ ⟧F X → Y SPolyS.⊎ Y₂ → Set} {x y}
          → MR (pr π₀) R (LOps.seqM u₀ F₁ x) y → (∀ {a b} → R a b → R′ (inj₁ a) (inj₁ b))
          → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊕ F₂) (inj₁ x)) (SE.fmap π₀ inj₁ y)
    inl-R Once.Spec.Grade.⊑-pure r k = k r
    inl-R Once.Spec.Grade.⊑-pa   r k = fmap-R pr-act r k
    inl-R Once.Spec.Grade.⊑-pe   r k = fmap-R pr-eff r k

    inr-R : ∀ {π₀} (u₀ : LG.pure Once.Spec.Grade.⊑π π₀) {F₁ F₂ : LT.Fun 0} {Y₁ : Set} {R : V.⟦ F₂ ⟧F X → Y → Set}
            {R′ : V.⟦ F₁ LT.⊕ F₂ ⟧F X → Y₁ SPolyS.⊎ Y → Set} {x y}
          → MR (pr π₀) R (LOps.seqM u₀ F₂ x) y → (∀ {a b} → R a b → R′ (inj₂ a) (inj₂ b))
          → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊕ F₂) (inj₂ x)) (SE.fmap π₀ inj₂ y)
    inr-R Once.Spec.Grade.⊑-pure r k = k r
    inr-R Once.Spec.Grade.⊑-pa   r k = fmap-R pr-act r k
    inr-R Once.Spec.Grade.⊑-pe   r k = fmap-R pr-eff r k

  pair-R : ∀ {π₀} (u₀ : LG.pure Once.Spec.Grade.⊑π π₀) {X Y₁ Y₂ : Set} {F₁ F₂ : LT.Fun 0}
           {R₁ : V.⟦ F₁ ⟧F X → Y₁ → Set} {R₂ : V.⟦ F₂ ⟧F X → Y₂ → Set} {R′ : V.⟦ F₁ LT.⊗ F₂ ⟧F X → Y₁ × Y₂ → Set}
           {x₁ x₂ y₁ y₂}
         → MR (pr π₀) R₁ (LOps.seqM u₀ F₁ x₁) y₁ → MR (pr π₀) R₂ (LOps.seqM u₀ F₂ x₂) y₂
         → (∀ {a₁ a₂ b₁ b₂} → R₁ a₁ b₁ → R₂ a₂ b₂ → R′ (a₁ , a₂) (b₁ , b₂))
         → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊗ F₂) (x₁ , x₂))
                         (SE.bind π₀ y₁ λ b₁ → SE.bind π₀ y₂ λ b₂ → SE.return π₀ (b₁ , b₂))
  pair-R Once.Spec.Grade.⊑-pure r₁ r₂ k = k r₁ r₂
  pair-R Once.Spec.Grade.⊑-pa   r₁ r₂ k = bindT-R r₁ (λ a → bindT-R r₂ (λ b → ret (k a b)))
  pair-R Once.Spec.Grade.⊑-pe   r₁ r₂ k = bind∞-R (λ a → bind∞-R (λ b → return∞-R (k a b)) r₂) r₁

-- The algebras, related.
module _ {valg : LGr.⟦ LT.⟦ Fg ⟧F Ag ⟧ᵛ → LGr.M π LGr.⟦ Ag ⟧ᵛ}
         {alg′ : SD.⟦ ST.⟦ F ⟧F A ST.⟨ σ ⟩ ⟧ᵛ → SE.M π SD.⟦ A ST.⟨ σ ⟩ ⟧ᵛ}
         (ralg : ∀ {x y} → ValR (GR-⟦⟧σ σ F gA) x y → MR (pr π) (ValR gA) (valg x) (alg′ y)) where

  -- the compiler's algebra on a layer of folded children (as `cata-semᵛ`)
  alg₂ : LPoly.⟦ translateF Carrier Carrier Fg ⟧SF (LGr.M π LGr.⟦ Ag ⟧ᵛ) → LGr.M π LGr.⟦ Ag ⟧ᵛ
  alg₂ x = LGr.bindM π (LOps.seqM u Fg (V.coerce-μ-out wf _ x)) (λ layer → valg (LOps.cf⁻¹ᵛ Ag wf layer))

  -- the Spec's
  a : SPoly.⟦ G ⟧SF SD.⟦ A ST.⟨ σ ⟩ ⟧ᵛ → SE.M π SD.⟦ A ST.⟨ σ ⟩ ⟧ᵛ
  a l = alg′ (SD.fromL σ F A l)

  fold-R  : ∀ {v w} → μR f₀ v w → MR (pr π) (ValR gA) (LPoly.cataS alg₂ v) (SD.foldM π G a w)
  layer-R : ∀ (F₁ : ST.Fun m) (wf₁ : LW.WellFormedF (F₁ ST.⟨ σ ⟩F)) {x y}
          → LayerR (gf (F₁ ST.⟨ σ ⟩F)) (μR f₀) x y
          → MR (pr π) (LayerV (gf (F₁ ST.⟨ σ ⟩F)) (ValR gA))
               (LOps.seqM u (F₁ ST.⟨ σ ⟩F) (V.coerce-μ-out wf₁ _ (LPoly.sfmapCata (translateF Carrier Carrier (F₁ ST.⟨ σ ⟩F)) alg₂ x)))
               (SD.layerM π G (SD.code (F₁ ST.⟨ σ ⟩F)) a y)

  fold-R (inR l) = bind-R (pr π) (layer-R F wf l) (λ rl → ralg (cf⁻¹-R σ F wf gA rl))

  layer-R (ST.K B) (LW.wf-K ib) r = unit-R u (fromBase-R ib (gr _) r)
    where
      unit-R : ∀ {π₀} (u₀ : LG.pure Once.Spec.Grade.⊑π π₀) {Y : Set} {R : V.⟦ B ST.⟨ σ ⟩ ⟧ → Y → Set} {x y} → R x y
             → MR (pr π₀) R (LOps.seqM u₀ (ST.K (B ST.⟨ σ ⟩)) {X = LGr.⟦ Ag ⟧ᵛ} x) (SE.return π₀ y)
      unit-R Once.Spec.Grade.⊑-pure r = r
      unit-R Once.Spec.Grade.⊑-pa   r = ret r
      unit-R Once.Spec.Grade.⊑-pe   r = return∞-R r
  layer-R ST.Id LW.wf-Id r = id-R u (fold-R r)
    where
      id-R : ∀ {π₀} (u₀ : LG.pure Once.Spec.Grade.⊑π π₀) {X Y : Set} {R : X → Y → Set} {x y} → MR (pr π₀) R x y
           → MR (pr π₀) R (LOps.seqM u₀ LT.Id x) y
      id-R Once.Spec.Grade.⊑-pure r = r
      id-R Once.Spec.Grade.⊑-pa   r = r
      id-R Once.Spec.Grade.⊑-pe   r = r
  layer-R (F₁ ST.⊕ H) (LW.wf-Sum wf₁ wh) {inj₁ _} {inj₁ _} r = inl-R u (layer-R F₁ wf₁ r) (λ x → x)
  layer-R (F₁ ST.⊕ H) (LW.wf-Sum wf₁ wh) {inj₂ _} {inj₂ _} r = inr-R u (layer-R H wh r) (λ x → x)
  layer-R (F₁ ST.⊕ H) (LW.wf-Sum wf₁ wh) {inj₁ _} {inj₂ _} ()
  layer-R (F₁ ST.⊕ H) (LW.wf-Sum wf₁ wh) {inj₂ _} {inj₁ _} ()
  layer-R (F₁ ST.⊗ H) (LW.wf-Prod wf₁ wh) {_ , _} {_ , _} (r , r′) =
    pair-R u (layer-R F₁ wf₁ r) (layer-R H wh r′) (λ x y → x , y)
