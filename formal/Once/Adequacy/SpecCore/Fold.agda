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
import Once.Lang.Core.PolyTy as LP
import Once.Lang.Type.Grade as LG
import Once.Lang.Type.Sub as LS
import Once.Lang.Type.WellFormed as LW
import Once.Spec.Type as ST
open import Once.Adequacy.SpecCore.Index using (InstG)

module Once.Adequacy.SpecCore.Fold (Σ : Signature)
  {m} {σ : LP.GSub m} {σ′ : ST.TySub m 0} (g : InstG σ σ′)
  (F : LP.Fun m) (A : LP.Ty m) (wf : LW.WellFormedF (F LP.⟪ σ ⟫F))
  {π} (u : LG.pure LS.⊑π π) where

open import Data.Product using (_×_; _,_)
import Data.Sum as SPolyS
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Word using (Carrier)
import Once.Lang.Value Carrier Carrier as V
import Once.Lang.Graded as LGr
import Once.Lang.GradedOps as LOps
import Once.Lang.Polynomial as LPoly
open import Once.Lang.FunctorMeaning using (translateF)
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Spec.Polynomial as SPoly
import Once.Lang.Type as LT
open import Once.Adequacy.SpecGrammar.Conv using (πS)
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Layer Σ

private
  Fg = F LP.⟪ σ ⟫F
  Ag = A LP.⟪ σ ⟫
  F′ = pfunS F
  A′ = ptyS A
  G  = SD.code (F′ ST.⟨ σ′ ⟩F)
  f₀ = GF-inst (pfr F) g
  gA = GR-inst (ptr A) g

-- One layer of computations, sequenced on both sides: the injections and the
-- pairing, at each grade a fold may have.
private
  module _ {X Y : Set} where
    inl-R : ∀ {π₀} (u₀ : LG.pure LS.⊑π π₀) {F₁ F₂ : LT.Functor} {Y₂ : Set} {R : V.⟦ F₁ ⟧F X → Y → Set}
            {R′ : V.⟦ F₁ LT.⊕ F₂ ⟧F X → Y SPolyS.⊎ Y₂ → Set} {x y}
          → MR (pr π₀) R (LOps.seqM u₀ F₁ x) y → (∀ {a b} → R a b → R′ (inj₁ a) (inj₁ b))
          → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊕ F₂) (inj₁ x)) (SE.fmap (πS π₀) inj₁ y)
    inl-R LS.⊑-pure r k = k r
    inl-R LS.⊑-pa   r k = fmap-R pr-act r k
    inl-R LS.⊑-pe   r k = fmap-R pr-eff r k

    inr-R : ∀ {π₀} (u₀ : LG.pure LS.⊑π π₀) {F₁ F₂ : LT.Functor} {Y₁ : Set} {R : V.⟦ F₂ ⟧F X → Y → Set}
            {R′ : V.⟦ F₁ LT.⊕ F₂ ⟧F X → Y₁ SPolyS.⊎ Y → Set} {x y}
          → MR (pr π₀) R (LOps.seqM u₀ F₂ x) y → (∀ {a b} → R a b → R′ (inj₂ a) (inj₂ b))
          → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊕ F₂) (inj₂ x)) (SE.fmap (πS π₀) inj₂ y)
    inr-R LS.⊑-pure r k = k r
    inr-R LS.⊑-pa   r k = fmap-R pr-act r k
    inr-R LS.⊑-pe   r k = fmap-R pr-eff r k

  pair-R : ∀ {π₀} (u₀ : LG.pure LS.⊑π π₀) {X Y₁ Y₂ : Set} {F₁ F₂ : LT.Functor}
           {R₁ : V.⟦ F₁ ⟧F X → Y₁ → Set} {R₂ : V.⟦ F₂ ⟧F X → Y₂ → Set} {R′ : V.⟦ F₁ LT.⊗ F₂ ⟧F X → Y₁ × Y₂ → Set}
           {x₁ x₂ y₁ y₂}
         → MR (pr π₀) R₁ (LOps.seqM u₀ F₁ x₁) y₁ → MR (pr π₀) R₂ (LOps.seqM u₀ F₂ x₂) y₂
         → (∀ {a₁ a₂ b₁ b₂} → R₁ a₁ b₁ → R₂ a₂ b₂ → R′ (a₁ , a₂) (b₁ , b₂))
         → MR (pr π₀) R′ (LOps.seqM u₀ (F₁ LT.⊗ F₂) (x₁ , x₂))
                         (SE.bind (πS π₀) y₁ λ b₁ → SE.bind (πS π₀) y₂ λ b₂ → SE.return (πS π₀) (b₁ , b₂))
  pair-R LS.⊑-pure r₁ r₂ k = k r₁ r₂
  pair-R LS.⊑-pa   r₁ r₂ k = bindT-R r₁ (λ a → bindT-R r₂ (λ b → ret (k a b)))
  pair-R LS.⊑-pe   r₁ r₂ k = bind∞-R (λ a → bind∞-R (λ b → return∞-R (k a b)) r₂) r₁

-- The algebras, related.
module _ {valg : LGr.⟦ LT.⟦ Fg ⟧T Ag ⟧ᵛ → LGr.M π LGr.⟦ Ag ⟧ᵛ}
         {alg′ : SD.⟦ ST.⟦ F′ ⟧F A′ ST.⟨ σ′ ⟩ ⟧ᵛ → SE.M (πS π) SD.⟦ A′ ST.⟨ σ′ ⟩ ⟧ᵛ}
         (ralg : ∀ {x y} → ValR (GR-⟦⟧ g (pfr F) gA) x y → MR (pr π) (ValR gA) (valg x) (alg′ y)) where

  -- the compiler's algebra on a layer of folded children (as `cata-semᵛ`)
  alg₂ : LPoly.⟦ translateF Carrier Carrier Fg ⟧SF (LGr.M π LGr.⟦ Ag ⟧ᵛ) → LGr.M π LGr.⟦ Ag ⟧ᵛ
  alg₂ x = LGr.bindM π (LOps.seqM u Fg (V.coerce-μ-out wf _ x)) (λ layer → valg (LOps.cf⁻¹ᵛ Ag wf layer))

  -- the Spec's
  a : SPoly.⟦ G ⟧SF SD.⟦ A′ ST.⟨ σ′ ⟩ ⟧ᵛ → SE.M (πS π) SD.⟦ A′ ST.⟨ σ′ ⟩ ⟧ᵛ
  a l = alg′ (SD.fromL σ′ F′ A′ l)

  fold-R  : ∀ {v w} → μR f₀ v w → MR (pr π) (ValR gA) (LPoly.cataS alg₂ v) (SD.foldM (πS π) G a w)
  layer-R : ∀ {F₁ F₁′} (sub : PFR F₁ F₁′) (wf₁ : LW.WellFormedF (F₁ LP.⟪ σ ⟫F)) {x y}
          → LayerR (GF-inst sub g) (μR f₀) x y
          → MR (pr π) (LayerV (GF-inst sub g) (ValR gA))
               (LOps.seqM u (F₁ LP.⟪ σ ⟫F) (V.coerce-μ-out wf₁ _ (LPoly.sfmapCata (translateF Carrier Carrier (F₁ LP.⟪ σ ⟫F)) alg₂ x)))
               (SD.layerM (πS π) G (SD.code (F₁′ ST.⟨ σ′ ⟩F)) a y)

  fold-R (inR l) = bind-R (pr π) (layer-R (pfr F) wf l) (λ rl → ralg (cf⁻¹-R g (pfr F) wf gA rl))

  layer-R {F₁ = LP.K B} (p-K b) (LW.wf-K ib) r = unit-R u (fromBase-R ib (GR-inst b g) r)
    where
      unit-R : ∀ {π₀} (u₀ : LG.pure LS.⊑π π₀) {Y : Set} {R : V.⟦ B LP.⟪ σ ⟫ ⟧ → Y → Set} {x y} → R x y
             → MR (pr π₀) R (LOps.seqM u₀ (LT.K (B LP.⟪ σ ⟫)) {X = LGr.⟦ Ag ⟧ᵛ} x) (SE.return (πS π₀) y)
      unit-R LS.⊑-pure r = r
      unit-R LS.⊑-pa   r = ret r
      unit-R LS.⊑-pe   r = return∞-R r
  layer-R p-Id LW.wf-Id r = id-R u (fold-R r)
    where
      id-R : ∀ {π₀} (u₀ : LG.pure LS.⊑π π₀) {X Y : Set} {R : X → Y → Set} {x y} → MR (pr π₀) R x y
           → MR (pr π₀) R (LOps.seqM u₀ LT.Id x) y
      id-R LS.⊑-pure r = r
      id-R LS.⊑-pa   r = r
      id-R LS.⊑-pe   r = r
  layer-R (p-⊕ f h) (LW.wf-Sum wf₁ wh) {inj₁ _} {inj₁ _} r = inl-R u (layer-R f wf₁ r) (λ x → x)
  layer-R (p-⊕ f h) (LW.wf-Sum wf₁ wh) {inj₂ _} {inj₂ _} r = inr-R u (layer-R h wh r) (λ x → x)
  layer-R (p-⊕ f h) (LW.wf-Sum wf₁ wh) {inj₁ _} {inj₂ _} ()
  layer-R (p-⊕ f h) (LW.wf-Sum wf₁ wh) {inj₂ _} {inj₁ _} ()
  layer-R (p-⊗ f h) (LW.wf-Prod wf₁ wh) {_ , _} {_ , _} (r , r′) =
    pair-R u (layer-R f wf₁ r) (layer-R h wh r′) (λ x y → x , y)
