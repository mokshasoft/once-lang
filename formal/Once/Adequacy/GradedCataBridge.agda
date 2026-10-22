-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.GradedCataBridge — the fold congruence between the GRADED
-- Spec fold (`cata-semᵛ π`) and the Kleisli one (`cata-sem`), D250.
--
-- Both run `sem-cata` over the SAME `μ` value (first-order data is shared);
-- they differ in the carrier: `M π ⟦A⟧ᵛ` against `T ⟦A⟧ᴰ`. So the fold
-- congruence `cataS-rel` applies at the carrier relation `RelGM π A`, and the
-- algebra step is the only content. Plan 0.119 D5: the Kleisli side is a `T∞`
-- run. At `eff` the layer is sequenced on both sides; at `act` the Spec's is a
-- finite tree, embedded; at `pure` the Spec's layer is already a layer of
-- values, and the Kleisli sequencing of it is silent (`seqF-relᵖ`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.GradedCataBridge (fmt : TargetNum) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import Once.Spec.Word using (Carrier)
open import Once.Spec.Grade using (Purity; pure; act; eff)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-pe; ⊑-pa)
open import Once.Spec.Type using (Type; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type using (Functor; ⟦_⟧T; μ-type)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Semantics.Machine using (coerce-μ-out; ⟦_⟧F)
open import Once.Internal.Stream using (seqF)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; coerce-functor⁻¹-D)
open import Once.Internal.Trace using (T; ret; _>>=T_)
open import Once.Denotation.Meaning using (cata-sem; cata-ev-algᴰ-D)
open import Once.Internal.Graded using (M; ⟦_⟧ᵛ; bindM)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open import Once.Internal.GradedOps using (cf⁻¹ᵛ; seqM; cata-semᵛ)
open import Once.Internal.Iterative using (T∞; seqF∞; return∞; _>>=∞_; fmap∞; embed)
open import Once.Denotation.TraceMonadInfLaws using (RelS; module RelS; s-ret; relS-ret; RelS-bind; RelS-≈ˡ; embed-bind)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (RelS-fmap; retargetˡ)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Adequacy.SeqRel using (RelF)
open import Once.Adequacy.GradedRelation fmt using (RelGV; RelGT; RelGM; injB-rel; RelGT-bind)

-- The out coercion moves a layer relation from the S-functor to the functor,
-- at any carrier relation.
out-relR : ∀ {G} (wf : WellFormedF G) {C₁ C₂ : Set} (R : C₁ → C₂ → Set)
           {y₁ : _} {y₂ : _}
         → RelSF (translateF Carrier Carrier G) R y₁ y₂
         → RelF G R (coerce-μ-out wf C₁ y₁) (coerce-μ-out wf C₂ y₂)
out-relR (wf-K ib) R {y₁} {y₂} feq rewrite feq = refl
out-relR wf-Id     R rc = rc
out-relR (wf-Sum wfF wfG) R {inj₁ _} {inj₁ _} rsf = out-relR wfF R rsf
out-relR (wf-Sum wfF wfG) R {inj₂ _} {inj₂ _} rsf = out-relR wfG R rsf
out-relR (wf-Sum wfF wfG) R {inj₁ _} {inj₂ _} ()
out-relR (wf-Sum wfF wfG) R {inj₂ _} {inj₁ _} ()
out-relR (wf-Prod wfF wfG) R {_ , _} {_ , _} (rf , rg) = out-relR wfF R rf , out-relR wfG R rg

-- A related functor layer reads back to related values of the layer type.
z-relᵍ : ∀ {G} (wf : WellFormedF G) {A : Type} {l : ⟦ G ⟧F ⟦ A ⟧ᵛ} {r : ⟦ G ⟧F ⟦ A ⟧ᴰ}
       → RelF G (RelGV A) l r
       → RelGV (⟦ G ⟧T A) (cf⁻¹ᵛ A wf l) (coerce-functor⁻¹-D wf A r)
z-relᵍ (wf-K ib) {r = r} refl = injB-rel ib r
z-relᵍ wf-Id     rel = rel
z-relᵍ (wf-Sum wfF wfG) {l = inj₁ _} {inj₁ _} rel = z-relᵍ wfF rel
z-relᵍ (wf-Sum wfF wfG) {l = inj₂ _} {inj₂ _} rel = z-relᵍ wfG rel
z-relᵍ (wf-Sum wfF wfG) {l = inj₁ _} {inj₂ _} ()
z-relᵍ (wf-Sum wfF wfG) {l = inj₂ _} {inj₁ _} ()
z-relᵍ (wf-Prod wfF wfG) {l = _ , _} {_ , _} (rf , rg) = z-relᵍ wfF rf , z-relᵍ wfG rg

-- A layer of VALUES against a layer of runs, each of which returns its value
-- silently: sequencing the latter is a silent return of the layer.
seqF-relᵖ : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set)
              {l : ⟦ G ⟧F X} {r : ⟦ G ⟧F (T∞ Y)}
          → RelF G (λ v t → RelS R (return∞ v) t) l r
          → RelS (RelF G R) (return∞ l) (seqF∞ G r)
seqF-relᵖ (K A)   R eq = relS-ret eq
seqF-relᵖ Id      R rel  = rel
seqF-relᵖ (G ⊕ H) R {inj₁ x} {inj₁ y} rel = retargetˡ refl (RelS-fmap {f = inj₁} {g = inj₁} (seqF-relᵖ G R rel) (λ z → z))
seqF-relᵖ (G ⊕ H) R {inj₂ x} {inj₂ y} rel = retargetˡ refl (RelS-fmap {f = inj₂} {g = inj₂} (seqF-relᵖ H R rel) (λ z → z))
seqF-relᵖ (G ⊕ H) R {inj₁ _} {inj₂ _} ()
seqF-relᵖ (G ⊕ H) R {inj₂ _} {inj₁ _} ()
seqF-relᵖ (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  retargetˡ refl (RelS-bind (seqF-relᵖ G R rG) λ ru → RelS-bind (seqF-relᵖ H R rH) λ rv → relS-ret (ru , rv))

private
  emb-ret : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → RelS R (embed (ret x)) (return∞ y)
  forceS (emb-ret r) = s-ret r

-- A layer of finite trees against a layer of runs (`act`).
seqF-relᵃ : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set) {l : ⟦ G ⟧F (T X)} {r : ⟦ G ⟧F (T∞ Y)}
          → RelF G (λ t t′ → RelS R (embed t) t′) l r → RelS (RelF G R) (embed (seqF G l)) (seqF∞ G r)
seqF-relᵃ (K A)   R eq  = emb-ret eq
seqF-relᵃ Id      R rel = rel
seqF-relᵃ (G ⊕ H) R {inj₁ x} {inj₁ y} rel =
  RelS-≈ˡ (embed-bind (seqF G x) (λ z → ret (inj₁ z))) (RelS-bind (seqF-relᵃ G R rel) (λ z → emb-ret z))
seqF-relᵃ (G ⊕ H) R {inj₂ x} {inj₂ y} rel =
  RelS-≈ˡ (embed-bind (seqF H x) (λ z → ret (inj₂ z))) (RelS-bind (seqF-relᵃ H R rel) (λ z → emb-ret z))
seqF-relᵃ (G ⊕ H) R {inj₁ _} {inj₂ _} ()
seqF-relᵃ (G ⊕ H) R {inj₂ _} {inj₁ _} ()
seqF-relᵃ (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  RelS-≈ˡ (embed-bind (seqF G x₁) (λ u → seqF H y₁ >>=T λ v → ret (u , v)))
    (RelS-bind (seqF-relᵃ G R rG) λ {u} ru →
      RelS-≈ˡ (embed-bind (seqF H y₁) (λ v → ret (u , v)))
        (RelS-bind (seqF-relᵃ H R rH) λ rv → emb-ret (ru , rv)))

-- A layer of runs against a layer of runs (`eff`).
seqF∞-rel : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set) {l : ⟦ G ⟧F (T∞ X)} {r : ⟦ G ⟧F (T∞ Y)}
          → RelF G (RelS R) l r → RelS (RelF G R) (seqF∞ G l) (seqF∞ G r)
seqF∞-rel (K A)   R eq  = relS-ret eq
seqF∞-rel Id      R rel = rel
seqF∞-rel (G ⊕ H) R {inj₁ x} {inj₁ y} rel = RelS-fmap {f = inj₁} {g = inj₁} (seqF∞-rel G R rel) (λ z → z)
seqF∞-rel (G ⊕ H) R {inj₂ x} {inj₂ y} rel = RelS-fmap {f = inj₂} {g = inj₂} (seqF∞-rel H R rel) (λ z → z)
seqF∞-rel (G ⊕ H) R {inj₁ _} {inj₂ _} ()
seqF∞-rel (G ⊕ H) R {inj₂ _} {inj₁ _} ()
seqF∞-rel (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  RelS-bind (seqF∞-rel G R rG) λ ru → RelS-bind (seqF∞-rel H R rH) λ rv → relS-ret (ru , rv)

-- The algebra step at each grade.
alg-step : ∀ {π : Purity} (u : pure ⊑π π) {F} {A : Type} (wfF : WellFormedF F)
             (alg₁ : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ ⟦ F ⟧T A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ)
         → (∀ {x y} → RelGV (⟦ F ⟧T A) x y → RelGM π A (alg₁ x) (alg₂ y))
         → ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) (RelGM π A) y₁ y₂
         → RelGM π A (bindM π (seqM u F (coerce-μ-out wfF (M π ⟦ A ⟧ᵛ) y₁)) λ l → alg₁ (cf⁻¹ᵛ A wfF l))
                     (cata-ev-algᴰ-D {F} {A} wfF alg₂ (coerce-μ-out wfF (T∞ ⟦ A ⟧ᴰ) y₂))
alg-step ⊑-pure {F} {A} wfF alg₁ alg₂ algR {y₁} {y₂} rsf =
  subst (λ v → RelGM pure A v (cata-ev-algᴰ-D {F} {A} wfF alg₂ (coerce-μ-out wfF (T∞ ⟦ A ⟧ᴰ) y₂)))
        (sym (>>=ᵖ-β (coerce-μ-out wfF ⟦ A ⟧ᵛ y₁) (λ l → alg₁ (cf⁻¹ᵛ A wfF l))))
        (retargetˡ refl (RelS-bind (seqF-relᵖ F (RelGV A) (out-relR wfF (RelGM pure A) rsf))
                                   (λ r → algR (z-relᵍ wfF r))))
alg-step ⊑-pa {F} {A} wfF alg₁ alg₂ algR {y₁} {y₂} rsf =
  RelS-≈ˡ (embed-bind (seqF F (coerce-μ-out wfF (T ⟦ A ⟧ᵛ) y₁)) (λ l → alg₁ (cf⁻¹ᵛ A wfF l)))
    (RelS-bind (seqF-relᵃ F (RelGV A) (out-relR wfF (RelGM act A) rsf)) (λ r → algR (z-relᵍ wfF r)))
alg-step ⊑-pe {F} {A} wfF alg₁ alg₂ algR {y₁} {y₂} rsf =
  RelS-bind (seqF∞-rel F (RelGV A) (out-relR wfF (RelGM eff A) rsf)) (λ r → algR (z-relᵍ wfF r))

cata-bridgeᵍ : ∀ {π : Purity} (u : pure ⊑π π) {F} {A : Type} {wfF : WellFormedF F}
                 (alg₁ : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ ⟦ F ⟧T A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ)
             → (∀ {x y} → RelGV (⟦ F ⟧T A) x y → RelGM π A (alg₁ x) (alg₂ y))
             → ∀ {a : ⟦ μ-type F ⟧ᵛ} {b : ⟦ μ-type F ⟧ᴰ} → RelGV (μ-type F) a b
             → RelGM π A (cata-semᵛ u wfF alg₁ a) (cata-sem wfF alg₂ b)
cata-bridgeᵍ {π} u {F} {A} {wfF} alg₁ alg₂ algR {a} refl =
  cataS-rel (RelGM π A) (alg-step u wfF alg₁ alg₂ algR) a
