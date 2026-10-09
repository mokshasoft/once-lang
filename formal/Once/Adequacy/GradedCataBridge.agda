-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.GradedCataBridge — the fold congruence between the GRADED
-- Spec fold (`cata-semᵛ π`) and the Kleisli one (`cata-sem`), D250.
--
-- Both run `sem-cata` over the SAME `μ` value (first-order data is shared);
-- they differ in the carrier: `M π ⟦A⟧ᵛ` against `T ⟦A⟧ᴰ`. So the fold
-- congruence `cataS-rel` applies at the carrier relation `RelGM π A`, and the
-- algebra step is the only content. At `eff` the layer is sequenced on both
-- sides; at `pure` the Spec's layer is already a layer of values, and the
-- Kleisli sequencing of it is silent (`seqF-relᵖ`).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.GradedCataBridge (fmt : TargetNum) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)

open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type; K; Id; _⊕_; _⊗_; Purity; pure; eff)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF)
open import Once.Semantics.Machine using (coerce-μ-out; ⟦_⟧F)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; seqF; coerce-functor⁻¹-D)
open import Once.Denotation.TraceMonad using (T; returnT; RelT′; rel-ret)
open import Once.Denotation.TraceMonadLaws using (RelT′-bind; RelT′-fmap)
open import Once.Denotation.Meaning using (cata-sem; cata-ev-algᴰ-D)
open import Once.Denotation.GradedDomain using (M; ⟦_⟧ᵛ; bindM)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open import Once.Denotation.GradedOps using (cf⁻¹ᵛ; seqM; cata-semᵛ)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Adequacy.SeqRel using (RelF; seqF-rel)
open import Once.Adequacy.GradedRelation fmt using (RelGV; RelGT; RelGM; injB-rel)

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

-- A layer of VALUES against a layer of computations, each of which returns
-- its value silently: sequencing the latter is a silent return of the layer.
seqF-relᵖ : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set)
              {l : ⟦ G ⟧F X} {r : ⟦ G ⟧F (T Y)}
          → RelF G (λ v t → RelT′ R (returnT v) t) l r
          → RelT′ (RelF G R) (returnT l) (seqF G r)
seqF-relᵖ (K A)   R eq = rel-ret eq
seqF-relᵖ Id      R rel  = rel
seqF-relᵖ (G ⊕ H) R {inj₁ x} {inj₁ y} rel =
  RelT′-fmap (RelF G R) (RelF (G ⊕ H) R) {g = inj₁} {g′ = inj₁} (λ _ _ z → z) (seqF-relᵖ G R rel)
seqF-relᵖ (G ⊕ H) R {inj₂ x} {inj₂ y} rel =
  RelT′-fmap (RelF H R) (RelF (G ⊕ H) R) {g = inj₂} {g′ = inj₂} (λ _ _ z → z) (seqF-relᵖ H R rel)
seqF-relᵖ (G ⊕ H) R {inj₁ _} {inj₂ _} ()
seqF-relᵖ (G ⊕ H) R {inj₂ _} {inj₁ _} ()
seqF-relᵖ (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  RelT′-bind (RelF G R) (RelF (G ⊗ H) R) (seqF-relᵖ G R rG)
    (λ u u′ ru →
      RelT′-bind (RelF H R) (RelF (G ⊗ H) R) (seqF-relᵖ H R rH)
        (λ v v′ rv → rel-ret (ru , rv)))

-- The algebra step at each grade.
alg-step : ∀ (π : Purity) {F} {A : Type} (wfF : WellFormedF F)
             (alg₁ : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ)
         → (∀ {x y} → RelGV (⟦ F ⟧T A) x y → RelGM π A (alg₁ x) (alg₂ y))
         → ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) (RelGM π A) y₁ y₂
         → RelGM π A (bindM π (seqM π F (coerce-μ-out wfF (M π ⟦ A ⟧ᵛ) y₁)) λ l → alg₁ (cf⁻¹ᵛ A wfF l))
                     (cata-ev-algᴰ-D {F} {A} wfF alg₂ (coerce-μ-out wfF (T ⟦ A ⟧ᴰ) y₂))
alg-step pure {F} {A} wfF alg₁ alg₂ algR {y₁} {y₂} rsf =
  subst (λ v → RelGT A (returnT v) (cata-ev-algᴰ-D {F} {A} wfF alg₂ (coerce-μ-out wfF (T ⟦ A ⟧ᴰ) y₂)))
        (sym (>>=ᵖ-β (coerce-μ-out wfF ⟦ A ⟧ᵛ y₁) (λ l → alg₁ (cf⁻¹ᵛ A wfF l))))
        (RelT′-bind (RelF F (RelGV A)) (RelGV A)
          {m = returnT (coerce-μ-out wfF ⟦ A ⟧ᵛ y₁)} {m′ = seqF F (coerce-μ-out wfF (T ⟦ A ⟧ᴰ) y₂)}
          {f = λ l → returnT (alg₁ (cf⁻¹ᵛ A wfF l))}
          {f′ = λ l → alg₂ (coerce-functor⁻¹-D wfF A l)}
          (seqF-relᵖ F (RelGV A) (out-relR wfF (RelGM pure A) rsf))
          (λ l₁ l₂ r → algR (z-relᵍ wfF r)))
alg-step eff {F} {A} wfF alg₁ alg₂ algR {y₁} {y₂} rsf =
  RelT′-bind (RelF F (RelGV A)) (RelGV A)
    {m = seqF F (coerce-μ-out wfF (T ⟦ A ⟧ᵛ) y₁)} {m′ = seqF F (coerce-μ-out wfF (T ⟦ A ⟧ᴰ) y₂)}
    {f = λ l → alg₁ (cf⁻¹ᵛ A wfF l)}
    {f′ = λ l → alg₂ (coerce-functor⁻¹-D wfF A l)}
    (seqF-rel F (RelGV A) (out-relR wfF (RelGM eff A) rsf))
    (λ l₁ l₂ r → algR (z-relᵍ wfF r))

cata-bridgeᵍ : ∀ (π : Purity) {F} {A : Type} {wfF : WellFormedF F}
                 (alg₁ : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ)
             → (∀ {x y} → RelGV (⟦ F ⟧T A) x y → RelGM π A (alg₁ x) (alg₂ y))
             → ∀ {a : ⟦ μ-type F ⟧ᵛ} {b : ⟦ μ-type F ⟧ᴰ} → RelGV (μ-type F) a b
             → RelGM π A (cata-semᵛ π wfF alg₁ a) (cata-sem wfF alg₂ b)
cata-bridgeᵍ π {F} {A} {wfF} alg₁ alg₂ algR {a} refl =
  cataS-rel (RelGM π A) (alg-step π wfF alg₁ alg₂ algR) a
