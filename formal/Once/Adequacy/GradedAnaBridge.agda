-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.GradedAnaBridge — the unfold congruence between the GRADED
-- Spec unfold (`ana-semᵛ`) and the Kleisli one (SD's `anaFᵈ`), D250.
--
-- A PURE ν is plain codata (`anaᵖ`): its coalgebra is a total function,
-- computed once. SD stores the coalgebra's computation and runs it in every
-- forced layer (D247). The two agree because the computation is related to a
-- silent return of that function — so each Kleisli layer is silent and returns
-- the layer the pure coalgebra gives (`anaᵖ-∼`, the heterogeneous
-- bisimulation's coinduction). An EFFECTFUL ν is `anaᵈ` on both sides, over
-- seeds of the two domains (`anaᵈ-∼` is already heterogeneous in its seeds).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.GradedAnaBridge (fmt : TargetNum) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Res using (Res; stopped; returns; mapRes; Res-rel; rel-stopped; rel-returns)
open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; ν-type; _⇒[_]_; mk-kind; Many; Purity; pure; eff)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF)
open import Once.Semantics.Machine using (coerce-ν-in; ⟦_⟧F)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; νᵈ; forceᵈ; anaᵈ; anaLayer; mapAnaᵈ; anaFᵈ; coerce-functor-D)
open import Once.Denotation.ValueDomainLaws using (CoalgRel; anaᵈ-∼)
open import Once.Denotation.TraceMonad using (T; projTrace; returnT; fmapT; _>>=T_)
open import Once.Denotation.GradedDomain using (M; ⟦_⟧ᵛ; νᵖ; forceᵖ; returnM; bindM; bindM-idˡ; toT)
open import Once.Denotation.GradedOps using (cfᵛ; anaᵖ; mapAnaᵖ; ana-semᵛ)
open import Once.Adequacy.GradedRelation fmt
  using (RelGV; RelGT; RelGM; RelGT-bind; _∼ᵖᵈ_; traceᵖᵈ-∼; layerᵖᵈ-∼; prjB-rel)

------------------------------------------------------------------------
-- Pure codata against effectful codata, by coinduction.
------------------------------------------------------------------------

mutual
  anaᵖ-∼ : ∀ (H : SFunctor) {X Y : Set} {R : X → Y → Set}
             {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T (⟦ H ⟧SF Y)}
         → CoalgRel H R (λ x → returnT (c₁ x)) c₂
         → ∀ {a b} → R a b → anaᵖ H c₁ a ∼ᵖᵈ anaᵈ H c₂ b
  traceᵖᵈ-∼ (anaᵖ-∼ H cr r) k = proj₁ (cr r) k
  layerᵖᵈ-∼ (anaᵖ-∼ H {c₂ = c₂} cr {b = b} r) = anaLayerᵖ H cr (T.resT (c₂ b)) (proj₂ (cr r))

  anaLayerᵖ : ∀ (H : SFunctor) {X Y : Set} {R : X → Y → Set}
                {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T (⟦ H ⟧SF Y)}
            → CoalgRel H R (λ x → returnT (c₁ x)) c₂
            → ∀ {l} (r : Res (⟦ H ⟧SF Y))
            → Res-rel (⟦ H ⟧SF-rel R) (returns l) r
            → Res-rel (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H}))
                      (returns (mapAnaᵖ H H c₁ l)) (anaLayer H c₂ r)
  anaLayerᵖ H cr (returns y) (rel-returns rr) = rel-returns (mapAnaᵖ-∼ H H cr rr)

  mapAnaᵖ-∼ : ∀ (H G : SFunctor) {X Y : Set} {R : X → Y → Set}
                {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T (⟦ H ⟧SF Y)}
            → CoalgRel H R (λ x → returnT (c₁ x)) c₂
            → ∀ {x : ⟦ G ⟧SF X} {y : ⟦ G ⟧SF Y}
            → ⟦ G ⟧SF-rel R x y
            → ⟦ G ⟧SF-rel (_∼ᵖᵈ_ {H}) (mapAnaᵖ H G c₁ x) (mapAnaᵈ H G c₂ y)
  mapAnaᵖ-∼ H (SK B)     cr rel = rel
  mapAnaᵖ-∼ H SId        cr rel = anaᵖ-∼ H cr rel
  mapAnaᵖ-∼ H (G₁ S⊕ G₂) cr {inj₁ _} {inj₁ _} rel = mapAnaᵖ-∼ H G₁ cr rel
  mapAnaᵖ-∼ H (G₁ S⊕ G₂) cr {inj₂ _} {inj₂ _} rel = mapAnaᵖ-∼ H G₂ cr rel
  mapAnaᵖ-∼ H (G₁ S⊕ G₂) cr {inj₁ _} {inj₂ _} ()
  mapAnaᵖ-∼ H (G₁ S⊕ G₂) cr {inj₂ _} {inj₁ _} ()
  mapAnaᵖ-∼ H (G₁ S⊗ G₂) cr {_ , _} {_ , _} (r₁ , r₂) =
    mapAnaᵖ-∼ H G₁ cr r₁ , mapAnaᵖ-∼ H G₂ cr r₂

------------------------------------------------------------------------
-- The coalgebra's layer, read into the S-functor on both sides.
------------------------------------------------------------------------

in-relᵍ : ∀ {A : Type} {G : Functor} (wf : WellFormedF G)
            {l : ⟦ ⟦ G ⟧T A ⟧ᵛ} {r : ⟦ ⟦ G ⟧T A ⟧ᴰ}
        → RelGV (⟦ G ⟧T A) l r
        → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A)
            (coerce-ν-in G ⟦ A ⟧ᵛ (cfᵛ A wf l))
            (coerce-ν-in G ⟦ A ⟧ᴰ (coerce-functor-D G A r))
in-relᵍ (wf-K ib) rel rewrite prjB-rel ib rel = refl
in-relᵍ wf-Id     rel = rel
in-relᵍ (wf-Sum wfF wfG) {inj₁ _} {inj₁ _} rel = in-relᵍ wfF rel
in-relᵍ (wf-Sum wfF wfG) {inj₂ _} {inj₂ _} rel = in-relᵍ wfG rel
in-relᵍ (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
in-relᵍ (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
in-relᵍ (wf-Prod wfF wfG) {_ , _} {_ , _} (rF , rG) = in-relᵍ wfF rF , in-relᵍ wfG rG

in-relᵍ-res : ∀ {A : Type} {G : Functor} (wf : WellFormedF G)
                (r₁ : Res ⟦ ⟦ G ⟧T A ⟧ᵛ) (r₂ : Res ⟦ ⟦ G ⟧T A ⟧ᴰ)
            → Res-rel (RelGV (⟦ G ⟧T A)) r₁ r₂
            → Res-rel (⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A))
                (mapRes (λ l → coerce-ν-in G ⟦ A ⟧ᵛ (cfᵛ A wf l)) r₁)
                (mapRes (coerce-ν-in G ⟦ A ⟧ᴰ) (mapRes (coerce-functor-D G A) r₂))
in-relᵍ-res wf stopped     stopped     rel = rel-stopped
in-relᵍ-res wf (returns _) (returns _) (rel-returns rel) = rel-returns (in-relᵍ wf rel)

------------------------------------------------------------------------
-- The unfold, at each coalgebra grade `π` and construction grade `π₀`. The
-- Spec's coalgebra is a VALUE `c₁`; SD's is a computation `cT` bound in each
-- layer; the premise relates the computation to a silent return of `c₁`.
------------------------------------------------------------------------

-- SD's unfold, as `⟦ ana ⟧ˢ` builds it.
anaSD : ∀ {A : Type} (F : Functor) (π : Purity)
      → T ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᴰ → ⟦ A ⟧ᴰ → νᵈ (translateF Carrier Carrier F)
anaSD {A} F π cT = anaFᵈ F (λ a′ → fmapT (coerce-functor-D F A) (cT >>=T λ clo → clo a′))

ana-bridgeᵍ : ∀ (π π₀ : Purity) {A : Type} {F : Functor} (wfF : WellFormedF F)
                (c₁ : ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᵛ) (cT : T ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᴰ)
            → RelGT (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A) (returnT c₁) cT
            → ∀ {a b} → RelGV A a b
            → RelGM π₀ (ν-type F π) (ana-semᵛ π π₀ wfF (returnM π₀ c₁) a) (returnT (anaSD F π cT b))
ana-bridgeᵍ pure π₀ {A} {F} wfF c₁ cT rc {a} {b} rab =
  subst (λ m → RelGM π₀ (ν-type F pure) m (returnT (anaSD F pure cT b)))
        (sym (bindM-idˡ π₀ c₁ (λ clo → returnM π₀ (anaᵖ H (λ a′ → coerce-ν-in F _ (cfᵛ A wfF (clo a′))) a))))
        (ret π₀)
  where
    H = translateF Carrier Carrier F
    cr : CoalgRel H (RelGV A)
           (λ x → returnT (coerce-ν-in F _ (cfᵛ A wfF (c₁ x))))
           (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (fmapT (coerce-functor-D F A) (cT >>=T λ clo → clo y)))
    cr {x} {y} r =
      (λ j → proj₁ (kr j))
      , in-relᵍ-res wfF (returns (c₁ x)) (T.resT (cT >>=T λ clo → clo y)) (proj₂ (kr 0))
      where
        kr = RelGT-bind {A = A ⇒[ mk-kind Many pure ] ⟦ F ⟧T A} {B = ⟦ F ⟧T A} {t₁ = returnT c₁} {t₂ = cT} {f = λ clo → returnT (clo x)} {g = λ clo → clo y}
                        rc (λ rfg → rfg r)
    ret : ∀ π₀ → RelGM π₀ (ν-type F pure)
                   (returnM π₀ (anaᵖ H (λ a′ → coerce-ν-in F _ (cfᵛ A wfF (c₁ a′))) a))
                   (returnT (anaSD F pure cT b))
    ret pure n = refl , rel-returns (anaᵖ-∼ H cr rab)
    ret eff  n = refl , rel-returns (anaᵖ-∼ H cr rab)
ana-bridgeᵍ eff π₀ {A} {F} wfF c₁ cT rc {a} {b} rab = ret π₀
  where
    H = translateF Carrier Carrier F
    cr : CoalgRel H (RelGV A)
           (λ x → fmapT (λ l → coerce-ν-in F _ (cfᵛ A wfF l)) (c₁ x))
           (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (fmapT (coerce-functor-D F A) (cT >>=T λ clo → clo y)))
    cr {x} {y} r =
      (λ j → proj₁ (kr j))
      , in-relᵍ-res wfF (T.resT (c₁ x)) (T.resT (cT >>=T λ clo → clo y)) (proj₂ (kr 0))
      where
        kr = RelGT-bind {A = A ⇒[ mk-kind Many eff ] ⟦ F ⟧T A} {B = ⟦ F ⟧T A} {t₁ = returnT c₁} {t₂ = cT} {f = λ clo → clo x} {g = λ clo → clo y}
                        rc (λ rfg → rfg r)
    ret : ∀ π₀ → RelGM π₀ (ν-type F eff) (ana-semᵛ eff π₀ wfF (returnM π₀ c₁) a) (returnT (anaSD F eff cT b))
    ret pure n = refl , rel-returns (anaᵈ-∼ H cr rab)
    ret eff  n = refl , rel-returns (anaᵈ-∼ H cr rab)
