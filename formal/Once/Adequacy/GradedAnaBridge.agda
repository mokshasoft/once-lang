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

open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; ν-type; _⇒[_]_; mk-kind; Many; Purity; pure; eff)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF)
open import Once.Semantics.Machine using (coerce-ν-in; ⟦_⟧F)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; νᵈ; forceᵈ; anaᵈ; anaTree; mapAnaᵈ; anaFᵈ; coerce-functor-D)
open import Once.Denotation.ValueDomainLaws using (CoalgRel; anaᵈ-∼)
open import Once.Denotation.TraceMonad using (T; ret; returnT; fmapT; fmapT-∘; _>>=T_; RelT′; rel-ret; RelT′-fmap)
open import Once.Denotation.GradedDomain using (M; ⟦_⟧ᵛ; νᵖ; returnM; bindM; bindM-idˡ; toT)
open Once.Denotation.GradedDomain.νᵖ using (forceᵖ)
open import Once.Denotation.GradedOps using (cfᵛ; anaᵖ; mapAnaᵖ; ana-semᵛ)
open import Once.Adequacy.GradedRelation fmt
  using (RelGV; RelGT; RelGM; RelGT-bind; _∼ᵖᵈ_; force-∼ᵖᵈ; prjB-rel)

------------------------------------------------------------------------
-- Pure codata against effectful codata, by coinduction.
------------------------------------------------------------------------

mutual
  anaᵖ-∼ : ∀ (H : SFunctor) {X Y : Set} {R : X → Y → Set}
             {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T (⟦ H ⟧SF Y)}
         → CoalgRel H R (λ x → returnT (c₁ x)) c₂
         → ∀ {a b} → R a b → anaᵖ H c₁ a ∼ᵖᵈ anaᵈ H c₂ b
  force-∼ᵖᵈ (anaᵖ-∼ H cr r) = anaTreeᵖ H cr (cr r)

  -- The Kleisli side's force is related to a `ret`, so it is one: no call, a
  -- related layer.
  anaTreeᵖ : ∀ (H : SFunctor) {X Y : Set} {R : X → Y → Set}
               {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T (⟦ H ⟧SF Y)}
           → CoalgRel H R (λ x → returnT (c₁ x)) c₂
           → ∀ {l} {m : T (⟦ H ⟧SF Y)}
           → RelT′ (⟦ H ⟧SF-rel R) (ret l) m
           → RelT′ (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (ret (mapAnaᵖ H H c₁ l)) (anaTree H c₂ m)
  anaTreeᵖ H cr (rel-ret rr) = rel-ret (mapAnaᵖ-∼ H H cr rr)

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
            (coerce-ν-in G ⟦ A ⟧ᴰ (coerce-functor-D wf A r))
in-relᵍ (wf-K ib) rel rewrite prjB-rel ib rel = refl
in-relᵍ wf-Id     rel = rel
in-relᵍ (wf-Sum wfF wfG) {inj₁ _} {inj₁ _} rel = in-relᵍ wfF rel
in-relᵍ (wf-Sum wfF wfG) {inj₂ _} {inj₂ _} rel = in-relᵍ wfG rel
in-relᵍ (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
in-relᵍ (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
in-relᵍ (wf-Prod wfF wfG) {_ , _} {_ , _} (rF , rG) = in-relᵍ wfF rF , in-relᵍ wfG rG

-- A related computation, mapped by the two layer readings (the Kleisli one in
-- two steps, as `⟦ ana ⟧ˢ` and the coalgebra build it), stays related.
in-relᵍ-T : ∀ {A : Type} {G : Functor} (wf : WellFormedF G)
              {g : ⟦ ⟦ G ⟧T A ⟧ᵛ → ⟦ translateF Carrier Carrier G ⟧SF ⟦ A ⟧ᵛ}
              (eg : ∀ l → g l ≡ coerce-ν-in G ⟦ A ⟧ᵛ (cfᵛ A wf l))
              {m₁ : T ⟦ ⟦ G ⟧T A ⟧ᵛ} {m₂ : T ⟦ ⟦ G ⟧T A ⟧ᴰ}
            → RelT′ (RelGV (⟦ G ⟧T A)) m₁ m₂
            → RelT′ (⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A))
                (fmapT g m₁)
                (fmapT (coerce-ν-in G ⟦ A ⟧ᴰ) (fmapT (coerce-functor-D wf A) m₂))
in-relᵍ-T {A} {G} wf {g} eg {m₁} {m₂} rm =
  subst (RelT′ (⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A)) (fmapT g m₁))
        (sym (fmapT-∘ (coerce-ν-in G ⟦ A ⟧ᴰ) (coerce-functor-D wf A) m₂))
        (RelT′-fmap (RelGV (⟦ G ⟧T A)) (⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A))
          (λ l₁ l₂ rl → subst (λ z → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A) z
                                       (coerce-ν-in G ⟦ A ⟧ᴰ (coerce-functor-D wf A l₂)))
                              (sym (eg l₁)) (in-relᵍ wf rl))
          rm)

------------------------------------------------------------------------
-- The unfold, at each coalgebra grade `π` and construction grade `π₀`. The
-- Spec's coalgebra is a VALUE `c₁`; SD's is a computation `cT` bound in each
-- layer; the premise relates the computation to a silent return of `c₁`.
------------------------------------------------------------------------

-- SD's unfold, as `⟦ ana ⟧ˢ` builds it.
anaSD : ∀ {A : Type} (F : Functor) → WellFormedF F → (π : Purity)
      → T ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᴰ → ⟦ A ⟧ᴰ → νᵈ (translateF Carrier Carrier F)
anaSD {A} F wf π cT = anaFᵈ F (λ a′ → fmapT (coerce-functor-D wf A) (cT >>=T λ clo → clo a′))

ana-bridgeᵍ : ∀ (π π₀ : Purity) {A : Type} {F : Functor} (wfF : WellFormedF F)
                (c₁ : ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᵛ) (cT : T ⟦ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ⟧ᴰ)
            → RelGT (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A) (returnT c₁) cT
            → ∀ {a b} → RelGV A a b
            → RelGM π₀ (ν-type F π) (ana-semᵛ π π₀ wfF (returnM π₀ c₁) a) (returnT (anaSD F wfF π cT b))
ana-bridgeᵍ pure π₀ {A} {F} wfF c₁ cT rc {a} {b} rab =
  subst (λ m → RelGM π₀ (ν-type F pure) m (returnT (anaSD F wfF pure cT b)))
        (sym (bindM-idˡ π₀ c₁ (λ clo → returnM π₀ (anaᵖ H (λ a′ → coerce-ν-in F _ (cfᵛ A wfF (clo a′))) a))))
        (retR π₀)
  where
    H = translateF Carrier Carrier F
    cr : CoalgRel H (RelGV A)
           (λ x → returnT (coerce-ν-in F _ (cfᵛ A wfF (c₁ x))))
           (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (fmapT (coerce-functor-D wfF A) (cT >>=T λ clo → clo y)))
    cr {x} {y} r = in-relᵍ-T wfF (λ l → refl) kr
      where
        kr = RelGT-bind {A = A ⇒[ mk-kind Many pure ] ⟦ F ⟧T A} {B = ⟦ F ⟧T A} {t₁ = returnT c₁} {t₂ = cT} {f = λ clo → returnT (clo x)} {g = λ clo → clo y}
                        rc (λ rfg → rfg r)
    retR : ∀ π₀ → RelGM π₀ (ν-type F pure)
                   (returnM π₀ (anaᵖ H (λ a′ → coerce-ν-in F _ (cfᵛ A wfF (c₁ a′))) a))
                   (returnT (anaSD F wfF pure cT b))
    retR pure = rel-ret (anaᵖ-∼ H cr rab)
    retR eff  = rel-ret (anaᵖ-∼ H cr rab)
ana-bridgeᵍ eff π₀ {A} {F} wfF c₁ cT rc {a} {b} rab = retR π₀
  where
    H = translateF Carrier Carrier F
    cr : CoalgRel H (RelGV A)
           (λ x → fmapT (λ l → coerce-ν-in F _ (cfᵛ A wfF l)) (c₁ x))
           (λ y → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ) (fmapT (coerce-functor-D wfF A) (cT >>=T λ clo → clo y)))
    cr {x} {y} r = in-relᵍ-T wfF (λ l → refl) kr
      where
        kr = RelGT-bind {A = A ⇒[ mk-kind Many eff ] ⟦ F ⟧T A} {B = ⟦ F ⟧T A} {t₁ = returnT c₁} {t₂ = cT} {f = λ clo → clo x} {g = λ clo → clo y}
                        rc (λ rfg → rfg r)
    retR : ∀ π₀ → RelGM π₀ (ν-type F eff) (ana-semᵛ eff π₀ wfF (returnM π₀ c₁) a) (returnT (anaSD F wfF eff cT b))
    retR pure = rel-ret (anaᵈ-∼ H cr rab)
    retR eff  = rel-ret (anaᵈ-∼ H cr rab)
