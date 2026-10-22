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
-- bisimulation's coinduction). At `act` (layers in `T`, D313) it is `anaᵈ` on
-- both sides (`anaᵈ-∼`, heterogeneous in its seeds). D318: a ν's grade is
-- finite, so there is no third case.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.GradedAnaBridge (fmt : TargetNum) where

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Once.Spec.Word using (Carrier)
open import Once.Spec.Grade using (mk-kind; Many; Purity; pure; act; eff; Finite; fin; pureᶠ; actᶠ)
open import Once.Spec.Type using (Type; _⇒[_]_)
open import Once.Internal.Type using (Functor; ⟦_⟧T; ν-type)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Semantics.Machine using (coerce-ν-in)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Internal.Stream using (νᵈ; anaᵈ; anaTree; mapAnaᵈ)
open import Once.Internal.StreamInf using (νᴵ; anaᴵ; anaRun; anaBlock; mapAnaᴵ; anaFᴵ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; coerce-functor-D)
open import Once.Internal.Trace using (T; ret; call; halt; fmapT; _>>=T_)
open import Once.Internal.Graded using (⟦_⟧ᵛ)
open import Once.Internal.GradedOps using (cfᵛ; anaᵖ; mapAnaᵖ; ana-semᵛ)
open import Once.Adequacy.GradedRelation fmt
  using (RelGV; RelGT; RelGM; _∼ᵖᵈ_; _∼ᵈ_; prjB-rel; module _∼ᵖᵈ_; module _∼ᵈ_)
open _∼ᵖᵈ_ using (force-∼ᵖᵈ)
open _∼ᵈ_ using (force-∼)
open import Once.Internal.Iterative using (T∞; fmap∞; return∞; _>>=∞_; embed; embedBlock; bindBlock)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt; RelS-≈ˡ; embed-bind)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (RelS-fmapˡ; RelS-fmapʳ; retargetˡ)

------------------------------------------------------------------------
-- The unfolds: a Spec unfold against the IR's, coalgebras related on related
-- seeds (plan 0.119 D5: the IR's coalgebra is a `T∞` run).
------------------------------------------------------------------------

module _ (H : SFunctor) {X Y : Set} {R : X → Y → Set} where

  -- A pure Spec unfold: its layer is there at once.
  module _ {c₁ : X → ⟦ H ⟧SF X} {c₂ : Y → T∞ (⟦ H ⟧SF Y)}
           (cr : ∀ {x y} → R x y → RelS (⟦ H ⟧SF-rel R) (return∞ (c₁ x)) (c₂ y)) where
    anaᵖ-∼    : ∀ {a b} → R a b → anaᵖ H c₁ a ∼ᵖᵈ anaᴵ H c₂ b
    anaRunᵖ   : ∀ {l m} → RelS (⟦ H ⟧SF-rel R) (return∞ l) m
              → RelS (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (return∞ (mapAnaᵖ H H c₁ l)) (anaRun H c₂ m)
    anaBlockᵖ : ∀ {l b} → RelSB (⟦ H ⟧SF-rel R) (ret (inj₁ l)) b
              → RelSB (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (ret (inj₁ (mapAnaᵖ H H c₁ l))) (anaBlock H c₂ b)
    mapAnaᵖ-∼ : ∀ (G : SFunctor) {x : ⟦ G ⟧SF X} {y : ⟦ G ⟧SF Y}
              → ⟦ G ⟧SF-rel R x y → ⟦ G ⟧SF-rel (_∼ᵖᵈ_ {H}) (mapAnaᵖ H G c₁ x) (mapAnaᴵ H G c₂ y)
    force-∼ᵖᵈ (anaᵖ-∼ r) = anaRunᵖ (cr r)
    forceS (anaRunᵖ h) = anaBlockᵖ (forceS h)
    anaBlockᵖ (s-ret rr) = s-ret (mapAnaᵖ-∼ H rr)
    mapAnaᵖ-∼ (SK B)     rel = rel
    mapAnaᵖ-∼ SId        rel = anaᵖ-∼ rel
    mapAnaᵖ-∼ (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} rel = mapAnaᵖ-∼ G₁ rel
    mapAnaᵖ-∼ (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} rel = mapAnaᵖ-∼ G₂ rel
    mapAnaᵖ-∼ (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
    mapAnaᵖ-∼ (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
    mapAnaᵖ-∼ (G₁ S⊗ G₂) {_ , _} {_ , _} (r₁ , r₂) = mapAnaᵖ-∼ G₁ r₁ , mapAnaᵖ-∼ G₂ r₂

  -- An `act` Spec unfold: its layer is a finite block, embedded.
  module _ {c₁ : X → T (⟦ H ⟧SF X)} {c₂ : Y → T∞ (⟦ H ⟧SF Y)}
           (cr : ∀ {x y} → R x y → RelS (⟦ H ⟧SF-rel R) (embed (c₁ x)) (c₂ y)) where
    anaᵈ-∼    : ∀ {a b} → R a b → anaᵈ H c₁ a ∼ᵈ anaᴵ H c₂ b
    anaRunᵈ   : ∀ {t m} → RelS (⟦ H ⟧SF-rel R) (embed t) m
              → RelS (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (embed (anaTree H c₁ t)) (anaRun H c₂ m)
    anaBlockᵈ : ∀ (t : T (⟦ H ⟧SF X)) {b} → RelSB (⟦ H ⟧SF-rel R) (embedBlock t) b
              → RelSB (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (embedBlock (anaTree H c₁ t)) (anaBlock H c₂ b)
    mapAnaᵈ-∼ : ∀ (G : SFunctor) {x : ⟦ G ⟧SF X} {y : ⟦ G ⟧SF Y}
              → ⟦ G ⟧SF-rel R x y → ⟦ G ⟧SF-rel (_∼ᵈ_ {H}) (mapAnaᵈ H G c₁ x) (mapAnaᴵ H G c₂ y)
    force-∼ (anaᵈ-∼ {a} r) = anaRunᵈ {t = c₁ a} (cr r)
    forceS (anaRunᵈ {t} h) = anaBlockᵈ t (forceS h)
    anaBlockᵈ (ret l)      (s-ret rr) = s-ret (mapAnaᵈ-∼ H rr)
    anaBlockᵈ (call o a k) (s-call f) = s-call (λ v → anaBlockᵈ (k v) (f v))
    anaBlockᵈ (halt o a)   s-halt     = s-halt
    mapAnaᵈ-∼ (SK B)     rel = rel
    mapAnaᵈ-∼ SId        rel = anaᵈ-∼ rel
    mapAnaᵈ-∼ (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} rel = mapAnaᵈ-∼ G₁ rel
    mapAnaᵈ-∼ (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} rel = mapAnaᵈ-∼ G₂ rel
    mapAnaᵈ-∼ (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
    mapAnaᵈ-∼ (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
    mapAnaᵈ-∼ (G₁ S⊗ G₂) {_ , _} {_ , _} (r₁ , r₂) = mapAnaᵈ-∼ G₁ r₁ , mapAnaᵈ-∼ G₂ r₂

------------------------------------------------------------------------
-- The ν-in coercions, heterogeneously (as `out-relᵍ`, the other way).
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

-- The IR side's two layer maps, against a run related at the layer type: the
-- Spec value, coerced in, is related to the mapped IR layer.
in-run : ∀ {A : Type} {G : Functor} (wf : WellFormedF G) {Z : Set} {m : T∞ Z} {S : Z → ⟦ ⟦ G ⟧T A ⟧ᴰ → Set}
           {n : T∞ ⟦ ⟦ G ⟧T A ⟧ᴰ} (val : Z → ⟦ ⟦ G ⟧T A ⟧ᵛ)
       → (∀ {z r} → S z r → RelGV (⟦ G ⟧T A) (val z) r)
       → RelS S m n
       → RelS (λ z r″ → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelGV A) (coerce-ν-in G ⟦ A ⟧ᵛ (cfᵛ A wf (val z))) r″)
              m (fmap∞ (coerce-ν-in G ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wf A) n))
in-run {A} {G} wf val h rn =
  RelS-fmapʳ (RelS-fmapʳ {R′ = λ z r′ → Σ[ r ∈ _ ] (r′ ≡ coerce-functor-D wf A r) × RelGV (⟦ G ⟧T A) (val z) r}
                         rn (λ {z} {r} s → r , refl , h s))
             (λ { (r , refl , rv) → in-relᵍ wf rv })

------------------------------------------------------------------------
-- THE UNFOLD BRIDGE: the coalgebra's Spec meaning and the IR's closure related,
-- related seeds unfold to related streams.
------------------------------------------------------------------------

ana-bridgeᵍ : ∀ (φ : Finite) {A : Type} {F : Functor} (wfF : WellFormedF F)
                (c₁ : ⟦ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ⟧ᵛ) (c₂ : ⟦ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ⟧ᴰ)
            → RelGV (A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A) c₁ c₂
            → ∀ {a b} → RelGV A a b
            → RelGV (ν-type F φ) (ana-semᵛ φ wfF c₁ a) (anaFᴵ F (λ a′ → fmap∞ (coerce-functor-D wfF A) (c₂ a′)) b)
ana-bridgeᵍ pureᶠ {A} {F} wfF c₁ c₂ (rc , _) rab = anaᵖ-∼ (translateF Carrier Carrier F) cr rab
  where
    cr : ∀ {x y} → RelGV A x y → RelS (⟦ translateF Carrier Carrier F ⟧SF-rel (RelGV A))
                                       (return∞ (coerce-ν-in F _ (cfᵛ A wfF (c₁ x))))
                                       (fmap∞ (coerce-ν-in F ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wfF A) (c₂ y)))
    cr {x} r = retargetˡ refl (RelS-fmapˡ {f = λ l → coerce-ν-in F _ (cfᵛ A wfF l)}
                                          (in-run wfF (λ l → l) (λ s → s) (rc r)) (λ z → z))
ana-bridgeᵍ actᶠ {A} {F} wfF c₁ c₂ (rc , _) rab = anaᵈ-∼ (translateF Carrier Carrier F) cr rab
  where
    g : ⟦ ⟦ F ⟧T A ⟧ᵛ → ⟦ translateF Carrier Carrier F ⟧SF ⟦ A ⟧ᵛ
    g l = coerce-ν-in F _ (cfᵛ A wfF l)
    -- `embed` is a monad morphism: a mapped finite block embeds as the map of
    -- its embedding.
    emb-map : ∀ {S : _ → _ → Set} (t : T ⟦ ⟦ F ⟧T A ⟧ᵛ) {n}
            → RelS (λ l r → S (g l) r) (embed t) n → RelS S (embed (fmapT g t)) n
    emb-map t h = RelS-≈ˡ (embed-bind t (λ l → ret (g l))) (emb-fmap h)
      where
        emb-fmap  : ∀ {S : _ → _ → Set} {m n} → RelS (λ l r → S (g l) r) m n → RelS S (m >>=∞ λ l → embed (ret (g l))) n
        emb-fmapB : ∀ {S : _ → _ → Set} {b b′} → RelSB (λ l r → S (g l) r) b b′ → RelSB S (bindBlock b λ l → embed (ret (g l))) b′
        forceS (emb-fmap h) = emb-fmapB (forceS h)
        emb-fmapB (s-ret r)  = s-ret r
        emb-fmapB (s-next h) = s-next (emb-fmap h)
        emb-fmapB (s-call f) = s-call (λ v → emb-fmapB (f v))
        emb-fmapB s-halt     = s-halt
    cr : ∀ {x y} → RelGV A x y → RelS (⟦ translateF Carrier Carrier F ⟧SF-rel (RelGV A))
                                       (embed (fmapT g (c₁ x)))
                                       (fmap∞ (coerce-ν-in F ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wfF A) (c₂ y)))
    cr {x} r = emb-map (c₁ x) (in-run wfF (λ l → l) (λ s → s) (rc r))
