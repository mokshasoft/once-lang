------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`, part 3a: `eqG`'s ELIMINATOR.
--
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStepExtE where

open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt public
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtLs public

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS; Id-cong₃
        ; subTy-renTy; renTy-subTy; subTy-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢app; ⊢nsuc; ⊢natrec
        ; ⊢fst; ⊢snd; ⊢nzero; ⊢idrefl; natrec-zero; natrec-suc
        ; ⊢conv; _≅ᵀ_; csymᵀ
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; ⊢⌜Nat⌝
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢; Ren⊢-ext; ren-ty; ren-lemma; ⊢[] )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR
        ; subrenTy; aIHTat-ren; aIHTat-sub; idOfRed )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; sub-w³; ren-w )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; stepᵀ; doneᵀ; red→≅ᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1; ⊢gcdBody
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s; PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ
        ; PAIRˢ; ⊢PAIRˢ; CERTˢ; ⊢CERTˢ )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )


------------------------------------------------------------------------
-- ★★ THE SUBSTITUTION TWINS, and `eqG`'s eliminator.
------------------------------------------------------------------------

gcdIH-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ : RTm Γ) →
            subTy σ (gcdIH μ) ≡ gcdIH (subTm σ μ)
gcdIH-sub μ = aIHTat-sub PairT ⌜Nat⌝ msr μ

pwT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ i₁ i₂ : RTm Γ) →
          subTy σ (pwT μ i₁ i₂) ≡ pwT (subTm σ μ) (subTm σ i₁) (subTm σ i₂)
pwT-sub {σ = σ} μ i₁ i₂ =
  cong₂ (λ u f → Π PairT (Π (Hom Nat (nsuc msr) u) f))
        (sub-w {σ = σ} μ)
        (Id-cong₃ refl (atv (sub-w² {σ = σ} i₁)) (atv (sub-w² {σ = σ} i₂)))
  where
    atv : {u u' : RTm _} → u ≡ u' →
          app (app u (var (vs vz))) (var vz) ≡ app (app u' (var (vs vz))) (var vz)
    atv e = cong (λ z → app (app z (var (vs vz))) (var vz)) e

-- ★ …and the eliminator: feed `eqG` its two IHs and the hypothesis.
--   Three `⊢app`s, three casts, and every cast is `wk-single`/`sub-w`.
eqGElim : {Γ : Ctx} {μ f e i₁ i₂ h : RTm ⌊ Γ ⌋} →
          Γ ⊢ e ∷ eqG μ f → Γ ⊢ i₁ ∷ gcdIH μ → Γ ⊢ i₂ ∷ gcdIH μ →
          Γ ⊢ h ∷ pwT μ i₁ i₂ →
          Γ ⊢ app (app (app e i₁) i₂) h
            ∷ Id (El ⌜Nat⌝) (app f i₁) (app f i₂)
eqGElim {μ = μ} {f = f} {i₁ = i₁} {i₂ = i₂} {h = h} de d₁ d₂ dh =
  ⊢-cast eq3 (⊢app (⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app de d₁)) d₂)) dh)
  where
    eq1 = cong₂ Π (trans (gcdIH-sub (w μ)) (cong gcdIH (wk-single {v = i₁} μ)))
                  (cong₂ Π (trans (pwT-sub (w (w μ)) (var (vs vz)) (var vz))
                                  (cong (λ u → pwT u (w i₁) (var vz))
                                        (trans (sub-w {σ = single i₁} (w μ))
                                               (cong w (wk-single {v = i₁} μ)))))
                           (Id-cong₃ refl
                             (cong₂ (λ z u → app z u)
                                    (trans (sub-w² {σ = single i₁} (w f))
                                           (cong (λ t → w (w t)) (wk-single {v = i₁} f)))
                                    refl)
                             (cong₂ (λ z u → app z u)
                                    (trans (sub-w² {σ = single i₁} (w f))
                                           (cong (λ t → w (w t)) (wk-single {v = i₁} f)))
                                    refl)))

    -- ⚠ ONE BINDER IN, so the slots lose a `w` by `sub-w`-then-`wk-single`,
    --   NOT by `wk-single` alone — `w f` lives one level up and
    --   `wk-single {v = i₂} (w f)` does not even typecheck.  Same peel
    --   `pwElim` uses; the `Π`-DOMAIN slots are the ones that take the bare
    --   `wk-single`, because they sit at the outer level.
    peel₂ : (t : RTm ⌊ _ ⌋) → subTm (extS (single i₂)) (w (w t)) ≡ w t
    peel₂ t = trans (sub-w {σ = single i₂} (w t))
                    (cong w (wk-single {v = i₂} t))

    eq2 = cong₂ Π (trans (pwT-sub (w μ) (w i₁) (var vz))
                         (cong₃' (wk-single {v = i₂} μ) (wk-single {v = i₂} i₁)))
                  (Id-cong₃ refl
                    (cong₂ (λ z u → app z u) (peel₂ f) (peel₂ i₁))
                    (cong₂ (λ z u → app z u) (peel₂ f) refl))
      where
        cong₃' : {a a' b b' : RTm _} → a ≡ a' → b ≡ b' →
                 pwT a b i₂ ≡ pwT a' b' i₂
        cong₃' refl refl = refl

    eq3 = Id-cong₃ refl
            (cong₂ (λ z u → app z u) (wk-single {v = h} f) (wk-single {v = h} i₁))
            (cong₂ (λ z u → app z u) (wk-single {v = h} f) (wk-single {v = h} i₂))

------------------------------------------------------------------------
-- ★★★★★ THE ASSEMBLY — three nested `natrec`s, mirroring `⊢gcdStp` step
--        for step, with `gcdG` replaced by `eqG` throughout.
------------------------------------------------------------------------


-- ★ …and `eqG` past a substitution.  ⚠ NOT definitional, even though `msr`
--   is concrete: `eqG` hides `w μ`, `w² μ` and `w³ f`, and an `extS σ`
--   meeting a `w` is `sub-w`, which is propositional.  Needed to instantiate
--   `gcdExt` at the carrier.
eqG-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ f : RTm Γ) →
          subTy σ (eqG μ f) ≡ eqG (subTm σ μ) (subTm σ f)
eqG-sub {σ = σ} μ f =
  cong₂ Π (gcdIH-sub μ)
    (cong₂ Π (trans (gcdIH-sub (w μ)) (cong gcdIH (sub-w {σ = σ} μ)))
      (cong₂ Π (trans (pwT-sub (w (w μ)) (var (vs vz)) (var vz))
                      (cong (λ u → pwT u (var (vs vz)) (var vz))
                            (sub-w² {σ = σ} μ)))
               (Id-cong₃ refl
                  (cong (λ z → app z (var (vs (vs vz)))) (sub-w³ {σ = σ} f))
                  (cong (λ z → app z (var (vs vz))) (sub-w³ {σ = σ} f)))))
