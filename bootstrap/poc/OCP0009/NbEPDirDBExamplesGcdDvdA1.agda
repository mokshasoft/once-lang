------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A1.
--
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdDvdA1 where

open import poc.OCP0009.NbEPDirDBExamplesGcdDvdL public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdLs public

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; RTy; RTm; El; Nat; Hom; Π
        ; var; nzero; nsuc; fst; snd; app; natrec; ⌜Nat⌝; Sub; subTm; subTy; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nsuc; ⊢fst; ⊢snd; ⊢app; ⊢natrec
        ; ⊢conv; _≅ᵀ_; csymᵀ; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢ )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; cong₃; cong₄ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN; reflN; ⊢reflN )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv; prvTm; prvOk; prv-cast )
open import poc.OCP0009.NbEPDirDBLibAmrecInd using ( IndStep )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( ⊢natrec-var )
open import poc.OCP0009.NbEPDirDBLibDvdArith using ( QCode; QCode-sub; QCode-conv )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; gcdIH; ⊢gcdIH
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt
  using ( μ₁; f₁; μ₂; f₂; μ₃; f₃; probe₁-s; probe₂-s
        ; red-β; gcdAt )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtE using ( gcdIH-sub )


-- ★ the substitution laws `indG` needs — mirrors of `pwT-sub`/`eqG-sub`
------------------------------------------------------------------------

indPWT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ i : RTm Γ) →
             subTy σ (indPWT μ i) ≡ indPWT (subTm σ μ) (subTm σ i)
indPWT-sub {σ = σ} μ i =
  cong₂ (λ u c → Π PairT (Π (Hom Nat (nsuc msr) u) (El c)))
        (sub-w {σ = σ} μ)
        (trans (QCode-sub {σ = extS (extS σ)}
                  (fst (var (vs vz))) (snd (var (vs vz)))
                  (app (app (w (w i)) (var (vs vz))) (var vz)))
               (cong (λ z → QCode (fst (var (vs vz))) (snd (var (vs vz)))
                                  (app (app z (var (vs vz))) (var vz)))
                     (sub-w² {σ = σ} i)))

indG-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ f u₁ u₂ : RTm Γ) →
           subTy σ (indG μ f u₁ u₂)
         ≡ indG (subTm σ μ) (subTm σ f) (subTm σ u₁) (subTm σ u₂)
indG-sub {σ = σ} μ f u₁ u₂ =
  cong₂ Π (gcdIH-sub μ)
    (cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                    (cong (λ u → indPWT u (var vz)) (sub-w {σ = σ} μ)))
             (cong El
                (trans (QCode-sub {σ = extS (extS σ)}
                          (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))
                       (cong₃ (λ a b z → QCode a b (app z (var (vs vz))))
                              (sub-w² {σ = σ} u₁) (sub-w² {σ = σ} u₂)
                              (sub-w² {σ = σ} f)))))

------------------------------------------------------------------------
-- ★ …and the elimination.
------------------------------------------------------------------------

indGElim : {Γ : Ctx} {μ f u₁ u₂ e i h : RTm ⌊ Γ ⌋} →
           Γ ⊢ e ∷ indG μ f u₁ u₂ → Γ ⊢ i ∷ gcdIH μ → Γ ⊢ h ∷ indPWT μ i →
           Γ ⊢ app (app e i) h ∷ El (QCode u₁ u₂ (app f i))
indGElim {μ = μ} {f = f} {u₁ = u₁} {u₂ = u₂} {i = i} {h = h} de di dh =
  ⊢-cast (cong El eq2) (⊢app (⊢-cast eq1 (⊢app de di)) dh)
  where
    p₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single i)) (w (w t)) ≡ w t
    p₁ t = trans (sub-w {σ = single i} (w t)) (cong w (wk-single {v = i} t))

    eq1 = cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                         (cong (λ u → indPWT u i) (wk-single {v = i} μ)))
                  (cong El
                     (trans (QCode-sub {σ = extS (single i)}
                               (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))
                            (cong₃ (λ a b z → QCode a b (app z (w i)))
                                   (p₁ u₁) (p₁ u₂) (p₁ f))))

    -- ⚠ FOUR slots, not three: the handle `i` is weakened here too.
    eq2 = trans (QCode-sub {σ = single h} (w u₁) (w u₂) (app (w f) (w i)))
                (cong₄ (λ a b z u → QCode a b (app z u))
                       (wk-single {v = h} u₁) (wk-single {v = h} u₂)
                       (wk-single {v = h} f) (wk-single {v = h} i))

