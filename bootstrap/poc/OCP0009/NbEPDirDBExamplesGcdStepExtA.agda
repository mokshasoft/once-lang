------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`, part 3g: StepExt, DISCHARGED.
--
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStepExtA where

open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt public
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA5 public

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
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm; ⊢monus )


-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

gcdStepExt : {Δ : Ctx} → StepExt Δ PairT ⌜Nat⌝ msr gcdStp
gcdStepExt hρ a ih₁ ih₂ da d₁ d₂ pw =
  idOfRed (red-β a ih₁) (red-β a ih₂)
          (prv _ (eqGElim (⊢-cast (eqG-sub {σ = single a} msr gcdBody)
                                  (⊢[] (prvOk gcdExt) da)) d₁ d₂
                          (prvOk (pwIntro (⊢plus (⊢fst da) (⊢snd da)) pw))))
