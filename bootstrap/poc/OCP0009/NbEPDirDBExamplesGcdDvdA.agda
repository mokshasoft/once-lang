------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A.
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
module poc.OCP0009.NbEPDirDBExamplesGcdDvdA where

open import poc.OCP0009.NbEPDirDBExamplesGcdDvdL public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdLs public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA1 public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA2 public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA3 public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA4 public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA5 public

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


-- ★★★★★★ …AND `IndStep`, DISCHARGED.
------------------------------------------------------------------------

gcdIndStep : {Δ : Ctx} → IndStep Δ PairT ⌜Nat⌝ msr gcdStp gcdP
-- ⚠ `ρ` is BOUND and PASSED: `PAtR` is a defined function, so the ambient
--   renaming never solves from the goal.
gcdIndStep {Δ} {Θ} {ρ} hρ a ih da dih pw =
  prv-cast (cong El (sym (PAtR-gcd ρ a (app (app gcdStp a) ih))))
    (prv _ (⊢conv (indGElim (⊢-cast (indG-sub {σ = single a}
                                       msr gcdBody (fst (var vz)) (snd (var vz)))
                                    (⊢[] (prvOk gcdInd) da))
                            dih
                            (prvOk (indPWIntro (⊢plus (⊢fst da) (⊢snd da)) pw)))
                  (csymᵀ (QCode-conv (fst a) (snd a) (red-β a ih)))))
