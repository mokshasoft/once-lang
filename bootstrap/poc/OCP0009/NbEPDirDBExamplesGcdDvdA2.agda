------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A2.
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
module poc.OCP0009.NbEPDirDBExamplesGcdDvdA2 where

open import poc.OCP0009.NbEPDirDBExamplesGcdDvdL public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdLs public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA1 public

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


-- ★★ the three motives, typed
------------------------------------------------------------------------

⊢MI₁ : {Γ : Ctx} → ((Γ ▹ PairT) ▹ Nat) ⊢ty MI₁
⊢MI₁ = ⊢indG (⊢plus (⊢fst (⊢var (there here))) (⊢var here))
             (⊢natrec-var ⊢G1 ⊢G1z ⊢gcdInn1)
             (⊢fst (⊢var (there here))) (⊢var here)

⊢MI₂ : {Γ : Ctx} → (ΘI₂ Γ ▹ Nat) ⊢ty MI₂
⊢MI₂ = ⊢indG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))
             (⊢natrec-var ⊢G2 ⊢G2z ⊢gcdInn2)
             (⊢var here) (⊢nsuc (⊢var (there (there here))))

⊢MI₃ : {Γ : Ctx} → (ΘI₃ Γ ▹ Nat) ⊢ty MI₃
⊢MI₃ =
  ty-Π (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there here))))
                       (⊢nsuc (⊢var (there (there (there (there here)))))))
               (⊢var here))
       (⊢indG (⊢wk (⊢plus (⊢nsuc (⊢var (there (there here))))
                          (⊢nsuc (⊢var (there (there (there (there here))))))))
              (⊢wk (⊢natrec-var ⊢G3 ⊢G3z ⊢G3s))
              (⊢wk (⊢nsuc (⊢var (there (there here)))))
              (⊢wk (⊢nsuc (⊢var (there (there (there (there here))))))))

