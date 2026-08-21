------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, SPLIT 3's `a ≤ b` LEAF.
--
-- ⚠⚠ ITS OWN MODULE, AND EVERY PIECE A TOP-LEVEL `Def`.  `…GcdStepExtA1`
--   records the measurement for the analogous leaf: split 3's leaves sit
--   at context depth 10, cost is ~1.7x per slot, and assembled as one term
--   with the motives in a `where` block the module OOM-KILLED after 2m18s.
--   Splitting into `Def`s was not enough — the FILE had to split too.
--   ⭐ Applied here from the start rather than after the kill.
--
-- ★ WHAT THIS LEAF IS.  `a ∸ b` is ZERO, so `gcd (a,b) = gcd (a , b ∸ a)`.
--   The IH gives `v ∣ a` and `v ∣ (b ∸ a)`; `gcdLeaf-le` turns those into
--   `v ∣ a ∧ v ∣ b` using `monusLe`.  ⚠ `monusPlus` is INAPPLICABLE here —
--   its premise is false at `a = b`, which this branch admits.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdDvdL where

open import poc.OCP0009.NbEPDirDBExamplesGcdDvd public

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; RTy; RTm; El; Nat; Hom
        ; var; nzero; nsuc; fst; snd; app; subTm; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢conv
        ; csymᵀ; _⟶*_; step; done; βfst; βsnd )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibPair using ( asN; PairT )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv; prvOk )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( QCode; QCode-conv; QCode-convU; ⊢Q-fst; ⊢Q-snd )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ; gcdIH; ⊢gcdIH; msr )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt
  using ( Θ₃; f₃; gcdIH-w; gcdIH-w²; appGcdIH )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtL using ( red₃z )

private

  -- the branch's own bound, at `Θ₃`
  B₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  B₃ = plusTm uA₃ uB₃

  ⊢B₃ : {Γ : Ctx} → Θ₃ Γ ⊢ B₃ ∷ Nat
  ⊢B₃ = ⊢plus (⊢nsuc (⊢var (there here)))
              (⊢nsuc (⊢var (there (there (there here)))))

  F₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  F₃ = subTm (single nzero) f₃

  -- ★ the equation slot IS the generalised `E` of `CΓz` — that is what the
  --   2026-08-21 generalisation bought, and why `⊢PAIRᶻ`/`⊢CERTᶻ` drop in.
  Θ₃E : Ctx → Ctx
  Θ₃E Γ = Θ₃ Γ ▹ IdN μAB nzero

  Θ₃L : Ctx → Ctx
  Θ₃L Γ = (Θ₃E Γ ▹ gcdIH (w B₃)) ▹ indPWT (w (w B₃)) (var vz)

  -- the three deep terms, named
  A₈ B₈ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  A₈ = w (w (w uA₃))
  B₈ = w (w (w uB₃))

  dA₈ : {Γ : Ctx} → Θ₃L Γ ⊢ A₈ ∷ Nat
  dA₈ = ⊢nsuc (⊢var (there (there (there (there here)))))

  dB₈ : {Γ : Ctx} → Θ₃L Γ ⊢ B₈ ∷ Nat
  dB₈ = ⊢nsuc (⊢var (there (there (there (there (there (there here)))))))

  dPAIR : {Γ : Ctx} → Θ₃L Γ ⊢ w (w PAIRᶻ) ∷ PairT
  dPAIR = ⊢wk (⊢wk ⊢PAIRᶻ)

  dCERT : {Γ : Ctx} → Θ₃L Γ ⊢ w (w CERTᶻ)
            ∷ Hom Nat (nsuc (subTm (single (w (w PAIRᶻ))) msr)) (w (w (w B₃)))
  dCERT = ⊢wk (⊢wk ⊢CERTᶻ)

  dIH : {Γ : Ctx} → Θ₃L Γ ⊢ var (vs vz) ∷ gcdIH (w (w (w B₃)))
  dIH = ⊢-cast (gcdIH-w² (w B₃)) (⊢var (there here))

  -- the IH's value at the recursive call
  dV : {Γ : Ctx} → Θ₃L Γ ⊢ app (app (var (vs vz)) (w (w PAIRᶻ))) (w (w CERTᶻ)) ∷ Nat
  dV = asN (appGcdIH dIH dPAIR dCERT)

  -- ★ the hypothesis, ELIMINATED at `(PAIRᶻ , CERTᶻ)` — the point where
  --   `IndPW` is finally spent.
  dcall : {Γ : Ctx} →
          Θ₃L Γ ⊢ app (app (var vz) (w (w PAIRᶻ))) (w (w CERTᶻ))
            ∷ El (QCode A₈ (monusTm B₈ A₈)
                    (app (app (var (vs vz)) (w (w PAIRᶻ))) (w (w CERTᶻ))))
  dcall =
    ⊢conv (indPWElim (⊢-cast (indPWT-w (w (w B₃)) (var vz)) (⊢var here))
                     dPAIR dCERT)
          (QCode-convU _ (step (βfst _ _) done) (step (βsnd _ _) done))

  dEq : {Γ : Ctx} → Θ₃L Γ ⊢ var (vs (vs vz)) ∷ IdN (monusTm A₈ B₈) nzero
  dEq = ⊢var (there (there here))

  inner : {Γ : Ctx} → Prv (Θ₃L Γ) (El (QCode A₈ B₈
                                        (app (w (w (w F₃))) (var (vs vz)))))
  inner =
    prv _ (⊢conv (prvOk (gcdLeaf-le dA₈ dB₈ dV dEq (⊢Q-fst dcall) (⊢Q-snd dcall)))
                 (csymᵀ (QCode-conv A₈ B₈ (red₃z _ (var (vs vz))))))

leafI₃z : {Γ : Ctx} → Prv (Θ₃ Γ) (subTy (single nzero) MI₃)
leafI₃z =
  prv _ (⊢lam (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there here)))
                              (⊢nsuc (⊢var (there (there (there here))))))
                      ⊢nzero)
          (⊢lam (⊢gcdIH (⊢wk ⊢B₃))
            (⊢lam (⊢indPWT (⊢wk (⊢wk ⊢B₃))
                           (⊢-cast (gcdIH-w (w B₃)) (⊢var here)))
                  (prvOk inner))))
