------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`, part 2: THE TWO RECURSIVE LEAVES.
--
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.StepExtL where
open import DirectedHoTT.Examples.Gcd.StepExt public

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS; Id-cong₃
        ; subTy-renTy; renTy-subTy; subTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢app; ⊢nsuc; ⊢natrec
        ; ⊢fst; ⊢snd; ⊢nzero; ⊢idrefl; natrec-zero; natrec-suc
        ; ⊢conv; _≅ᵀ_; csymᵀ
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; ⊢⌜Nat⌝
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢; Ren⊢-ext; ren-ty; ren-lemma; ⊢[] )
open import DirectedHoTT.Lib.Amrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR
        ; subrenTy; aIHTat-ren; aIHTat-sub; idOfRed )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; sub-w²; sub-w³; ren-w )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT; asP )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; stepᵀ; doneᵀ; red→≅ᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import DirectedHoTT.Examples.Gcd.Step
  using ( gcdStp; gcdBody; msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1; ⊢gcdBody
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s; PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ
        ; PAIRˢ; ⊢PAIRˢ; CERTˢ; ⊢CERTˢ )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )


------------------------------------------------------------------------
-- ★★★★ LEAF 3 — `a ∸ b = 0`, i.e. `a ≤ b`: recurse at `(a , b ∸ a)`.
--       THE FIRST LEAF THAT USES THE HYPOTHESIS.
--
-- ⭐ AND IT IS ONE APPLICATION.  `G3z` reduces to `ih (PAIRᶻ) (CERTᶻ)`, the
--   Π-bound hypothesis is about the two IHs at the bound
--   `plusTm (nsuc k') (nsuc n')`, and `⊢CERTᶻ` is stated at EXACTLY that
--   bound.  Nothing is transported.  This is what carrying the IHs in the
--   motive bought — under the 2026-08-15 design the certificate would have
--   had to be rebuilt at `μ a` first.
------------------------------------------------------------------------

red₃z : {Γ : Cx} (sb : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w (natrec (G3z {Γ}) sb nzero)))) i
      ⟶* app (app i (w (w PAIRᶻ))) (w (w CERTᶻ))
red₃z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

-- ⚠ Same treatment as leaf 4: the `where` block is gone, every piece is a
--   top-level Def.  Measured: 43s as one term, and that was the CHEAP leaf.

private

  B₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  B₃ = plusTm (nsuc (var (vs vz))) (nsuc (var (vs (vs (vs vz)))))

  F₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  F₃ = subTm (single nzero) f₃

  ⊢B₃ : {Γ : Ctx} → Θ₃ Γ ⊢ B₃ ∷ Nat
  ⊢B₃ = ⊢plus (⊢nsuc (⊢var (there here)))
              (⊢nsuc (⊢var (there (there (there here)))))

  Θ₃' : Ctx → Ctx
  Θ₃' Γ = ((Θ₃ Γ ▹ gcdIH B₃) ▹ gcdIH (w B₃))
            ▹ pwT (w (w B₃)) (var (vs vz)) (var vz)

  idPrf₃ : {Γ : Ctx} →
           Prv (Θ₃' Γ)
               (Id (El ⌜Nat⌝) (app (w (w (w F₃))) (var (vs (vs vz))))
                              (app (w (w (w F₃))) (var (vs vz))))
  idPrf₃ = idOfRed (red₃z _ (var (vs (vs vz)))) (red₃z _ (var (vs vz)))
                   (prv _ (pwElim (⊢-cast (pwT-w _ _ _) (⊢var here))
                                  (⊢wk (⊢wk ⊢PAIRᶻ))
                                  (⊢wk (⊢wk ⊢CERTᶻ))))

leaf₃z : {Γ : Ctx} → Prv (Θ₃ Γ) (subTy (single nzero) M₃)
leaf₃z =
  prv _ (⊢lam (⊢gcdIH ⊢B₃)
          (⊢lam (⊢gcdIH (⊢wk ⊢B₃))
            (⊢lam (⊢pwT (⊢wk (⊢wk ⊢B₃))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf₃))))
