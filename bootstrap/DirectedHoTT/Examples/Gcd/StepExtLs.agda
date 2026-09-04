------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`, part 2b: LEAF 4, ALONE.
--
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ And ONE MODULE PER LEAF: leaf 3 alone is 43s, but leaf 3 AND
--   leaf 4 together OOM.  Leaf 4 is the heavier — its `CERTˢ` goes
--   through `plusMonoLTm`, i.e. `trHomʳ`/`trHomˡ`/`commTm`/`congS`/`jsub`,
--   where leaf 3's `CERTᶻ` is just a `plusMonoTm` natrec.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.StepExtLs where
open import DirectedHoTT.Examples.Gcd.StepExtL public

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
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢; Ren⊢-ext; ren-ty; ren-lemma; ⊢[] )
open import DirectedHoTT.Lib.Amrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR
        ; subrenTy; aIHTat-ren; aIHTat-sub; idOfRed )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; sub-w²; sub-w³; ren-w )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT; asP )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import DirectedHoTT.Metatheory.RedCong
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
-- ★★★★ LEAF 4 — `a ∸ b = suc d`, i.e. `a > b`: recurse at `(a ∸ b , b)`.
--
-- ⭐ `natrec-suc` HANDS BACK `G3s` UNCHANGED.  The step substitutes the
--   natrec's predecessor and its IH into the successor branch, and `G3s`
--   uses NEITHER — its two free variables are `k'` and `n'`, three and five
--   slots further out.  So the branch is reached in one step and the leaf
--   is `β` plus one application of the hypothesis, exactly like leaf 3.
------------------------------------------------------------------------

red₃s : {Γ : Cx} {F : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)} → F ⟶* G3s →
        (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w F))) i ⟶* app (app i (w (w PAIRˢ))) (w (w CERTˢ))
red₃s r i =
  ⟶*-trans (⟶*-appˡ (⟶*-ren vs (⟶*-ren vs (⟶*-ren vs r))))
           (step (β _ i) done)

-- ⚠ EVERY PIECE OF LEAF 4 IS A TOP-LEVEL Def, and the `where` block it
--   came from is gone.  In a `where` the whole leaf elaborates as ONE term
--   and this module OOM-killed; behind names each piece is elaborated and
--   freed.  Leaf 3 needs no such treatment — its certificate is a
--   `plusMonoTm` natrec, leaf 4's goes through `jsub`.

private

  B₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  B₄ = plusTm (nsuc (var (vs (vs (vs vz)))))
              (nsuc (var (vs (vs (vs (vs (vs vz)))))))

  F₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  F₄ = subTm nrs f₃

  ⊢B₄ : {Γ : Ctx} → ((Θ₃ Γ ▹ Nat) ▹ M₃) ⊢ B₄ ∷ Nat
  ⊢B₄ = ⊢plus (⊢nsuc (⊢var (there (there (there here)))))
              (⊢nsuc (⊢var (there (there (there (there (there here)))))))

  rr₄ : {Γ : Cx} → subTm nrs (f₃ {Γ}) ⟶* G3s
  rr₄ = step (natrec-suc _ _ _) done

  Θ₄ : Ctx → Ctx
  Θ₄ Γ = ((((Θ₃ Γ ▹ Nat) ▹ M₃) ▹ gcdIH B₄) ▹ gcdIH (w B₄))
           ▹ pwT (w (w B₄)) (var (vs vz)) (var vz)

  idPrf₄ : {Γ : Ctx} →
           Prv (Θ₄ Γ)
               (Id (El ⌜Nat⌝) (app (w (w (w F₄))) (var (vs (vs vz))))
                              (app (w (w (w F₄))) (var (vs vz))))
  idPrf₄ = idOfRed (red₃s rr₄ (var (vs (vs vz)))) (red₃s rr₄ (var (vs vz)))
                   (prv _ (pwElim (⊢-cast (pwT-w _ _ _) (⊢var here))
                                  (⊢wk (⊢wk ⊢PAIRˢ))
                                  (⊢wk (⊢wk ⊢CERTˢ))))

leaf₃s : {Γ : Ctx} → Prv ((Θ₃ Γ ▹ Nat) ▹ M₃) (subTy nrs M₃)
leaf₃s =
  prv _ (⊢lam (⊢gcdIH ⊢B₄)
          (⊢lam (⊢gcdIH (⊢wk ⊢B₄))
            (⊢lam (⊢pwT (⊢wk (⊢wk ⊢B₄))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf₄))))
