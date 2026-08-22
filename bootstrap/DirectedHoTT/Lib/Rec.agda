------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — THE INDUCTION-HYPOTHESIS TYPES.
--
-- `(y : A) → μ y < μ x → P y`, shared by every WF combinator.  ★ It is
-- ONE type: measure recursion's IH and lexicographic recursion's `rec₁`
-- are the same, which is the main evidence that these are one abstraction
-- and not two.
--
-- ★★ D8 — `aIHTat` IS LOAD-BEARING AND MUST STAY NAMEABLE.  It is the IH
--   at an ARBITRARY bound, and a non-ℕ carrier forces you to need it:
--   `natrec` requires a ℕ, so the case split lands on the MEASURE rather
--   than the carrier, and then the IH's bound is the natrec VARIABLE, not
--   `μ x`.  The codes-and-functions interface could not say this (its
--   bound was always `app μ x`), which is why the pair-carrier use site
--   had to hand-write it there.
--
--   `aIHT` is then just `aIHTat` at the binder where the carrier variable
--   IS `x` — where `μ x` is the measure family itself.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Rec where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs; Ren
        ; RTy; El; Hom; Nat
        ; RTm; var; nsuc; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing using ( single )
open import DirectedHoTT.Lib.Wk
  using ( w; wᶠ; cong₄; sub-w; sub-w²; ren-w; ren-w²; wk-singleTy; wᶠ-single
        ; ren-wTy; ren-wᶠ )

aIHTat' : {Γ : Cx} (A : RTy Γ) (m mx : RTm (Γ ∙)) (cm : RTm ((Γ ∙) ∙)) → RTy Γ
aIHTat' A m mx cm = Π A (Π (Hom Nat (nsuc m) mx) (El cm))

aIHTat : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μx : RTm Γ) → RTy Γ
aIHTat A cM m μx = aIHTat' A m (w μx) (w cM)

aIHT : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) → RTy (Γ ∙)
aIHT A cM m = aIHTat (renTy vs A) (wᶠ cM) (wᶠ m) m

aIHT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
           renTy (extR ρ) (aIHT A cM m)
         ≡ aIHT (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
aIHT-ren {ρ = ρ} A cM m =
  cong₄ (λ a p q c → Π a (Π (Hom Nat (nsuc p) q) (El c)))
        (ren-wTy A) (ren-wᶠ m) (ren-w {ρ = extR ρ} m)
        (trans (ren-w {ρ = extR (extR ρ)} (wᶠ cM)) (cong w (ren-wᶠ cM)))

aIHT-fit : {Γ : Cx} {X : RTm Γ} (A : RTy Γ) (cM m : RTm (Γ ∙)) →
           subTy (single X) (aIHT A cM m)
         ≡ aIHTat A cM m (subTm (single X) m)
aIHT-fit {X = X} A cM m =
  cong₄ aIHTat' (wk-singleTy A) (wᶠ-single m) (sub-w m)
        (trans (sub-w {σ = extS (single X)} (wᶠ cM)) (cong w (wᶠ-single cM)))

------------------------------------------------------------------------
-- ★ THE ONE-MEASURE RECURSION TYPE — `(y : A) → μ₁ y < μ₁ x → P y`.
--
-- ⚠ MOVED HERE 2026-08-22 from `…ExamplesLexC`, where four live
--   amrec-track modules (`…ExamplesAmrecC`/`DivC`/`PairC`, and `AmrecT`
--   for the weakening kit alone) were importing it from an EXAMPLE.  A
--   library has no business living in an Examples file, and it is what
--   stopped the lexrec track from being separable at all.
--
-- ⭐ AND IT IS A FOURTH INSTANCE OF `…LibIHCall.ihCallT`:
--       rec1T' cA m₁ x' cp
--     = ihCallT (El cA) (app m₁ (var vz)) (app m₁ x') (El (app cp (var (vs vz))))
--   asserted by `refl` in `…ExamplesIHCallAgree`.  It cannot be DEFINED
--   that way here — `…LibIHCall` imports THIS module for `aIHTat'`, so the
--   dependency would be circular.  The assertion is the next best thing.
------------------------------------------------------------------------

rec1T' : {Γ : Cx} (cA : RTm Γ) (m₁ x' : RTm (Γ ∙)) (cp : RTm ((Γ ∙) ∙)) → RTy Γ
rec1T' cA m₁ x' cp =
  Π (El cA)
    (Π (Hom Nat (nsuc (app m₁ (var vz))) (app m₁ x'))
       (El (app cp (var (vs vz)))))

rec1T : {Γ : Cx} (cA cP μ₁ x : RTm Γ) → RTy Γ
rec1T cA cP μ₁ x = rec1T' cA (w μ₁) (w x) (w (w cP))

rec1T-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA cP μ₁ x : RTm Γ) →
            subTy σ (rec1T cA cP μ₁ x)
          ≡ rec1T (subTm σ cA) (subTm σ cP) (subTm σ μ₁) (subTm σ x)
rec1T-sub cA cP μ₁ x = cong₄ rec1T' refl (sub-w μ₁) (sub-w x) (sub-w² cP)

rec1T-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ x : RTm Γ) →
            renTy ρ (rec1T cA cP μ₁ x)
          ≡ rec1T (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ x)
rec1T-ren cA cP μ₁ x = cong₄ rec1T' refl (ren-w μ₁) (ren-w x) (ren-w² cP)
