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
module poc.OCP0009.NbEPDirDBLibRec where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; Ren
        ; RTy; El; Hom; Nat
        ; RTm; var; nsuc
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType using ( single )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₄; sub-w; ren-w; wk-singleTy; wᶠ-single; ren-wTy; ren-wᶠ )

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
