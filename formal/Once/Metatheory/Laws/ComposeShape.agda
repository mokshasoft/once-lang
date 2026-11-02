{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.ComposeShape — what any derivation of `compose f g`
-- fixes about its arms: both are arrows (`f`'s codomain the closure's, `g`'s
-- codomain `f`'s domain), their latent grades are below the closure's, and an
-- `f` that erases its argument makes `g` effect-free (the erased argument
-- `app g x` is typed at `pure`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.ComposeShape (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.Spec.Grade
  using (Quantity; Zero; One; Many; mk-kind; Purity; pure; act; eff; _·p_; positionGrade;
         _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Type using (Ty; KCtx; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; Usage)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.Types using (⊑π-trans)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)
open import Once.Metatheory.Laws.Strengthen Σ S using (varTy; pure⊑)
open import Once.Metatheory.Laws.Tools Σ u fmt S using (peel; peeled; Peeled)

-- Below a sequence: each part (`_·p_` is the join of the chain).
⊑·ˡ : ∀ x y {z} → (x ·p y) ⊑π z → x ⊑π z
⊑·ˡ pure y e = ⊑π-trans (pure⊑ _) e
⊑·ˡ act pure e = e
⊑·ˡ act act e = e
⊑·ˡ act eff ⊑-eff = ⊑-ae
⊑·ˡ eff y e = e

⊑·ʳ : ∀ x y {z} → (x ·p y) ⊑π z → y ⊑π z
⊑·ʳ pure y e = e
⊑·ʳ act pure e = ⊑π-trans (pure⊑ act) e
⊑·ʳ act act e = e
⊑·ʳ act eff e = e
⊑·ʳ eff pure ⊑-eff = ⊑-pe
⊑·ʳ eff act ⊑-eff = ⊑-ae
⊑·ʳ eff eff ⊑-eff = ⊑-eff

⊑pure′ : ∀ {π} → π ⊑π pure → π ≡ pure
⊑pure′ ⊑-pure = refl

module _ {m : ℕ} {Δ : KCtx m} {n} {Γ : Ctx m n} where

  record Shape (A : Ty m) (π : Purity) (T : Ty m) (f g : Tm S m n) : Set where
    constructor shape
    field
      {B C}   : Ty m
      {qf qg} : Quantity
      {πf πg} : Purity
      eT      : T ≡ A ⇒[ mk-kind Many π ] C
      tyF     : ∀ {Ψ F π′} → Δ ⊩ Γ ⊢[ Ψ ] f ∷ F ! π′ → F ≡ B ⇒[ mk-kind qf πf ] C
      tyG     : ∀ {Ψ G π′} → Δ ⊩ Γ ⊢[ Ψ ] g ∷ G ! π′ → G ≡ A ⇒[ mk-kind qg πg ] B
      lf      : πf ⊑π π
      lg      : πg ⊑π π
      zp      : qf ≡ Zero → πg ≡ pure

  private
    lfOf : ∀ qf {π₁ π₂ πf π′} → (π₁ ·p positionGrade qf π₂ ·p πf) ⊑π π′ → πf ⊑π π′
    lfOf qf {π₁} {π₂} {πf} e = ⊑·ʳ (positionGrade qf π₂) πf (⊑·ʳ π₁ _ e)

    lgOf : ∀ qf q₂ {π₁ π₂ πf π′ σ₁ σ₂ πg} → (π₁ ·p positionGrade qf π₂ ·p πf) ⊑π π′
         → (σ₁ ·p positionGrade q₂ σ₂ ·p πg) ⊑π positionGrade qf π₂ → πg ⊑π π′
    lgOf Zero q₂ {π′ = π′} {σ₁} {σ₂} {πg} e e′ = ⊑π-trans (⊑·ʳ (positionGrade q₂ σ₂) πg (⊑·ʳ σ₁ _ e′)) (pure⊑ π′)
    lgOf One  q₂ {π₁} {π₂} {πf} {π′} {σ₁} {σ₂} {πg} e e′ =
      ⊑π-trans (⊑·ʳ (positionGrade q₂ σ₂) πg (⊑·ʳ σ₁ _ e′)) (⊑·ˡ π₂ πf (⊑·ʳ π₁ _ e))
    lgOf Many q₂ {π₁} {π₂} {πf} {π′} {σ₁} {σ₂} {πg} e e′ =
      ⊑π-trans (⊑·ʳ (positionGrade q₂ σ₂) πg (⊑·ʳ σ₁ _ e′)) (⊑·ˡ π₂ πf (⊑·ʳ π₁ _ e))

    zpOf : ∀ qf q₂ {π₂ σ₁ σ₂ πg} → (σ₁ ·p positionGrade q₂ σ₂ ·p πg) ⊑π positionGrade qf π₂ → qf ≡ Zero → πg ≡ pure
    zpOf Zero q₂ {σ₁ = σ₁} {σ₂} {πg} e′ refl = ⊑pure′ (⊑·ʳ (positionGrade q₂ σ₂) πg (⊑·ʳ σ₁ _ e′))
    zpOf One  q₂ e′ ()
    zpOf Many q₂ e′ ()

  compShape : ∀ {Ψa A π T π₀ f g} → Δ ⊩ Γ ⊢[ Ψa ] composeᶜ A π f g ∷ T ! π₀ → Shape A π T f g
  compShape d with peel d
  ... | peeled (⊢sub-use _ _) _ ()
  ... | peeled (⊢sub-eff _ _) _ ()
  ... | peeled (⊢let de db) _ _ with peel db
  ...   | peeled (⊢sub-use _ _) _ ()
  ...   | peeled (⊢sub-eff _ _) _ ()
  ...   | peeled (⊢let dw dl) _ _ with peel dl
  ...     | peeled (⊢sub-use _ _) _ ()
  ...     | peeled (⊢sub-eff _ _) _ ()
  ...     | peeled (⊢lam _ dt) _ _ with peel dt
  ...       | peeled (⊢sub-use _ _) _ ()
  ...       | peeled (⊢sub-eff _ _) _ ()
  ...       | peeled (⊢app {q = qf} {π = πf} {π₁} {π₂} df₃ dx₃) _ _ {grd} with varTy df₃
  ...         | refl with peel dx₃
  ...           | peeled (⊢sub-use _ _) _ ()
  ...           | peeled (⊢sub-eff _ _) _ ()
  ...           | peeled (⊢app {q = qg} {π = πg} {σ₁} {σ₂} df₄ dx₄) _ _ {grd′} with varTy df₄ | varTy dx₄
  ...             | refl | refl =
                    shape refl (λ df → ty-unique df de) (λ dg → ty-unique (wk-⊢ dg) dw)
                          (lfOf qf {π₁} {π₂} grd) (lgOf qf qg {π₁} {π₂} {πf} {σ₁ = σ₁} {σ₂} grd grd′) (zpOf qf qg {σ₁ = σ₁} {σ₂} grd′)
