-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Below — what `below` lists is strictly below
-- (plan 0.121 `complete`; the converse of `Principal.below-complete`).
--
-- Each type `below T` lists keeps `T`'s domains, lies under it, and is not
-- it (`below-sound`): so a body the Spec types at no type strictly below its
-- own is one the compiler's `PrincipalAt` admits.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Below where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind; fin)
import Once.Spec.Grade as G
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Internal.Type using (μ-type; ν-type)
open import Once.Spec.Sub using (_<:ᶜ_; subᶜ-void; subᶜ-arr; subᶜ-ν)
open import Once.Internal.Type.Sub using (<:ᶜ-refl; subᶜ-prod; subᶜ-sum)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Internal.Principal using (below; gradesBelow; finBelow)

private
  ⊑π-refl : ∀ π → π ⊑π π
  ⊑π-refl pure = ⊑-pure
  ⊑π-refl act  = ⊑-act
  ⊑π-refl eff  = ⊑-eff

  grade-below : ∀ {π′} π → π′ ∈ gradesBelow π → (π′ ⊑π π) × (π′ ≢ π)
  grade-below act (here refl)         = ⊑-pa , λ ()
  grade-below eff (here refl)         = ⊑-pe , λ ()
  grade-below eff (there (here refl)) = ⊑-ae , λ ()

  fin-below : ∀ {φ′} φ → φ′ ∈ finBelow φ → (fin φ′ ⊑π fin φ) × (φ′ ≢ φ)
  fin-below G.actᶠ (here refl) = ⊑-pa , λ ()

  -- a grade at or below
  at-or-below : ∀ {π′} π → π′ ∈ π ∷ gradesBelow π → π′ ⊑π π
  at-or-below π (here refl) = ⊑π-refl π
  at-or-below π (there m)   = proj₁ (grade-below π m)

  *-inj : ∀ {A B A′ B′ : Type} → A * B ≡ A′ * B′ → (A ≡ A′) × (B ≡ B′)
  *-inj refl = refl , refl
  +-inj : ∀ {A B A′ B′ : Type} → A + B ≡ A′ + B′ → (A ≡ A′) × (B ≡ B′)
  +-inj refl = refl , refl
  ⇒-inj : ∀ {A A′ B B′ : Type} {q q′ π π′} → (A ⇒[ mk-kind q π ] B) ≡ (A′ ⇒[ mk-kind q′ π′ ] B′) → (π ≡ π′) × (B ≡ B′)
  ⇒-inj refl = refl , refl
  ν-inj : ∀ {F F′ : Once.Spec.Type.Fun 0} {φ φ′} → ν-type F φ ≡ ν-type F′ φ′ → φ ≡ φ′
  ν-inj refl = refl

-- Each type `below T` lists is under `T`, and is not `T`.
below-sound : ∀ (T : Type) {X} → X ∈ below T → (X <:ᶜ T) × (X ≢ T)
private
  first : ∀ (A : Type) {x} → x ∈ A ∷ below A → x <:ᶜ A
below-sound Unit        (here refl) = subᶜ-void , λ ()
below-sound Int         (here refl) = subᶜ-void , λ ()
below-sound Float       (here refl) = subᶜ-void , λ ()
below-sound (μ-type F)  (here refl) = subᶜ-void , λ ()
below-sound (ν-type F φ) (here refl) = subᶜ-void , λ ()
below-sound (ν-type F φ) {X} (there m) = at (∈-map⁻ (ν-type F) m)
  where
    at : (Σ[ φ′ ∈ _ ] (φ′ ∈ finBelow φ) × (X ≡ ν-type F φ′)) → (X <:ᶜ ν-type F φ) × (X ≢ ν-type F φ)
    at (φ′ , m′ , refl) = let (g , n) = fin-below φ m′ in subᶜ-ν g , λ e → n (ν-inj e)
below-sound (A * B) (here refl) = subᶜ-void , λ ()
below-sound (A * B) {X} (there m) = cases (∈-++⁻ (cartesianProductWith _*_ (below A) (B ∷ [])) m)
  where
    Goal = (X <:ᶜ A * B) × (X ≢ A * B)
    one : (∃₂ λ x y → (x ∈ below A) × (y ∈ B ∷ []) × (X ≡ x * y)) → Goal
    one (x , .B , x∈ , here refl , refl) =
      let (sx , nx) = below-sound A x∈ in subᶜ-prod sx (<:ᶜ-refl B) , λ e → nx (proj₁ (*-inj e))
    two : (∃₂ λ x y → (x ∈ A ∷ below A) × (y ∈ below B) × (X ≡ x * y)) → Goal
    two (x , y , x∈ , y∈ , refl) =
      let (sy , ny) = below-sound B y∈ in subᶜ-prod (first A x∈) sy , λ e → ny (proj₂ (*-inj e))
    cases : (X ∈ cartesianProductWith _*_ (below A) (B ∷ [])) ⊎ (X ∈ cartesianProductWith _*_ (A ∷ below A) (below B)) → Goal
    cases (inj₁ m₁) = one (∈-cartesianProductWith⁻ _*_ (below A) (B ∷ []) m₁)
    cases (inj₂ m₂) = two (∈-cartesianProductWith⁻ _*_ (A ∷ below A) (below B) m₂)
below-sound (A + B) (here refl) = subᶜ-void , λ ()
below-sound (A + B) {X} (there m) = cases (∈-++⁻ (cartesianProductWith _+_ (below A) (B ∷ [])) m)
  where
    Goal = (X <:ᶜ A + B) × (X ≢ A + B)
    one : (∃₂ λ x y → (x ∈ below A) × (y ∈ B ∷ []) × (X ≡ x + y)) → Goal
    one (x , .B , x∈ , here refl , refl) =
      let (sx , nx) = below-sound A x∈ in subᶜ-sum sx (<:ᶜ-refl B) , λ e → nx (proj₁ (+-inj e))
    two : (∃₂ λ x y → (x ∈ A ∷ below A) × (y ∈ below B) × (X ≡ x + y)) → Goal
    two (x , y , x∈ , y∈ , refl) =
      let (sy , ny) = below-sound B y∈ in subᶜ-sum (first A x∈) sy , λ e → ny (proj₂ (+-inj e))
    cases : (X ∈ cartesianProductWith _+_ (below A) (B ∷ [])) ⊎ (X ∈ cartesianProductWith _+_ (A ∷ below A) (below B)) → Goal
    cases (inj₁ m₁) = one (∈-cartesianProductWith⁻ _+_ (below A) (B ∷ []) m₁)
    cases (inj₂ m₂) = two (∈-cartesianProductWith⁻ _+_ (A ∷ below A) (below B) m₂)
below-sound (A ⇒[ mk-kind q π ] B) (here refl) = subᶜ-void , λ ()
below-sound (A ⇒[ mk-kind q π ] B) {X} (there m) = cases (∈-++⁻ (cartesianProductWith f (gradesBelow π) (B ∷ [])) m)
  where
    f : Purity → Type → Type
    f π′ B′ = A ⇒[ mk-kind q π′ ] B′
    Goal = (X <:ᶜ A ⇒[ mk-kind q π ] B) × (X ≢ A ⇒[ mk-kind q π ] B)
    one : (∃₂ λ π′ y → (π′ ∈ gradesBelow π) × (y ∈ B ∷ []) × (X ≡ f π′ y)) → Goal
    one (π′ , .B , g∈ , here refl , refl) =
      let (g , n) = grade-below π g∈ in subᶜ-arr (<:ᶜ-refl B) g , λ e → n (proj₁ (⇒-inj e))
    two : (∃₂ λ π′ y → (π′ ∈ π ∷ gradesBelow π) × (y ∈ below B) × (X ≡ f π′ y)) → Goal
    two (π′ , y , g∈ , y∈ , refl) =
      let (sy , ny) = below-sound B y∈ in subᶜ-arr sy (at-or-below π g∈) , λ e → ny (proj₂ (⇒-inj e))
    cases : (X ∈ cartesianProductWith f (gradesBelow π) (B ∷ [])) ⊎ (X ∈ cartesianProductWith f (π ∷ gradesBelow π) (below B)) → Goal
    cases (inj₁ m₁) = one (∈-cartesianProductWith⁻ f (gradesBelow π) (B ∷ []) m₁)
    cases (inj₂ m₂) = two (∈-cartesianProductWith⁻ f (π ∷ gradesBelow π) (below B) m₂)

-- (a component at or below its own)
first A (here refl) = <:ᶜ-refl A
first A (there m′)  = proj₁ (below-sound A m′)
