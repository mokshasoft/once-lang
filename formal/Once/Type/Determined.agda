-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Determined — plan 0.103 phase 2b: substitution sees a schema only
-- through its free variables, so a codomain whose variables occur in the
-- domain is DETERMINED by the domain's instance. This is what makes the
-- argument-driven rule `d-poly` a function of its given domain (mode
-- agreement), and `codVarsInDom?` decides its premise.
------------------------------------------------------------------------

module Once.Type.Determined where

open import Data.List using (List; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
import Data.String as Str
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Data.Product
import Data.List.Relation.Binary.Subset.DecPropositional as SubDec

open import Once.Type

------------------------------------------------------------------------
-- Agreement on the free variables is exactly equality of the substitutions.
------------------------------------------------------------------------

mutual
  agree-on : ∀ (θ θ′ : String → Type) (p : PolyType)
    → (∀ {x} → x ∈ ftv p → θ x ≡ θ′ x) → substPoly θ p ≡ substPoly θ′ p
  agree-on θ θ′ (PTVar x) h = h (here refl)
  agree-on θ θ′ PUnit   h = refl
  agree-on θ θ′ PVoid   h = refl
  agree-on θ θ′ PInt    h = refl
  agree-on θ θ′ PFloat  h = refl
  agree-on θ θ′ (A P* B) h =
    cong₂ _*_ (agree-on θ θ′ A (λ m → h (∈-++⁺ˡ m))) (agree-on θ θ′ B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  agree-on θ θ′ (A P+ B) h =
    cong₂ _+_ (agree-on θ θ′ A (λ m → h (∈-++⁺ˡ m))) (agree-on θ θ′ B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  agree-on θ θ′ (A P⇒[ q ] B) h =
    cong₂ (λ a b → a ⇒[ mk-kind q pure ] b)
      (agree-on θ θ′ A (λ m → h (∈-++⁺ˡ m))) (agree-on θ θ′ B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  agree-on θ θ′ (PEff A B) h =
    cong₂ (λ a b → a ⇒[ mk-kind Many eff ] b)
      (agree-on θ θ′ A (λ m → h (∈-++⁺ˡ m))) (agree-on θ θ′ B (λ m → h (∈-++⁺ʳ (ftv A) m)))
  agree-on θ θ′ (Pμ-type F) h = cong μ-type (agreeF-on θ θ′ F h)
  agree-on θ θ′ (Pν-type F π) h = cong (λ f → ν-type f π) (agreeF-on θ θ′ F h)

  agreeF-on : ∀ (θ θ′ : String → Type) (F : PolyFunctor)
    → (∀ {x} → x ∈ ftvF F → θ x ≡ θ′ x) → substPolyF θ F ≡ substPolyF θ′ F
  agreeF-on θ θ′ (PK A) h = cong K (agree-on θ θ′ A h)
  agreeF-on θ θ′ PId h = refl
  agreeF-on θ θ′ (F P⊕ G) h =
    cong₂ _⊕_ (agreeF-on θ θ′ F (λ m → h (∈-++⁺ˡ m))) (agreeF-on θ θ′ G (λ m → h (∈-++⁺ʳ (ftvF F) m)))
  agreeF-on θ θ′ (F P⊗ G) h =
    cong₂ _⊗_ (agreeF-on θ θ′ F (λ m → h (∈-++⁺ˡ m))) (agreeF-on θ θ′ G (λ m → h (∈-++⁺ʳ (ftvF F) m)))

private
  *-inj : ∀ {a b c d} → a * b ≡ c * d → (a ≡ c) Data.Product.× (b ≡ d)
  *-inj refl = refl Data.Product., refl
  +-inj : ∀ {a b c d} → a + b ≡ c + d → (a ≡ c) Data.Product.× (b ≡ d)
  +-inj refl = refl Data.Product., refl
  ⇒-inj : ∀ {a b c d k k′} → a ⇒[ k ] b ≡ c ⇒[ k′ ] d → (a ≡ c) Data.Product.× (b ≡ d)
  ⇒-inj refl = refl Data.Product., refl
  μ-inj : ∀ {f g} → μ-type f ≡ μ-type g → f ≡ g
  μ-inj refl = refl
  ν-inj : ∀ {f g π π′} → ν-type f π ≡ ν-type g π′ → f ≡ g
  ν-inj refl = refl
  K-inj : ∀ {a b} → K a ≡ K b → a ≡ b
  K-inj refl = refl
  ⊕-inj : ∀ {f g f′ g′} → f ⊕ g ≡ f′ ⊕ g′ → (f ≡ f′) Data.Product.× (g ≡ g′)
  ⊕-inj refl = refl Data.Product., refl
  ⊗-inj : ∀ {f g f′ g′} → f ⊗ g ≡ f′ ⊗ g′ → (f ≡ f′) Data.Product.× (g ≡ g′)
  ⊗-inj refl = refl Data.Product., refl

open import Data.Product using ()

mutual
  agree-from : ∀ (θ θ′ : String → Type) (p : PolyType)
    → substPoly θ p ≡ substPoly θ′ p → ∀ {x} → x ∈ ftv p → θ x ≡ θ′ x
  agree-from θ θ′ (PTVar y) e (here refl) = e
  agree-from θ θ′ (A P* B) e m = pair-from θ θ′ A B (*-inj e) m
  agree-from θ θ′ (A P+ B) e m = pair-from θ θ′ A B (+-inj e) m
  agree-from θ θ′ (A P⇒[ q ] B) e m = pair-from θ θ′ A B (⇒-inj e) m
  agree-from θ θ′ (PEff A B) e m = pair-from θ θ′ A B (⇒-inj e) m
  agree-from θ θ′ (Pμ-type F) e m = agreeF-from θ θ′ F (μ-inj e) m
  agree-from θ θ′ (Pν-type F π) e m = agreeF-from θ θ′ F (ν-inj e) m

  pair-from : ∀ (θ θ′ : String → Type) (A B : PolyType)
    → (substPoly θ A ≡ substPoly θ′ A) Data.Product.× (substPoly θ B ≡ substPoly θ′ B)
    → ∀ {x} → x ∈ ftv A ++ ftv B → θ x ≡ θ′ x
  pair-from θ θ′ A B (ea Data.Product., eb) m with ∈-++⁻ (ftv A) m
  ... | inj₁ ma = agree-from θ θ′ A ea ma
  ... | inj₂ mb = agree-from θ θ′ B eb mb

  agreeF-from : ∀ (θ θ′ : String → Type) (F : PolyFunctor)
    → substPolyF θ F ≡ substPolyF θ′ F → ∀ {x} → x ∈ ftvF F → θ x ≡ θ′ x
  agreeF-from θ θ′ (PK A) e m = agree-from θ θ′ A (K-inj e) m
  agreeF-from θ θ′ (F P⊕ G) e m = pairF-from θ θ′ F G (⊕-inj e) m
  agreeF-from θ θ′ (F P⊗ G) e m = pairF-from θ θ′ F G (⊗-inj e) m

  pairF-from : ∀ (θ θ′ : String → Type) (F G : PolyFunctor)
    → (substPolyF θ F ≡ substPolyF θ′ F) Data.Product.× (substPolyF θ G ≡ substPolyF θ′ G)
    → ∀ {x} → x ∈ ftvF F ++ ftvF G → θ x ≡ θ′ x
  pairF-from θ θ′ F G (ef Data.Product., eg) m with ∈-++⁻ (ftvF F) m
  ... | inj₁ mf = agreeF-from θ θ′ F ef mf
  ... | inj₂ mg = agreeF-from θ θ′ G eg mg

-- THE DETERMINACY: the domain's instance fixes the codomain's.
cod-determined : ∀ {sd sc : PolyType} → CodVarsInDom sd sc
  → ∀ (θ θ′ : String → Type) → substPoly θ sd ≡ substPoly θ′ sd → substPoly θ sc ≡ substPoly θ′ sc
cod-determined {sd} {sc} inc θ θ′ e = agree-on θ θ′ sc (λ m → agree-from θ θ′ sd e (inc m))

-- The decider of the premise.
codVarsInDom? : ∀ (sd sc : PolyType) → Dec (CodVarsInDom sd sc)
codVarsInDom? sd sc = SubDec._⊆?_ Str._≟_ (ftv sc) (ftv sd)

-- Is the schema an arrow schema? (The view the elaborator dispatches on.)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)

ArrowView : PolyType → Set
ArrowView s = Σ-syntax PolyType (λ sd → Σ-syntax PolyType (λ sc → Σ-syntax Purity (λ π′ → ArrowSchema s sd sc π′)))

arrowSchema? : (s : PolyType) → Maybe (ArrowView s)
arrowSchema? (sd P⇒[ Many ] sc) = just (sd , sc , pure , as-pure)
arrowSchema? (PEff sd sc)       = just (sd , sc , eff , as-eff)
arrowSchema? (_ P⇒[ Zero ] _)   = nothing
arrowSchema? (_ P⇒[ One ] _)    = nothing
arrowSchema? (PTVar _)          = nothing
arrowSchema? PUnit              = nothing
arrowSchema? PVoid              = nothing
arrowSchema? PInt               = nothing
arrowSchema? PFloat             = nothing
arrowSchema? (_ P* _)           = nothing
arrowSchema? (_ P+ _)           = nothing
arrowSchema? (Pμ-type _)        = nothing
arrowSchema? (Pν-type _ _)      = nothing

-- An arrow schema's instance at the domain `A` whose codomain is read off.
arrow-instance : ∀ {s sd sc π′} → ArrowSchema s sd sc π′ → ∀ (θ : String → Type) {A}
  → substPoly θ sd ≡ A → IsInstance s (A ⇒[ mk-kind Many π′ ] substPoly θ sc)
arrow-instance as-pure θ eθ = θ , cong (λ a → a ⇒[ mk-kind Many pure ] _) eθ
arrow-instance as-eff  θ eθ = θ , cong (λ a → a ⇒[ mk-kind Many eff ] _) eθ
