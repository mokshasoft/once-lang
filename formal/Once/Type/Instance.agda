-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Instance — plan 0.103 phase 2a: the decider `instantiate` is
-- COMPLETE for the property `IsInstance` (every instance of a schema is
-- matched), which is what lets the elaborator decide the instance premise of
-- `t-var-poly-instantiate`.
--
-- Invariant of the accumulator: every binding agrees with the assignment θ
-- the target is an instance under. Matching an instance of `s` under θ
-- against a θ-consistent accumulator succeeds and stays θ-consistent.
------------------------------------------------------------------------

module Once.Type.Instance where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.String using (String)
import Data.String as Str
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type

------------------------------------------------------------------------
-- Structural equality is reflexive.
------------------------------------------------------------------------

quantityEqBool-refl : ∀ q → quantityEqBool q q ≡ true
quantityEqBool-refl Zero = refl
quantityEqBool-refl One  = refl
quantityEqBool-refl Many = refl

purityEqBool-refl : ∀ p → purityEqBool p p ≡ true
purityEqBool-refl pure = refl
purityEqBool-refl eff  = refl

mutual
  typeEqBool-refl : ∀ t → typeEqBool t t ≡ true
  typeEqBool-refl Unit = refl
  typeEqBool-refl Void = refl
  typeEqBool-refl Int = refl
  typeEqBool-refl Float = refl
  typeEqBool-refl Str = refl
  typeEqBool-refl Buffer = refl
  typeEqBool-refl (a * b) rewrite typeEqBool-refl a | typeEqBool-refl b = refl
  typeEqBool-refl (a + b) rewrite typeEqBool-refl a | typeEqBool-refl b = refl
  typeEqBool-refl (a ⇒[ mk-kind q p ] b)
    rewrite quantityEqBool-refl q | purityEqBool-refl p | typeEqBool-refl a | typeEqBool-refl b = refl
  typeEqBool-refl (μ-type f) = functorEqBool-refl f
  typeEqBool-refl (ν-type f p) rewrite purityEqBool-refl p = functorEqBool-refl f

  functorEqBool-refl : ∀ f → functorEqBool f f ≡ true
  functorEqBool-refl (K a) = typeEqBool-refl a
  functorEqBool-refl Id = refl
  functorEqBool-refl (f ⊕ g) rewrite functorEqBool-refl f | functorEqBool-refl g = refl
  functorEqBool-refl (f ⊗ g) rewrite functorEqBool-refl f | functorEqBool-refl g = refl

------------------------------------------------------------------------
-- θ-consistent accumulators.
------------------------------------------------------------------------

Consistent : (String → Type) → Subst → Set
Consistent θ s = ∀ x t → lookupSubst x s ≡ just t → t ≡ θ x

consistent-[] : ∀ θ → Consistent θ []
consistent-[] θ x t ()

consistent-∷ : ∀ θ s x → Consistent θ s → Consistent θ ((x , θ x) ∷ s)
consistent-∷ θ s x c y t eq with y Str.≟ x
... | yes refl with eq
...   | refl = refl
consistent-∷ θ s x c y t eq | no _ = c y t eq

Matches : (String → Type) → Maybe Subst → Set
Matches θ r = Σ Subst (λ s′ → (r ≡ just s′) × Consistent θ s′)
  where open import Data.Product using (_×_)

extend-ok : ∀ θ s x → Consistent θ s → Matches θ (extendSubst x (θ x) s)
extend-ok θ s x c with lookupSubst x s in eq
... | just t′ rewrite c x t′ eq | typeEqBool-refl (θ x) = s , refl , c
... | nothing = ((x , θ x) ∷ s) , refl , consistent-∷ θ s x c

bind-ok : ∀ θ (r : Maybe Subst) (k : Subst → Maybe Subst)
  → Matches θ r → (∀ s′ → Consistent θ s′ → Matches θ (k s′)) → Matches θ (maybe-bind k r)
bind-ok θ .(just s′) k (s′ , refl , c′) f = f s′ c′

mutual
  inst-ok : ∀ θ (p : PolyType) s → Consistent θ s → Matches θ (instantiateAcc p (substPoly θ p) s)
  inst-ok θ (PTVar x) s c = extend-ok θ s x c
  inst-ok θ PUnit   s c = s , refl , c
  inst-ok θ PVoid   s c = s , refl , c
  inst-ok θ PInt    s c = s , refl , c
  inst-ok θ PFloat  s c = s , refl , c
  inst-ok θ PStr    s c = s , refl , c
  inst-ok θ PBuffer s c = s , refl , c
  inst-ok θ (A P* B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (A P+ B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (A P⇒[ q ] B) s c rewrite quantityEqBool-refl q =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (PEff A B) s c =
    bind-ok θ (instantiateAcc A (substPoly θ A) s) (instantiateAcc B (substPoly θ B)) (inst-ok θ A s c) (λ s′ c′ → inst-ok θ B s′ c′)
  inst-ok θ (Pμ-type F) s c = instF-ok θ F s c
  inst-ok θ (Pν-type F pure) s c = instF-ok θ F s c
  inst-ok θ (Pν-type F eff)  s c = instF-ok θ F s c

  instF-ok : ∀ θ (F : PolyFunctor) s → Consistent θ s → Matches θ (instantiateFunctor F (substPolyF θ F) s)
  instF-ok θ (PK A) s c = inst-ok θ A s c
  instF-ok θ PId s c = s , refl , c
  instF-ok θ (F P⊕ G) s c =
    bind-ok θ (instantiateFunctor F (substPolyF θ F) s) (instantiateFunctor G (substPolyF θ G)) (instF-ok θ F s c) (λ s′ c′ → instF-ok θ G s′ c′)
  instF-ok θ (F P⊗ G) s c =
    bind-ok θ (instantiateFunctor F (substPolyF θ F) s) (instantiateFunctor G (substPolyF θ G)) (instF-ok θ F s c) (λ s′ c′ → instF-ok θ G s′ c′)

-- COMPLETENESS: every instance is matched.
instantiate-complete : ∀ (p : PolyType) (T : Type) → IsInstance p T → Σ Subst (λ σ → instantiate p T ≡ just σ)
instantiate-complete p .(substPoly θ p) (θ , refl) with inst-ok θ p [] (consistent-[] θ)
... | σ , eq , _ = σ , eq
