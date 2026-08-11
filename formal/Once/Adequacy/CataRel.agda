-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CataRel
--
-- Plan 0.58: the RELATIONAL `cataS` congruence — two folds of the SAME
-- `μS` value, with algebras that preserve a relation `R` over the
-- functor-lifted `RelSF R`, produce `R`-related results. This is the
-- "recurse on output" bridge for the `cata` case, now that the fold
-- carries `⟦_⟧ᴰ` (Plan 0.58 trace-preserving fold) so the relation
-- threads with NO reflexivity and NO carrier constraint.
------------------------------------------------------------------------

module Once.Adequacy.CataRel where

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; cataS; sfmapCata)

-- Functor-lifted relation: `SK`→equality (the constant is shared, since both
-- folds run over the SAME structure), `SId`→the carrier relation, structural.
RelSF : ∀ F {A₁ A₂ : Set} (R : A₁ → A₂ → Set) → ⟦ F ⟧SF A₁ → ⟦ F ⟧SF A₂ → Set
RelSF (SK A)   R x y = x ≡ y
RelSF SId      R x y = R x y
RelSF (F S⊕ G) R (inj₁ x) (inj₁ y) = RelSF F R x y
RelSF (F S⊕ G) R (inj₂ x) (inj₂ y) = RelSF G R x y
RelSF (F S⊕ G) R (inj₁ _) (inj₂ _) = ⊥
RelSF (F S⊕ G) R (inj₂ _) (inj₁ _) = ⊥
RelSF (F S⊗ G) R (x₁ , y₁) (x₂ , y₂) = RelSF F R x₁ x₂ × RelSF G R y₁ y₂

mutual
  -- Two folds of the SAME `μS F` value with `R`-preserving algebras are `R`-related.
  cataS-rel : ∀ {F} {A₁ A₂ : Set} (R : A₁ → A₂ → Set)
      {alg₁ : ⟦ F ⟧SF A₁ → A₁} {alg₂ : ⟦ F ⟧SF A₂ → A₂}
    → (∀ {y₁ y₂} → RelSF F R y₁ y₂ → R (alg₁ y₁) (alg₂ y₂))
    → (x : μS F) → R (cataS alg₁ x) (cataS alg₂ x)
  cataS-rel {F} R algR ⟨ x ⟩ = algR (sfmapCata-rel F R algR x)

  sfmapCata-rel : ∀ F' {F} {A₁ A₂ : Set} (R : A₁ → A₂ → Set)
      {alg₁ : ⟦ F ⟧SF A₁ → A₁} {alg₂ : ⟦ F ⟧SF A₂ → A₂}
    → (∀ {y₁ y₂} → RelSF F R y₁ y₂ → R (alg₁ y₁) (alg₂ y₂))
    → (x : ⟦ F' ⟧SF (μS F))
    → RelSF F' R (sfmapCata F' alg₁ x) (sfmapCata F' alg₂ x)
  sfmapCata-rel (SK B)    R algR x        = refl
  sfmapCata-rel SId       R algR x        = cataS-rel R algR x
  sfmapCata-rel (F' S⊕ G') R algR (inj₁ x) = sfmapCata-rel F' R algR x
  sfmapCata-rel (F' S⊕ G') R algR (inj₂ y) = sfmapCata-rel G' R algR y
  sfmapCata-rel (F' S⊗ G') R algR (x , y)  = (sfmapCata-rel F' R algR x , sfmapCata-rel G' R algR y)
