{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapSem — what `Core.Derived.mapᶜ` means, on values: a
-- type's action in its 0th variable on a function, by the type's structure.
-- An arrow type is mapped by post-composition only when the variable is not
-- in its domain (`Cov`), the only case `mapᶜ` types; a functor's constants
-- are base types at both ends (as typing has them), so that `μ` values and
-- stream layers, compared by `≡`, compare as their parts do. The function is asked
-- for only where the variable occurs (`Occ T`, its covariant occurrences): where it does not,
-- typing does not fix the mapped arrow's type to `A → B`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Laws.MapSem (Σ : Signature) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Spec.Grade using (Zero; One; Many; mk-kind; fin)
open import Once.Spec.Type using (Ty; Fun; KCtx; Base; ⟦_⟧F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_;
                                  TySub; _⟨_⟩; _⟨_⟩F; at₀)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (M; fmap; νM; ana)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)

-- Where the 0th variable occurs covariantly: not through an arrow's domain
-- (where `mapᶜ` types, the variable is not there; `Cov`).
data Occ  {m : ℕ} : Ty (suc m) → Set
data OccF {m : ℕ} : Fun (suc m) → Set
data Occ where
  p-var : Occ (var zero)
  p-*ˡ  : ∀ {T₁ T₂} → Occ T₁ → Occ (T₁ * T₂)
  p-*ʳ  : ∀ {T₁ T₂} → Occ T₂ → Occ (T₁ * T₂)
  p-+ˡ  : ∀ {T₁ T₂} → Occ T₁ → Occ (T₁ + T₂)
  p-+ʳ  : ∀ {T₁ T₂} → Occ T₂ → Occ (T₁ + T₂)
  p-⇒ʳ  : ∀ {T₁ k T₂} → Occ T₂ → Occ (T₁ ⇒[ k ] T₂)
  p-μ   : ∀ {G} → OccF G → Occ (μ G)
  p-ν   : ∀ {G f} → OccF G → Occ (ν G f)
data OccF where
  p-K  : ∀ {C} → Occ C → OccF (K C)
  p-⊕ˡ : ∀ {F G} → OccF F → OccF (F ⊕ G)
  p-⊕ʳ : ∀ {F G} → OccF G → OccF (F ⊕ G)
  p-⊗ˡ : ∀ {F G} → OccF F → OccF (F ⊗ G)
  p-⊗ʳ : ∀ {F G} → OccF G → OccF (F ⊗ G)

module MapAt {m : ℕ} (Δ : KCtx m) (σ : TySub m 0) (A B : Ty m) where

  -- The variable is not in the domain of any arrow type `T` maps through.
  Cov  : Ty (suc m) → Set
  CovF : Fun (suc m) → Set
  Cov (var i)                 = ⊤
  Cov Unit                    = ⊤
  Cov Void                    = ⊤
  Cov Int                     = ⊤
  Cov Float                   = ⊤
  Cov (T₁ * T₂)               = Cov T₁ × Cov T₂
  Cov (T₁ + T₂)               = Cov T₁ × Cov T₂
  Cov (T₁ ⇒[ k ] T₂)          = (T₁ ⟨ at₀ A ⟩ ≡ T₁ ⟨ at₀ B ⟩) × Cov T₂
  Cov (μ G)                   = CovF G
  Cov (ν G f)                 = CovF G
  CovF (K C)   = Cov C × Base Δ (C ⟨ at₀ A ⟩) × Base Δ (C ⟨ at₀ B ⟩)
  CovF Id      = ⊤
  CovF (F ⊕ G) = CovF F × CovF G
  CovF (F ⊗ G) = CovF F × CovF G

  -- Values of `T` at `A`, at `B`; of a layer of `H`, at `A`, at `B`.
  VA VB : Ty (suc m) → Set
  VA T = ⟦ T ⟨ at₀ A ⟩ ⟨ σ ⟩ ⟧ᵛ
  VB T = ⟦ T ⟨ at₀ B ⟩ ⟨ σ ⟩ ⟧ᵛ
  CA CB : Fun (suc m) → SFunctor
  CA H = code (H ⟨ at₀ A ⟩F ⟨ σ ⟩F)
  CB H = code (H ⟨ at₀ B ⟩F ⟨ σ ⟩F)

  -- The function, where the variable occurs in `T`; in a layer of `H`.
  Fn : Ty (suc m) → Set
  Fn T = Occ T → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ
  FnF : Fun (suc m) → Set
  FnF H = OccF H → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ

  mutual
    mapS : ∀ T → Cov T → Fn T → VA T → VB T
    mapS (var zero)    c φ x = φ p-var x
    mapS (var (suc i)) c φ x = x
    mapS Unit          c φ x = x
    mapS Void          c φ x = x
    mapS Int           c φ x = x
    mapS Float         c φ x = x
    mapS (T₁ * T₂) (c₁ , c₂) φ (x , y) = mapS T₁ c₁ (λ o → φ (p-*ˡ o)) x , mapS T₂ c₂ (λ o → φ (p-*ʳ o)) y
    mapS (T₁ + T₂) (c₁ , c₂) φ (inj₁ x) = inj₁ (mapS T₁ c₁ (λ o → φ (p-+ˡ o)) x)
    mapS (T₁ + T₂) (c₁ , c₂) φ (inj₂ y) = inj₂ (mapS T₂ c₂ (λ o → φ (p-+ʳ o)) y)
    mapS (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c) φ g = λ u → fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (g u)
    mapS (T₁ ⇒[ mk-kind One  π ] T₂) (e , c) φ g =
      λ y → fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (g (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym e) y))
    mapS (T₁ ⇒[ mk-kind Many π ] T₂) (e , c) φ g =
      λ y → fmap π (mapS T₂ c (λ o → φ (p-⇒ʳ o))) (g (subst (λ X → ⟦ X ⟨ σ ⟩ ⟧ᵛ) (sym e) y))
    mapS (μ G)   c φ x = muMap G c (λ o → φ (p-μ o)) x
    mapS (ν G f) c φ x =
      ana f (CB G) (λ y → fmap (fin f) (nuLayer G c (λ o → φ (p-ν o)) {νM f (CA G)}) (outν y)) x

    -- μ: each layer's constants mapped, its recursive positions folded.
    muMap : ∀ G → CovF G → FnF G → μS (CA G) → μS (CB G)
    muMap G c φ (inS l) = inS (muLayer G G c φ c φ l)

    muLayer : ∀ G H → CovF G → FnF G → CovF H → FnF H
            → ⟦ CA H ⟧SF (μS (CA G)) → ⟦ CB H ⟧SF (μS (CB G))
    muLayer G (K C)     cG φG cH φ y = mapS C (proj₁ cH) (λ o → φ (p-K o)) y
    muLayer G Id        cG φG cH φ y = muMap G cG φG y
    muLayer G (H₁ ⊕ H₂) cG φG (c₁ , c₂) φ (inj₁ y) = inj₁ (muLayer G H₁ cG φG c₁ (λ o → φ (p-⊕ˡ o)) y)
    muLayer G (H₁ ⊕ H₂) cG φG (c₁ , c₂) φ (inj₂ y) = inj₂ (muLayer G H₂ cG φG c₂ (λ o → φ (p-⊕ʳ o)) y)
    muLayer G (H₁ ⊗ H₂) cG φG (c₁ , c₂) φ (y , z)  =
      muLayer G H₁ cG φG c₁ (λ o → φ (p-⊗ˡ o)) y , muLayer G H₂ cG φG c₂ (λ o → φ (p-⊗ʳ o)) z

    -- ν: each forced layer's constants mapped, its recursive positions kept as seeds.
    nuLayer : ∀ H → CovF H → FnF H → ∀ {X : Set} → ⟦ CA H ⟧SF X → ⟦ CB H ⟧SF X
    nuLayer (K C)     cH φ y = mapS C (proj₁ cH) (λ o → φ (p-K o)) y
    nuLayer Id        cH φ y = y
    nuLayer (H₁ ⊕ H₂) (c₁ , c₂) φ (inj₁ y) = inj₁ (nuLayer H₁ c₁ (λ o → φ (p-⊕ˡ o)) y)
    nuLayer (H₁ ⊕ H₂) (c₁ , c₂) φ (inj₂ y) = inj₂ (nuLayer H₂ c₂ (λ o → φ (p-⊕ʳ o)) y)
    nuLayer (H₁ ⊗ H₂) (c₁ , c₂) φ (y , z)  = nuLayer H₁ c₁ (λ o → φ (p-⊗ˡ o)) y , nuLayer H₂ c₂ (λ o → φ (p-⊗ʳ o)) z

  -- One layer of `H` at the value level (`mapLayerᶜ`): the constants mapped,
  -- the recursive positions, of type `R`, kept.
  layerS : ∀ (R : Ty m) H → CovF H → FnF H → ⟦ (⟦ H ⟨ at₀ A ⟩F ⟧F R) ⟨ σ ⟩ ⟧ᵛ → ⟦ (⟦ H ⟨ at₀ B ⟩F ⟧F R) ⟨ σ ⟩ ⟧ᵛ
  layerS R (K C)     c φ y = mapS C (proj₁ c) (λ o → φ (p-K o)) y
  layerS R Id        c φ y = y
  layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ (inj₁ y) = inj₁ (layerS R H₁ c₁ (λ o → φ (p-⊕ˡ o)) y)
  layerS R (H₁ ⊕ H₂) (c₁ , c₂) φ (inj₂ y) = inj₂ (layerS R H₂ c₂ (λ o → φ (p-⊕ʳ o)) y)
  layerS R (H₁ ⊗ H₂) (c₁ , c₂) φ (y , z)  = layerS R H₁ c₁ (λ o → φ (p-⊗ˡ o)) y , layerS R H₂ c₂ (λ o → φ (p-⊗ʳ o)) z
