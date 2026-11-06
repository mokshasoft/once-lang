{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Categorical.Tools — what the combinator laws read with: no usage below every usage, sameness
-- at a pure arrow pointwise, and `idᶜ` typed once.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Categorical.Tools (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where


open import Data.Fin using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; 0≤q; 1≤ω)
open import Once.Spec.Type using (Ty; KCtx; TySub; _⟨_⟩; _⇒[_]_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; _∷_; []; Usage; zeroUsage; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (idᶜ; composeᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; bind; sub; T∞; _>>=∞_; return∞; _≈_; toT∞)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Erase Σ using (toT∞-bind; toT∞-sub)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; idʳ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; ≈-Relatedˡ; ≈-Relatedʳ; bindRel; returnRel; returnRel⁻; toObserved; fromObserved)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs; appMany; relPure⁻)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Strengthen Σ S using (pure⊑)
open import Once.Metatheory.Laws.Compose Σ u fmt S using (compᵛ; module CompV)
open import Once.Metatheory.Laws.Combinators Σ u fmt S using (pairᵛ; module CombV)
open import Once.Metatheory.Laws.Canon Σ S using (terminalD; initialD; inlD; inrD; fstD′; sndD′; applyD; composeD; pairD; curryD; caseD)
open import Once.Spec.Core.Derived using (terminalᶜ; initialᶜ; inlᶜ; inrᶜ; fstᶜ; sndᶜ; applyᶜ; pairᶜ; caseᶜ; curryᶜ)
open import Once.Spec.Type using (Unit; Void; _*_; _+_)
open import Once.Spec.Metatheory using (Pure)
open import Data.Sum using (inj₁; inj₂; [_,_]′)

-- Nothing is used below every usage.
zero⊑ : ∀ {n} (Ψ : Usage n) → zeroUsage ⊑ᵘ Ψ
zero⊑ []      = []
zero⊑ (q ∷ Ψ) = 0≤q ⊑∷ zero⊑ Ψ

zero⊑ω : ∀ {n} (Ψ : Usage n) → (zeroUsage +ᵘ Many *ᵘ zeroUsage) ⊑ᵘ Ψ
zero⊑ω []      = []
zero⊑ω (q ∷ Ψ) = 0≤q ⊑∷ zero⊑ω Ψ

-- Sameness at a pure arrow is sameness of the values, pointwise.
module _ {m : ℕ} (σ : TySub m 0) where
  toSameP : ∀ {X Y : Ty m} {h h′ : ⟦ (X ⇒[ mk-kind Many pure ] Y) ⟨ σ ⟩ ⟧ᵛ}
          → (∀ {x x′} → Same (X ⟨ σ ⟩) x x′ → Same (Y ⟨ σ ⟩) (h x) (h′ x′)) → Same ((X ⇒[ mk-kind Many pure ] Y) ⟨ σ ⟩) h h′
  toSameP k x x′ sx = toObserved (returnRel (k sx))

  fromSameP : ∀ {X Y : Ty m} {h h′ : ⟦ (X ⇒[ mk-kind Many pure ] Y) ⟨ σ ⟩ ⟧ᵛ}
            → Same ((X ⇒[ mk-kind Many pure ] Y) ⟨ σ ⟩) h h′ → ∀ {x x′} → Same (X ⟨ σ ⟩) x x′ → Same (Y ⟨ σ ⟩) (h x) (h′ x′)
  fromSameP s sx = returnRel⁻ (fromObserved (s _ _ sx))

module _ {m : ℕ} {Δ : KCtx m} where

  -- `idᶜ`, typed once and for all.
  idD : ∀ {n} {Γ : Ctx m n} (B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] idᶜ B π ∷ B ⇒[ mk-kind Many π ] B ! pure
  idD B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢var zero))
