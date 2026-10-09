-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.GradedDomainLaws — the lemmas about `Once.Denotation.GradedDomain`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Denotation.GradedDomainLaws where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Type
open import Once.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; pure⊑)
import Once.Semantics.Machine as Val
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Functor.Translate using (translateF)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.ValueDomain using (νᵈ)
open import Once.Denotation.GradedDomain

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-β : ∀ {X Y : Set} (m : X) (k : X → Y) → (m >>=ᵖ k) ≡ k m
  >>=ᵖ-β m k = refl

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-assoc : ∀ {X Y Z : Set} (m : X) (f : X → Y) (g : Y → Z)
             → ((m >>=ᵖ f) >>=ᵖ g) ≡ (m >>=ᵖ λ x → f x >>=ᵖ g)
  >>=ᵖ-assoc m f g = refl

  >>=ᵖ-idʳ : ∀ {X : Set} (m : X) → (m >>=ᵖ λ x → x) ≡ m
  >>=ᵖ-idʳ m = refl

-- Left identity at every grade: definitional at `eff` (T's bind on a unit), the
-- β-law of the opaque bind at `pure`.
bindM-idˡ : ∀ π {X Y} (x : X) (k : X → M π Y) → bindM π (returnM π x) k ≡ k x

bindM-idˡ pure x k = >>=ᵖ-β x k

bindM-idˡ eff  x k = refl
