{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.MapFun — a type is a functor in its 0th variable, on
-- the effect-free arrows (`Spec.Metatheory.Categorical.map-idᶜ`,
-- `map-composeᶜ`): `mapᶜ` means the semantic map (`Laws.MapTop`), and the
-- semantic map preserves identities and composites (`Laws.MapLaws`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.MapFun (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Fin using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Many; mk-kind; pure)
open import Once.Spec.Type using (Ty; KCtx; _⟨_⟩; _⇒[_]_; at₀)
open import Once.Spec.Context using (Ctx)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived using (idᶜ; mapᶜ)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (return∞; toT∞)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Metatheory using (_≅_)
open import Once.Metatheory.Bisim Σ using (idˡ)
open import Once.Metatheory.Coherence.Relation Σ using (≈-Relatedˡ; returnRel)
open import Once.Metatheory.Coherence.Layer Σ using (rel; runs)
open import Once.Metatheory.Laws.Tools Σ u fmt S
open import Once.Metatheory.Laws.Views Σ u fmt S
open import Once.Metatheory.Laws.Categorical Σ u fmt S using (zero⊑; toSameP; fromSameP; idD)
open import Once.Metatheory.Laws.MapSem Σ using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)
open import Once.Metatheory.Laws.MapLaws Σ using (module MapId)
open import Once.Metatheory.Laws.MapTop Σ u fmt S using (module MapTopV)
open import Once.Metatheory.Laws.MapV Σ u fmt S using (module MapV)

module _ {m : ℕ} {Δ : KCtx m} where

  map-idᶜ : ∀ {n} {Γ : Ctx m n} {Ψ T A π₀}
            (d : Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A A (idᶜ A pure) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
            (d′ : Δ ⊩ Γ ⊢[ Ψ ] idᶜ (T ⟨ at₀ A ⟩) pure ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
          → _≅_ Σ fmt S d d′
  map-idᶜ {Γ = Γ} {Ψ} {T} {A} {π₀} d d′ δ sd σ r γ sγ =
    sameM {TT ⟨ σ ⟩} {π₀}
      (rel (~trans {TT} (MT.mapSem γ sγ T d base (idD A pure) r₀ Φ HΦ)
             (≈-Relatedˡ (idˡ idv _) (~trans {TT} (returnRel SAME) (~sym {TT} (runs (fl d′ (idD (T ⟨ at₀ A ⟩) pure) base r₀)))))))
    where
      open Views δ sd σ r γ sγ
      module MT = MapTopV δ sd σ r A A
      module MV = MapV δ sd σ r A A
      open MapAt Δ σ A A using (mapS; Fn)
      TT = T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩
      r₀ = resR base (zero⊑ Ψ)
      idv = ⟦ idD {Γ = Γ} A pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ)
      Φ : ⟦ (A ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩ ⟧ᵛ → Fn T
      Φ g o a = g a
      HΦ : ∀ {hv hv′} → Same ((A ⇒[ mk-kind Many pure ] A) ⟨ σ ⟩) hv hv′ → MV.HCall T (Φ hv′) (A ⇒[ mk-kind Many pure ] A) hv
      HΦ sh o refl a a′ sa = returnRel (fromSameP σ {X = A} {Y = A} sh sa)
      SAME : Same (TT ⟨ σ ⟩) (λ x → mapS T (MT.covD T d) (Φ idv) x)
                             (⟦ idD {Γ = Γ} (T ⟨ at₀ A ⟩) pure ⟧ δ σ r (restrict σ (zero⊑ Ψ) γ))
      SAME = toSameP σ {X = T ⟨ at₀ A ⟩} {Y = T ⟨ at₀ A ⟩}
               (λ {x} {x′} sx → MapId.mid σ r A T (MT.covD T d) {φ = Φ idv} (λ o a a′ sa → sa) {x} {x′} sx)
