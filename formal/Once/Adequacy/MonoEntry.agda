-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MonoEntry — plan 0.103 6b leg F, plan 0.122: a MONOMORPHIC
-- entry means, in the telescope, exactly what its elaboration means.
--
-- The table means an entry at an instance through `ty-subst-⊢`; at arity 0
-- the instance substitutes for no variable (`TySubstZero.ty0`), so the
-- meaning is the derivation's own, up to the type equation `A ⟨ σ ⟩ ≡ A`.
-- (It replaces `CoreAbsSem`, the abstraction round trip at arity 0.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (TySub)

module Once.Adequacy.MonoEntry (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) (σ₀ : TySub 0 0) where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.Spec.Grade using (pure)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects)
open import Once.Spec.Context using (∅; [])
open import Once.Spec.Core.Typing Σ S
open import Once.Postulates using (extensionality)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ)
import Once.Spec.Core.Meaning Σ fmt S as SM
open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀ using (⟦_⟧ₛ)
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Core.TySubstZero Σ S using (⟨⟩-0; ⟪⟫-0; ty0)

private
  ⟦⟧-≅ : ∀ {Δ Δ′ : KCtx 0} {t t′ A A′} {d : Δ ⊩ ∅ ⊢[ [] ] t ∷ A ! pure} {d′ : Δ′ ⊩ ∅ ⊢[ [] ] t′ ∷ A′ ! pure}
       → Δ ≡ Δ′ → t ≡ t′ → A ≡ A′ → d ≅ d′ → (δ : SM.DefSem) → ⟦ d ⟧ₛ δ tt ≅ ⟦ d′ ⟧ₛ δ tt
  ⟦⟧-≅ refl refl refl H.refl δ = H.refl

  -- Two kinds over no variable are one.
  kinds-0 : (Δ Δ′ : KCtx 0) → Δ ≡ Δ′
  kinds-0 Δ Δ′ = extensionality λ ()

mono-entry-sem : ∀ (Δ Δ′ : KCtx 0) (σ : TySub 0 0) (r : Respects Δ Δ′ σ) {A : Ty 0} {t}
                   (D : Δ ⊩ ∅ ⊢[ [] ] t ∷ A ! pure) (δ : SM.DefSem)
               → subst (λ X → ⟦ X ⟧ᵛ) (⟨⟩-0 σ A) (⟦ TS.ty-subst-⊢ σ r D ⟧ₛ δ tt) ≡ ⟦ D ⟧ₛ δ tt
mono-entry-sem Δ Δ′ σ r {A} {t} D δ = go (kinds-0 Δ Δ′) r
  where
    go : ∀ {Δ″} (e : Δ ≡ Δ″) (r′ : Respects Δ Δ″ σ)
       → subst (λ X → ⟦ X ⟧ᵛ) (⟨⟩-0 σ A) (⟦ TS.ty-subst-⊢ σ r′ D ⟧ₛ δ tt) ≡ ⟦ D ⟧ₛ δ tt
    go refl r′ = H.≅-to-≡ (H.trans (H.≡-subst-removable (λ X → ⟦ X ⟧ᵛ) (⟨⟩-0 σ A) _)
                                   (⟦⟧-≅ refl (⟪⟫-0 σ t) (⟨⟩-0 σ A) (ty0 σ r′ D) δ))
