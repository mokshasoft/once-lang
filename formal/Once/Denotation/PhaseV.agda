-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.PhaseV — the coherence laws of the runtime environment's
-- operations (`Once.Spec.Environment`).
------------------------------------------------------------------------

module Once.Denotation.PhaseV where

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Spec.Type.Grade using (Quantity; Zero; One; Many)
-- Imported from `Surface.Context` (the DEFINING module) rather than through
-- `Surface.Syntax`'s re-export: `_↾_` is recursive, and a recursive function
-- reached through a re-export does not always reduce at the use site.
open import Once.Spec.Context using (Ctx; Usage; lookup; _,_^_; ∅; ⟦_⟧ᶜ; _↾_; _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; singleUse; _∷_; [])
open import Once.Spec.Graded using (⟦_⟧ᵛ)
open import Once.Spec.Environment using (restrictᵛ; bindᵛ; eraseᵛ)

-- | THE COHERENCE that makes the factoring work: narrowing an already-erased
--   environment is the same as erasing at the smaller usage directly.
--
--       restrictᵛ le (eraseᵛ Γ Ψ dγ) ≡ eraseᵛ Γ Ψ' dγ      (le : Ψ' ⊑ᵘ Ψ)
--
--   Without it, a proof stated over the full environment cannot apply its own
--   induction hypothesis: the goal carries `restrictᵛ … (eraseᵛ Γ Ψ dγ)` while
--   the IH is about `eraseᵛ Γ Ψ' dγ`. With it, every clause of such a proof
--   goes through unchanged.
eraseᵛ-restrict : ∀ {n} (Γ : Ctx n) {Ψ Ψ' : Usage n} (le : Ψ' ⊑ᵘ Ψ)
                  (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᵛ)
                → restrictᵛ {Γ = Γ} le (eraseᵛ Γ Ψ dγ) ≡ eraseᵛ Γ Ψ' dγ
eraseᵛ-restrict ∅           ⊑[]            dγ = refl
eraseᵛ-restrict (Γ , A ^ q) (z≤z ⊑∷ ule) dγ = eraseᵛ-restrict Γ ule (proj₁ dγ)
eraseᵛ-restrict (Γ , A ^ q) (z≤o ⊑∷ ule) dγ = eraseᵛ-restrict Γ ule (proj₁ dγ)
eraseᵛ-restrict (Γ , A ^ q) (z≤m ⊑∷ ule) dγ = eraseᵛ-restrict Γ ule (proj₁ dγ)
eraseᵛ-restrict (Γ , A ^ q) (o≤o ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᵛ-restrict Γ ule (proj₁ dγ))
eraseᵛ-restrict (Γ , A ^ q) (o≤m ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᵛ-restrict Γ ule (proj₁ dγ))
eraseᵛ-restrict (Γ , A ^ q) (m≤m ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᵛ-restrict Γ ule (proj₁ dγ))

-- | The BINDER coherence, dual to `eraseᵛ-restrict`: erasing an environment that
--   has already been extended by a binder is the same as extending the erased
--   base with `bindᵛ`. Both sides case-split on `q`; with `q` a variable neither
--   reduces, so the equation has to be proved (three refls) rather than assumed.
eraseᵛ-bind : ∀ {n} (Γ : Ctx n) {A} (q : Quantity) (Ψ : Usage n)
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᵛ) (a : ⟦ A ⟧ᵛ)
            → eraseᵛ (Γ , A ^ Many) (q ∷ Ψ) (dγ , a)
                ≡ bindᵛ {Γ = Γ} {A = A} q (eraseᵛ Γ Ψ dγ) a
eraseᵛ-bind Γ Zero Ψ dγ a = refl
eraseᵛ-bind Γ One  Ψ dγ a = refl
eraseᵛ-bind Γ Many Ψ dγ a = refl

