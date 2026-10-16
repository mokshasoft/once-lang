-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Laws.Order — the language's orders are partial orders
-- (plan 0.112 B6).
--
-- Reflexivity and transitivity were already proved (`Metatheory.SubLaws`,
-- `Spec.Context`); antisymmetry was not, for any order in the tree. It holds
-- for all three: subtyping `<:`, the effect order `⊑π`, and the pointwise
-- usage order `⊑ᵘ`.
------------------------------------------------------------------------

module Once.Lang.Laws.Order where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; isEquivalence)
open import Relation.Binary.Structures using (IsPartialOrder)
open import Once.Lang.Type.Grade using (Purity; pure; eff; mk-kind; eff⁺)
open import Once.Lang.Type using (Type; _*_; _+_)
open import Once.Lang.Type.Sub
  using ( _⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae; ⊑-g; ⊑-ge
        ; _<:_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-prod; sub-sum; sub-μ; sub-ν; sub-rigid )
open import Once.Lang.Context
  using (Usage; []; _∷_; _⊑ᵘ_; ⊑[]; _⊑∷_; ⊑ᵘ-refl; ⊑ᵘ-trans)
open import Once.Lang.Laws.SubLaws using (⊑π-trans; <:-trans)
open import Once.Lang.Type.Sub using (⊑π-refl; <:-refl)
open import Once.Lang.Laws.Grade using (≤q'-antisym)

------------------------------------------------------------------------
-- The effect order
------------------------------------------------------------------------

⊑π-antisym : ∀ {π π′} → π ⊑π π′ → π′ ⊑π π → π ≡ π′
⊑π-antisym ⊑-pure _ = refl
⊑π-antisym ⊑-eff _ = refl
⊑π-antisym ⊑-act _ = refl
⊑π-antisym ⊑-g _ = refl

purity-⊑-isPartialOrder : IsPartialOrder _≡_ _⊑π_
purity-⊑-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ { {π} refl → ⊑π-refl π }
    ; trans = ⊑π-trans }
  ; antisym = ⊑π-antisym }

------------------------------------------------------------------------
-- Subtyping
------------------------------------------------------------------------

<:-antisym : ∀ {A B} → A <: B → B <: A → A ≡ B
<:-antisym sub-void sub-void = refl
<:-antisym sub-unit sub-unit = refl
<:-antisym sub-int sub-int = refl
<:-antisym sub-float sub-float = refl
<:-antisym (sub-arr a b g) (sub-arr a′ b′ g′)
  rewrite <:-antisym a′ a | <:-antisym b b′ | ⊑π-antisym g g′ = refl
<:-antisym (sub-prod a b) (sub-prod a′ b′) = cong₂ _*_ (<:-antisym a a′) (<:-antisym b b′)
<:-antisym (sub-sum a b) (sub-sum a′ b′) = cong₂ _+_ (<:-antisym a a′) (<:-antisym b b′)
<:-antisym sub-μ sub-μ = refl
<:-antisym (sub-ν g) (sub-ν g′) rewrite ⊑π-antisym g g′ = refl
<:-antisym sub-rigid sub-rigid = refl

subtype-isPartialOrder : IsPartialOrder _≡_ _<:_
subtype-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ { {A} refl → <:-refl A }
    ; trans = <:-trans }
  ; antisym = <:-antisym }

------------------------------------------------------------------------
-- The pointwise usage order
------------------------------------------------------------------------

⊑ᵘ-antisym : ∀ {n} {Ψ Φ : Usage n} → Ψ ⊑ᵘ Φ → Φ ⊑ᵘ Ψ → Ψ ≡ Φ
⊑ᵘ-antisym ⊑[] ⊑[] = refl
⊑ᵘ-antisym (p ⊑∷ ps) (q ⊑∷ qs) = cong₂ _∷_ (≤q'-antisym p q) (⊑ᵘ-antisym ps qs)

usage-⊑-isPartialOrder : ∀ {n} → IsPartialOrder _≡_ (_⊑ᵘ_ {n})
usage-⊑-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ { {Ψ} refl → ⊑ᵘ-refl Ψ }
    ; trans = ⊑ᵘ-trans }
  ; antisym = ⊑ᵘ-antisym }
