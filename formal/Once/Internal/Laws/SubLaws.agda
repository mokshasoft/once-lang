-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Laws.SubLaws — the lemmas about `Once.Type.Sub`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free). The
-- order laws are promised as `TypeSystem` in `Once.Spec.Metatheory` (D305).
------------------------------------------------------------------------

module Once.Internal.Laws.SubLaws where

open import Once.Spec.Type using (Ty)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Internal.Type.DecEq using (_≟q_)
open import Once.Internal.Type.DecEq using (_≟F_; _≟T_)
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub

⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h
⊑π-unique ⊑-pure ⊑-pure = refl
⊑π-unique ⊑-eff ⊑-eff = refl
⊑π-unique ⊑-pe ⊑-pe = refl
⊑π-unique ⊑-act ⊑-act = refl
⊑π-unique ⊑-pa ⊑-pa = refl
⊑π-unique ⊑-ae ⊑-ae = refl

⊑π-trans : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
⊑π-trans ⊑-pure ⊑-pure = ⊑-pure
⊑π-trans ⊑-pure ⊑-pe = ⊑-pe
⊑π-trans ⊑-pure ⊑-pa = ⊑-pa
⊑π-trans ⊑-eff ⊑-eff = ⊑-eff
⊑π-trans ⊑-pe ⊑-eff = ⊑-pe
⊑π-trans ⊑-act ⊑-act = ⊑-act
⊑π-trans ⊑-act ⊑-ae = ⊑-ae
⊑π-trans ⊑-pa ⊑-act = ⊑-pa
⊑π-trans ⊑-pa ⊑-ae = ⊑-pe
⊑π-trans ⊑-ae ⊑-eff = ⊑-ae

<:-unique : ∀ {m} {A B : Ty m} (p q : A <: B) → p ≡ q

<:-unique sub-void   sub-void   = refl

<:-unique sub-unit   sub-unit   = refl

<:-unique sub-int    sub-int    = refl

<:-unique sub-float  sub-float  = refl

<:-unique (sub-arr a b g) (sub-arr a′ b′ g′)
  rewrite <:-unique a a′ | <:-unique b b′ | ⊑π-unique g g′ = refl

<:-unique (sub-prod a b) (sub-prod a′ b′) = cong₂ sub-prod (<:-unique a a′) (<:-unique b b′)

<:-unique (sub-sum a b)  (sub-sum a′ b′)  = cong₂ sub-sum  (<:-unique a a′) (<:-unique b b′)

<:-unique sub-μ sub-μ = refl

<:-unique (sub-ν g) (sub-ν h) = cong sub-ν (⊑π-unique g h)

<:-unique sub-rigid sub-rigid = refl

<:-trans : ∀ {m} {A B C : Ty m} → A <: B → B <: C → A <: C

<:-trans sub-void   _          = sub-void

<:-trans sub-unit   q          = q

<:-trans sub-int    q          = q

<:-trans sub-float  q          = q

<:-trans (sub-arr a b g) (sub-arr a′ b′ g′) = sub-arr (<:-trans a′ a) (<:-trans b b′) (⊑π-trans g g′)

<:-trans (sub-prod a b)  (sub-prod a′ b′)   = sub-prod (<:-trans a a′) (<:-trans b b′)

<:-trans (sub-sum a b)   (sub-sum a′ b′)    = sub-sum  (<:-trans a a′) (<:-trans b b′)

<:-trans sub-μ q = q

<:-trans (sub-ν g) (sub-ν h) = sub-ν (⊑π-trans g h)

<:-trans sub-rigid q = q
