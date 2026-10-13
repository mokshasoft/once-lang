-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.SubLaws — the lemmas about `Once.Type.Sub`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free). The
-- order laws are promised as `TypeSystem` in `Once.Spec.Metatheory` (D305).
------------------------------------------------------------------------

module Once.Metatheory.SubLaws where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff; prod; mk-kind)
open import Once.Spec.Type using (Type; rigid; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Spec.Type.DecEq using (_≟q_)
open import Once.Spec.Type.DecEq using (_≟F_; _≟T_)
open import Once.Spec.Type.Sub
open import Once.Type.Sub

⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h
⊑π-unique ⊑-pure ⊑-pure = refl
⊑π-unique ⊑-eff ⊑-eff = refl
⊑π-unique ⊑-pe ⊑-pe = refl
⊑π-unique ⊑-prod ⊑-prod = refl
⊑π-unique ⊑-pp ⊑-pp = refl
⊑π-unique ⊑-ep ⊑-ep = refl
⊑π-unique ⊑-g ⊑-g = refl
⊑π-unique ⊑-ge ⊑-ge = refl
⊑π-unique ⊑-gp ⊑-gp = refl

⊑π-trans : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
⊑π-trans ⊑-pure ⊑-pure = ⊑-pure
⊑π-trans ⊑-pure ⊑-pe = ⊑-pe
⊑π-trans ⊑-pure ⊑-pp = ⊑-pp
⊑π-trans ⊑-eff ⊑-eff = ⊑-eff
⊑π-trans ⊑-eff ⊑-ep = ⊑-ep
⊑π-trans ⊑-pe ⊑-eff = ⊑-pe
⊑π-trans ⊑-pe ⊑-ep = ⊑-pp
⊑π-trans ⊑-prod ⊑-prod = ⊑-prod
⊑π-trans ⊑-pp ⊑-prod = ⊑-pp
⊑π-trans ⊑-ep ⊑-prod = ⊑-ep
⊑π-trans ⊑-g ⊑-g = ⊑-g
⊑π-trans ⊑-g ⊑-ge = ⊑-ge
⊑π-trans ⊑-g ⊑-gp = ⊑-gp
⊑π-trans ⊑-ge ⊑-eff = ⊑-ge
⊑π-trans ⊑-ge ⊑-ep = ⊑-gp
⊑π-trans ⊑-gp ⊑-prod = ⊑-gp

<:-unique : ∀ {A B} (p q : A <: B) → p ≡ q

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

<:-trans : ∀ {A B C} → A <: B → B <: C → A <: C

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
