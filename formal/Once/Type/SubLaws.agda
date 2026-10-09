-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.SubLaws — the lemmas about `Once.Type.Sub`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Type.SubLaws where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Type using (Type; rigid; Purity; pure; eff; mk-kind; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; _≟q_)
open import Once.Type.DecEq using (_≟F_; _≟T_)
open import Once.Type.Sub

⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

⊑π-unique ⊑-pure ⊑-pure = refl

⊑π-unique ⊑-eff  ⊑-eff  = refl

⊑π-unique ⊑-pe   ⊑-pe   = refl

⊑π-refl : ∀ π → π ⊑π π

⊑π-refl pure = ⊑-pure

⊑π-refl eff  = ⊑-eff

⊑π-trans : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃

⊑π-trans ⊑-pure g     = g

⊑π-trans ⊑-eff  ⊑-eff = ⊑-eff

⊑π-trans ⊑-pe   ⊑-eff = ⊑-pe

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

<:-refl : ∀ A → A <: A

<:-refl Unit   = sub-unit

<:-refl Void   = sub-void

<:-refl Int    = sub-int

<:-refl Float  = sub-float

<:-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:-refl A) (<:-refl B) (⊑π-refl π)

<:-refl (A * B) = sub-prod (<:-refl A) (<:-refl B)

<:-refl (A + B) = sub-sum (<:-refl A) (<:-refl B)

<:-refl (μ-type F) = sub-μ

<:-refl (ν-type F π) = sub-ν (⊑π-refl π)

<:-refl (rigid _ _) = sub-rigid

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
