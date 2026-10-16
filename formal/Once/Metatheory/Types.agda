{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Types — subtyping and the effect order are partial
-- orders with one derivation per pair (`Spec.Metatheory.Types`).
------------------------------------------------------------------------

module Once.Metatheory.Types where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade
  using (fin; Purity; pure; act; eff; mk-kind; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Type using (Ty; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Sub
open import Once.Spec.Metatheory using (Types)

⊑π-refl : ∀ π → π ⊑π π
⊑π-refl pure = ⊑-pure
⊑π-refl act  = ⊑-act
⊑π-refl eff  = ⊑-eff

⊑π-trans : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
⊑π-trans ⊑-pure g     = g
⊑π-trans ⊑-pa   ⊑-act = ⊑-pa
⊑π-trans ⊑-pa   ⊑-ae  = ⊑-pe
⊑π-trans ⊑-pe   ⊑-eff = ⊑-pe
⊑π-trans ⊑-act  g     = g
⊑π-trans ⊑-ae   ⊑-eff = ⊑-ae
⊑π-trans ⊑-eff  ⊑-eff = ⊑-eff

⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h
⊑π-unique ⊑-pure ⊑-pure = refl
⊑π-unique ⊑-pa   ⊑-pa   = refl
⊑π-unique ⊑-pe   ⊑-pe   = refl
⊑π-unique ⊑-act  ⊑-act  = refl
⊑π-unique ⊑-ae   ⊑-ae   = refl
⊑π-unique ⊑-eff  ⊑-eff  = refl

<:-refl : ∀ {m} (A : Ty m) → A <: A
<:-refl (var i)      = sub-var
<:-refl Unit         = sub-unit
<:-refl Void         = sub-void
<:-refl (A * B)      = sub-* (<:-refl A) (<:-refl B)
<:-refl (A + B)      = sub-+ (<:-refl A) (<:-refl B)
<:-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:-refl A) (<:-refl B) (⊑π-refl π)
<:-refl (μ F)        = sub-μ
<:-refl (ν F f)      = sub-ν (⊑π-refl (fin f))
<:-refl Int          = sub-int
<:-refl Float        = sub-float

<:-trans : ∀ {m} {A B C : Ty m} → A <: B → B <: C → A <: C
<:-trans sub-void        q               = sub-void
<:-trans sub-var         q               = q
<:-trans sub-unit        q               = q
<:-trans sub-int         q               = q
<:-trans sub-float       q               = q
<:-trans (sub-arr a b g) (sub-arr a′ b′ g′) = sub-arr (<:-trans a′ a) (<:-trans b b′) (⊑π-trans g g′)
<:-trans (sub-* a b)     (sub-* a′ b′)   = sub-* (<:-trans a a′) (<:-trans b b′)
<:-trans (sub-+ a b)     (sub-+ a′ b′)   = sub-+ (<:-trans a a′) (<:-trans b b′)
<:-trans sub-μ           q               = q
<:-trans (sub-ν g)       (sub-ν g′)      = sub-ν (⊑π-trans g g′)

<:-unique : ∀ {m} {A B : Ty m} (p q : A <: B) → p ≡ q
<:-unique sub-void        sub-void          = refl
<:-unique sub-var         sub-var           = refl
<:-unique sub-unit        sub-unit          = refl
<:-unique sub-int         sub-int           = refl
<:-unique sub-float       sub-float         = refl
<:-unique (sub-arr a b g) (sub-arr a′ b′ g′)
  rewrite <:-unique a a′ | <:-unique b b′ | ⊑π-unique g g′ = refl
<:-unique (sub-* a b)     (sub-* a′ b′)     = cong₂ sub-* (<:-unique a a′) (<:-unique b b′)
<:-unique (sub-+ a b)     (sub-+ a′ b′)     = cong₂ sub-+ (<:-unique a a′) (<:-unique b b′)
<:-unique sub-μ           sub-μ             = refl
<:-unique (sub-ν g)       (sub-ν g′)        = cong sub-ν (⊑π-unique g g′)

types : Types
types = record
  { <:-refl   = <:-refl
  ; <:-trans  = <:-trans
  ; <:-unique = <:-unique
  ; ⊑π-refl   = ⊑π-refl
  ; ⊑π-trans  = ⊑π-trans
  ; ⊑π-unique = ⊑π-unique
  }
