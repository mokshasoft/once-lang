-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — the USAGE grades (PLAN-GRADED §2, ROADMAP R5).
--
-- How many times a variable is used, in the ordered semiring
--     0 ≤ 1 ≤ ω
-- (quantitative type theory, affine: `1` is AT MOST once). It is the least
-- semiring that separates "never run" (types, indices, proofs: what
-- extraction removes) from "run at most once" (what the linear core
-- owns) and "run freely".
--
-- The definitions are master's `formal/Once/Spec/Grade.agda`
-- (`origin/0.146-linear-core-4`), COPIED, not imported: the POC owns its
-- syntax. Names and tables are kept identical so the two stay comparable.
-- The effect chain (`pure ≤ act ≤ eff`) is not here yet: it arrives
-- with the first effectful former (PLAN-GRADED D3).
--
-- The laws below are the ones the graded substitution lemma uses (usages
-- add, scale and are ordered pointwise). Each is proved by exhausting the
-- three grades.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Grade where
open import DirectedHoTT.Prelude using ( _≡_; refl )

------------------------------------------------------------------------
-- The grades and their operations (master's tables)
------------------------------------------------------------------------

data Quantity : Set where
  Zero One Many : Quantity

-- The usage of two uses together.
_+q_ : Quantity → Quantity → Quantity
Zero +q q    = q
One  +q Zero = One
One  +q One  = Many
One  +q Many = Many
Many +q _    = Many

-- A use of usage `q`, inside a context used `p` times.
_*q_ : Quantity → Quantity → Quantity
Zero *q _    = Zero
One  *q q    = q
Many *q Zero = Zero
Many *q One  = Many
Many *q Many = Many

infixl 60 _+q_
infixl 70 _*q_

-- The order `0 ≤ 1 ≤ ω`: a use may claim more than it makes (affine).
-- One derivation per pair.
data _≤q_ : Quantity → Quantity → Set where
  0≤q : ∀ {q} → Zero ≤q q
  1≤1 : One ≤q One
  1≤ω : One ≤q Many
  ω≤ω : Many ≤q Many

infix 4 _≤q_

------------------------------------------------------------------------
-- Addition: a commutative monoid with unit `Zero`
------------------------------------------------------------------------

+q-identityˡ : ∀ q → Zero +q q ≡ q
+q-identityˡ _ = refl

+q-identityʳ : ∀ q → q +q Zero ≡ q
+q-identityʳ Zero = refl
+q-identityʳ One  = refl
+q-identityʳ Many = refl

+q-comm : ∀ p q → p +q q ≡ q +q p
+q-comm Zero Zero = refl
+q-comm Zero One  = refl
+q-comm Zero Many = refl
+q-comm One  Zero = refl
+q-comm One  One  = refl
+q-comm One  Many = refl
+q-comm Many Zero = refl
+q-comm Many One  = refl
+q-comm Many Many = refl

+q-assoc : ∀ p q r → (p +q q) +q r ≡ p +q (q +q r)
+q-assoc Zero q    r    = refl
+q-assoc One  Zero r    = refl
+q-assoc One  One  Zero = refl
+q-assoc One  One  One  = refl
+q-assoc One  One  Many = refl
+q-assoc One  Many r    = refl
+q-assoc Many q    r    = refl

------------------------------------------------------------------------
-- Multiplication: a commutative monoid with unit `One`; `Zero` annihilates
------------------------------------------------------------------------

*q-identityˡ : ∀ q → One *q q ≡ q
*q-identityˡ _ = refl

*q-identityʳ : ∀ q → q *q One ≡ q
*q-identityʳ Zero = refl
*q-identityʳ One  = refl
*q-identityʳ Many = refl

*q-zeroˡ : ∀ q → Zero *q q ≡ Zero
*q-zeroˡ _ = refl

*q-zeroʳ : ∀ q → q *q Zero ≡ Zero
*q-zeroʳ Zero = refl
*q-zeroʳ One  = refl
*q-zeroʳ Many = refl

*q-comm : ∀ p q → p *q q ≡ q *q p
*q-comm Zero Zero = refl
*q-comm Zero One  = refl
*q-comm Zero Many = refl
*q-comm One  Zero = refl
*q-comm One  One  = refl
*q-comm One  Many = refl
*q-comm Many Zero = refl
*q-comm Many One  = refl
*q-comm Many Many = refl

*q-assoc : ∀ p q r → (p *q q) *q r ≡ p *q (q *q r)
*q-assoc Zero q    r    = refl
*q-assoc One  q    r    = refl
*q-assoc Many Zero r    = refl
*q-assoc Many One  r    = refl
*q-assoc Many Many Zero = refl
*q-assoc Many Many One  = refl
*q-assoc Many Many Many = refl

------------------------------------------------------------------------
-- Distributivity (the semiring)
------------------------------------------------------------------------

*q-distribˡ-+q : ∀ p q r → p *q (q +q r) ≡ (p *q q) +q (p *q r)
*q-distribˡ-+q Zero q    r    = refl
*q-distribˡ-+q One  q    r    = refl
*q-distribˡ-+q Many Zero r    = refl
*q-distribˡ-+q Many One  Zero = refl
*q-distribˡ-+q Many One  One  = refl
*q-distribˡ-+q Many One  Many = refl
*q-distribˡ-+q Many Many Zero = refl
*q-distribˡ-+q Many Many One  = refl
*q-distribˡ-+q Many Many Many = refl

*q-distribʳ-+q : ∀ p q r → (q +q r) *q p ≡ (q *q p) +q (r *q p)
*q-distribʳ-+q Zero Zero Zero = refl
*q-distribʳ-+q Zero Zero One  = refl
*q-distribʳ-+q Zero Zero Many = refl
*q-distribʳ-+q Zero One  Zero = refl
*q-distribʳ-+q Zero One  One  = refl
*q-distribʳ-+q Zero One  Many = refl
*q-distribʳ-+q Zero Many Zero = refl
*q-distribʳ-+q Zero Many One  = refl
*q-distribʳ-+q Zero Many Many = refl
*q-distribʳ-+q One  q    r    = lemma q r
  where
  lemma : ∀ q r → (q +q r) *q One ≡ (q *q One) +q (r *q One)
  lemma Zero r    = refl
  lemma One  Zero = refl
  lemma One  One  = refl
  lemma One  Many = refl
  lemma Many Zero = refl
  lemma Many One  = refl
  lemma Many Many = refl
*q-distribʳ-+q Many Zero r    = refl
*q-distribʳ-+q Many One  Zero = refl
*q-distribʳ-+q Many One  One  = refl
*q-distribʳ-+q Many One  Many = refl
*q-distribʳ-+q Many Many Zero = refl
*q-distribʳ-+q Many Many One  = refl
*q-distribʳ-+q Many Many Many = refl

------------------------------------------------------------------------
-- The order: a partial order, and both operations are monotone in it
------------------------------------------------------------------------

≤q-refl : ∀ {q} → q ≤q q
≤q-refl {Zero} = 0≤q
≤q-refl {One}  = 1≤1
≤q-refl {Many} = ω≤ω

≤q-trans : ∀ {p q r} → p ≤q q → q ≤q r → p ≤q r
≤q-trans 0≤q _   = 0≤q
≤q-trans 1≤1 b   = b
≤q-trans 1≤ω ω≤ω = 1≤ω
≤q-trans ω≤ω ω≤ω = ω≤ω

≤q-antisym : ∀ {p q} → p ≤q q → q ≤q p → p ≡ q
≤q-antisym 0≤q 0≤q = refl
≤q-antisym 1≤1 1≤1 = refl
≤q-antisym ω≤ω ω≤ω = refl

-- `Many` is the top: every use may be claimed as unrestricted.
≤q-ω : ∀ q → q ≤q Many
≤q-ω Zero = 0≤q
≤q-ω One  = 1≤ω
≤q-ω Many = ω≤ω

+q-monoˡ : ∀ {p p′} q → p ≤q p′ → p +q q ≤q p′ +q q
+q-monoˡ {p′ = p′} q 0≤q = lemma p′ q
  where
  lemma : ∀ p′ q → q ≤q p′ +q q
  lemma Zero q    = ≤q-refl
  lemma One  Zero = 0≤q
  lemma One  One  = 1≤ω
  lemma One  Many = ω≤ω
  lemma Many q    = ≤q-ω q
+q-monoˡ q 1≤1 = ≤q-refl
+q-monoˡ Zero 1≤ω = 1≤ω
+q-monoˡ One  1≤ω = ω≤ω
+q-monoˡ Many 1≤ω = ω≤ω
+q-monoˡ q ω≤ω = ω≤ω

+q-mono : ∀ {p p′ q q′} → p ≤q p′ → q ≤q q′ → p +q q ≤q p′ +q q′
+q-mono {p} {p′} {q} {q′} a b =
  ≤q-trans (+q-monoˡ q a) (≤q-subst (+q-comm q p′) (+q-comm q′ p′) (+q-monoˡ p′ b))
  where
  ≤q-subst : ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → x ≤q y → x′ ≤q y′
  ≤q-subst refl refl c = c

*q-monoˡ : ∀ {p p′} q → p ≤q p′ → p *q q ≤q p′ *q q
*q-monoˡ q 0≤q = 0≤q
*q-monoˡ q 1≤1 = ≤q-refl
*q-monoˡ Zero 1≤ω = 0≤q
*q-monoˡ One  1≤ω = 1≤ω
*q-monoˡ Many 1≤ω = ω≤ω
*q-monoˡ q ω≤ω = ≤q-refl

*q-monoʳ : ∀ p {q q′} → q ≤q q′ → p *q q ≤q p *q q′
*q-monoʳ Zero _   = 0≤q
*q-monoʳ One  b   = b
*q-monoʳ Many 0≤q = 0≤q
*q-monoʳ Many 1≤1 = ω≤ω
*q-monoʳ Many 1≤ω = ω≤ω
*q-monoʳ Many ω≤ω = ω≤ω
