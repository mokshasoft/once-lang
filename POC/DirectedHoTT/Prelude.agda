-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- DirectedHoTT.Prelude: the minimal prelude (no external dependencies).
--
-- A verbatim copy of the "Minimal Prelude" section of the OCP-0004
-- normalizer's `normalizer.Syntax.Types`, which this tree imported until
-- 2026-11-26. The POC owns its copy, so it depends on nothing outside POC/.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Prelude where

------------------------------------------------------------------------
-- Minimal Prelude
------------------------------------------------------------------------

-- Propositional equality
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ {x} → x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B} →
        x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

-- Dependent pairs (Σ types)
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A ; snd : B fst

∃-syntax : ∀ {A : Set} → (A → Set) → Set
∃-syntax {A} B = Σ A B
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Non-dependent pairs
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- Disjoint sum (Either)
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Empty type (absurdity)
data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Unit type
record ⊤ : Set where
  constructor tt

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

-- Decision type
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

-- Inspect idiom for remembering with-pattern results
record Reveal_·_is_ {A B : Set} (f : A → B) (x : A) (y : B) : Set where
  constructor ⟪_⟫
  field eq : f x ≡ y

inspect : ∀ {A B : Set} (f : A → B) (x : A) → Reveal f · x is (f x)
inspect f x = ⟪ refl ⟫

