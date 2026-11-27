-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — USAGE VECTORS (PLAN-GRADED §2, ROADMAP R5).
--
-- A usage `Usage Γ` says how often each variable of the scope `Γ` is
-- used (`Spec/Grade`). Usages add, scale and are ordered pointwise: a
-- term may claim more than it uses (affine). This is master's
-- `formal/Once/Spec/Context.agda` (`Usage n`, `zeroUsage`, `singleUse`,
-- `_+ᵘ_`, `_*ᵘ_`, `_⊑ᵘ_`), indexed here by the POC's scope `Cx` (a snoc
-- list, so a usage grows on the RIGHT, as the context does) instead of
-- a length.
--
-- The laws are the algebra the graded substitution lemma uses:
-- a commutative monoid under `+ᵘ` with unit `zeroUsage`, scaling an
-- action of the semiring that distributes over `+ᵘ`, `Zero` scaling to
-- `zeroUsage`, and every operation monotone in `⊑ᵘ`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Usage where
open import DirectedHoTT.Prelude using ( _≡_; refl; cong; trans )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import DirectedHoTT.Spec.Grade

------------------------------------------------------------------------
-- Usages
------------------------------------------------------------------------

infixl 5 _,_
data Usage : Cx → Set where
  []  : Usage ε
  _,_ : ∀ {Γ} → Usage Γ → Quantity → Usage (Γ ∙)

zeroUsage : ∀ {Γ} → Usage Γ
zeroUsage {ε}   = []
zeroUsage {Γ ∙} = zeroUsage , Zero

-- Variable `x` used `q` times, nothing else.
singleUse : ∀ {Γ} → Var Γ → Quantity → Usage Γ
singleUse vz     q = zeroUsage , q
singleUse (vs x) q = singleUse x q , Zero

-- The usage of variable `x`.
infixl 50 _!ᵘ_
_!ᵘ_ : ∀ {Γ} → Usage Γ → Var Γ → Quantity
(Ψ , q) !ᵘ vz   = q
(Ψ , _) !ᵘ vs x = Ψ !ᵘ x

infixl 60 _+ᵘ_
infixl 70 _*ᵘ_
infix 4 _⊑ᵘ_

_+ᵘ_ : ∀ {Γ} → Usage Γ → Usage Γ → Usage Γ
[]       +ᵘ []       = []
(Ψ₁ , p) +ᵘ (Ψ₂ , q) = (Ψ₁ +ᵘ Ψ₂) , (p +q q)

_*ᵘ_ : ∀ {Γ} → Quantity → Usage Γ → Usage Γ
q *ᵘ []      = []
q *ᵘ (Ψ , p) = (q *ᵘ Ψ) , (q *q p)

data _⊑ᵘ_ : ∀ {Γ} → Usage Γ → Usage Γ → Set where
  []  : [] ⊑ᵘ []
  _,_ : ∀ {Γ} {Ψ Ψ′ : Usage Γ} {p q} → Ψ ⊑ᵘ Ψ′ → p ≤q q → (Ψ , p) ⊑ᵘ (Ψ′ , q)

------------------------------------------------------------------------
-- A small congruence
------------------------------------------------------------------------

private
  cong₂, : ∀ {Γ} {Ψ Ψ′ : Usage Γ} {p p′} → Ψ ≡ Ψ′ → p ≡ p′ → (Ψ , p) ≡ (Ψ′ , p′)
  cong₂, refl refl = refl

------------------------------------------------------------------------
-- Addition: a commutative monoid with unit `zeroUsage`
------------------------------------------------------------------------

+ᵘ-identityˡ : ∀ {Γ} (Ψ : Usage Γ) → zeroUsage +ᵘ Ψ ≡ Ψ
+ᵘ-identityˡ []      = refl
+ᵘ-identityˡ (Ψ , q) = cong₂, (+ᵘ-identityˡ Ψ) refl

+ᵘ-identityʳ : ∀ {Γ} (Ψ : Usage Γ) → Ψ +ᵘ zeroUsage ≡ Ψ
+ᵘ-identityʳ []      = refl
+ᵘ-identityʳ (Ψ , q) = cong₂, (+ᵘ-identityʳ Ψ) (+q-identityʳ q)

+ᵘ-comm : ∀ {Γ} (Ψ₁ Ψ₂ : Usage Γ) → Ψ₁ +ᵘ Ψ₂ ≡ Ψ₂ +ᵘ Ψ₁
+ᵘ-comm []       []       = refl
+ᵘ-comm (Ψ₁ , p) (Ψ₂ , q) = cong₂, (+ᵘ-comm Ψ₁ Ψ₂) (+q-comm p q)

+ᵘ-assoc : ∀ {Γ} (Ψ₁ Ψ₂ Ψ₃ : Usage Γ) → (Ψ₁ +ᵘ Ψ₂) +ᵘ Ψ₃ ≡ Ψ₁ +ᵘ (Ψ₂ +ᵘ Ψ₃)
+ᵘ-assoc []       []       []       = refl
+ᵘ-assoc (Ψ₁ , p) (Ψ₂ , q) (Ψ₃ , r) = cong₂, (+ᵘ-assoc Ψ₁ Ψ₂ Ψ₃) (+q-assoc p q r)

------------------------------------------------------------------------
-- Scaling: an action of the semiring
------------------------------------------------------------------------

*ᵘ-identity : ∀ {Γ} (Ψ : Usage Γ) → One *ᵘ Ψ ≡ Ψ
*ᵘ-identity []      = refl
*ᵘ-identity (Ψ , q) = cong₂, (*ᵘ-identity Ψ) refl

*ᵘ-zeroˡ : ∀ {Γ} (Ψ : Usage Γ) → Zero *ᵘ Ψ ≡ zeroUsage
*ᵘ-zeroˡ []      = refl
*ᵘ-zeroˡ (Ψ , q) = cong₂, (*ᵘ-zeroˡ Ψ) refl

*ᵘ-zeroʳ : ∀ {Γ} q → q *ᵘ zeroUsage {Γ} ≡ zeroUsage
*ᵘ-zeroʳ {ε}   q = refl
*ᵘ-zeroʳ {Γ ∙} q = cong₂, (*ᵘ-zeroʳ q) (*q-zeroʳ q)

*ᵘ-assoc : ∀ {Γ} p q (Ψ : Usage Γ) → (p *q q) *ᵘ Ψ ≡ p *ᵘ (q *ᵘ Ψ)
*ᵘ-assoc p q []      = refl
*ᵘ-assoc p q (Ψ , r) = cong₂, (*ᵘ-assoc p q Ψ) (*q-assoc p q r)

*ᵘ-distrib-+ᵘ : ∀ {Γ} q (Ψ₁ Ψ₂ : Usage Γ) → q *ᵘ (Ψ₁ +ᵘ Ψ₂) ≡ (q *ᵘ Ψ₁) +ᵘ (q *ᵘ Ψ₂)
*ᵘ-distrib-+ᵘ q []       []       = refl
*ᵘ-distrib-+ᵘ q (Ψ₁ , p) (Ψ₂ , r) = cong₂, (*ᵘ-distrib-+ᵘ q Ψ₁ Ψ₂) (*q-distribˡ-+q q p r)

+q-distrib-*ᵘ : ∀ {Γ} p q (Ψ : Usage Γ) → (p +q q) *ᵘ Ψ ≡ (p *ᵘ Ψ) +ᵘ (q *ᵘ Ψ)
+q-distrib-*ᵘ p q []      = refl
+q-distrib-*ᵘ p q (Ψ , r) = cong₂, (+q-distrib-*ᵘ p q Ψ) (*q-distribʳ-+q r p q)

------------------------------------------------------------------------
-- Single uses and lookup
------------------------------------------------------------------------

*ᵘ-singleUse : ∀ {Γ} p (x : Var Γ) q → p *ᵘ singleUse x q ≡ singleUse x (p *q q)
*ᵘ-singleUse p vz     q = cong₂, (*ᵘ-zeroʳ p) refl
*ᵘ-singleUse p (vs x) q = cong₂, (*ᵘ-singleUse p x q) (*q-zeroʳ p)

zeroUsage-! : ∀ {Γ} (x : Var Γ) → zeroUsage !ᵘ x ≡ Zero
zeroUsage-! vz     = refl
zeroUsage-! (vs x) = zeroUsage-! x

+ᵘ-! : ∀ {Γ} (Ψ₁ Ψ₂ : Usage Γ) (x : Var Γ) → (Ψ₁ +ᵘ Ψ₂) !ᵘ x ≡ (Ψ₁ !ᵘ x) +q (Ψ₂ !ᵘ x)
+ᵘ-! (Ψ₁ , p) (Ψ₂ , q) vz     = refl
+ᵘ-! (Ψ₁ , p) (Ψ₂ , q) (vs x) = +ᵘ-! Ψ₁ Ψ₂ x

*ᵘ-! : ∀ {Γ} q (Ψ : Usage Γ) (x : Var Γ) → (q *ᵘ Ψ) !ᵘ x ≡ q *q (Ψ !ᵘ x)
*ᵘ-! q (Ψ , p) vz     = refl
*ᵘ-! q (Ψ , p) (vs x) = *ᵘ-! q Ψ x

------------------------------------------------------------------------
-- The order: a preorder, and every operation monotone in it
------------------------------------------------------------------------

⊑ᵘ-refl : ∀ {Γ} {Ψ : Usage Γ} → Ψ ⊑ᵘ Ψ
⊑ᵘ-refl {Ψ = []}    = []
⊑ᵘ-refl {Ψ = Ψ , q} = ⊑ᵘ-refl , ≤q-refl

⊑ᵘ-trans : ∀ {Γ} {Ψ₁ Ψ₂ Ψ₃ : Usage Γ} → Ψ₁ ⊑ᵘ Ψ₂ → Ψ₂ ⊑ᵘ Ψ₃ → Ψ₁ ⊑ᵘ Ψ₃
⊑ᵘ-trans []      []      = []
⊑ᵘ-trans (a , p) (b , q) = ⊑ᵘ-trans a b , ≤q-trans p q

-- `zeroUsage` is the bottom: an unused variable may be claimed at any usage.
zeroUsage-⊑ᵘ : ∀ {Γ} (Ψ : Usage Γ) → zeroUsage ⊑ᵘ Ψ
zeroUsage-⊑ᵘ []      = []
zeroUsage-⊑ᵘ (Ψ , q) = zeroUsage-⊑ᵘ Ψ , 0≤q

+ᵘ-mono : ∀ {Γ} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage Γ} → Ψ₁ ⊑ᵘ Ψ₁′ → Ψ₂ ⊑ᵘ Ψ₂′ → Ψ₁ +ᵘ Ψ₂ ⊑ᵘ Ψ₁′ +ᵘ Ψ₂′
+ᵘ-mono []      []      = []
+ᵘ-mono (a , p) (b , q) = +ᵘ-mono a b , +q-mono p q

*ᵘ-monoʳ : ∀ {Γ} q {Ψ Ψ′ : Usage Γ} → Ψ ⊑ᵘ Ψ′ → q *ᵘ Ψ ⊑ᵘ q *ᵘ Ψ′
*ᵘ-monoʳ q []      = []
*ᵘ-monoʳ q (a , p) = *ᵘ-monoʳ q a , *q-monoʳ q p

*ᵘ-monoˡ : ∀ {Γ} {p p′} (Ψ : Usage Γ) → p ≤q p′ → p *ᵘ Ψ ⊑ᵘ p′ *ᵘ Ψ
*ᵘ-monoˡ []      _ = []
*ᵘ-monoˡ (Ψ , q) a = *ᵘ-monoˡ Ψ a , *q-monoˡ q a
