{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Context — typing contexts and usage vectors.
--
-- A context `Ctx m n` lists `n` variables typed over `m` type variables, each with a declared usage
-- quantity; variables are de Bruijn indices `Fin n`, `Fin.zero` the innermost.
-- A `Usage n` records how many times a term uses each variable; usages add
-- (`+ᵘ`, two subterms), scale (`*ᵘ`, a subterm under a binder used `q` times)
-- and join (`⊔ᵘ`, the branches of a case). `Γ ↾ Ψ` is the context of the
-- variables a usage actually uses: the environment a term's meaning receives.
------------------------------------------------------------------------
-- The contexts and usages ARE the Spec's (`Once.Spec.Context`): a binder
-- carries no quantity of its own — how a variable may be used is the usage
-- vector's business.

module Once.Internal.Context where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Type.Grade using (_⊔q_)
open import Once.Spec.Type using (Ty; Unit; _*_)
import Once.Spec.Context as S
open S using (Ctx; ∅; _▸_; lookup; Usage; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; []; _∷_; _⊑∷_)

pattern _,_ Γ A = Γ ▸ A

infixl 5 _,_

-- | Interpret a context as the (left-nested) product environment type.
--   (A₀,…,Aₙ₋₁) ↦ (…((Unit * A₀) * A₁) … * Aₙ₋₁). Pure `Ctx → Type` — it lives
--   here (with `Ctx`/`Type`), NOT in `Surface.Elaborate`, so the denotational
--   meaning can take it without importing the (operational) elaborator (0.47).
⟦_⟧ᶜ : ∀ {m n} → Ctx m n → Ty m
⟦ ∅ ⟧ᶜ     = Unit
⟦ Γ , A ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

-- | Join two usage vectors (the branches of a case).
_⊔ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[]        ⊔ᵘ []        = []
(q₁ ∷ ψ₁) ⊔ᵘ (q₂ ∷ ψ₂) = (q₁ ⊔q q₂) ∷ (ψ₁ ⊔ᵘ ψ₂)

infixl 55 _⊔ᵘ_

data SVar {m} : ∀ {n} → Ctx m n → Usage n → Ty m → Set where
  svar : ∀ {n} {Γ : Ctx m n} (i : Fin n) → SVar Γ (singleUse i One) (lookup Γ i)

-- | The variables a usage actually uses.
liveCount : ∀ {n} → Usage n → ℕ
liveCount []           = 0
liveCount (Zero ∷ Ψ)   = liveCount Ψ
liveCount (One  ∷ Ψ)   = ℕ.suc (liveCount Ψ)
liveCount (Many ∷ Ψ)   = ℕ.suc (liveCount Ψ)

_↾_ : ∀ {m n} → Ctx m n → (Ψ : Usage n) → Ctx m (liveCount Ψ)
∅       ↾ []         = ∅
(Γ , A) ↾ (Zero ∷ Ψ) = Γ ↾ Ψ
(Γ , A) ↾ (One  ∷ Ψ) = (Γ ↾ Ψ) , A
(Γ , A) ↾ (Many ∷ Ψ) = (Γ ↾ Ψ) , A

infixl 6 _↾_

-- | The usage order is the Spec's (`≤q`, pointwise `⊑ᵘ`); the six names below
--   spell its constructors at each pair of quantities.
pattern z≤z = 0≤q {Zero}
pattern z≤o = 0≤q {One}
pattern z≤m = 0≤q {Many}
pattern o≤o = 1≤1
pattern o≤m = 1≤ω
pattern m≤m = ω≤ω

⊑ᵘ-refl : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Ψ
⊑ᵘ-refl []           = []
⊑ᵘ-refl (Zero ∷ Ψ)   = z≤z ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (One  ∷ Ψ)   = o≤o ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (Many ∷ Ψ)   = m≤m ⊑∷ ⊑ᵘ-refl Ψ

-- | Each summand uses no more than the sum: the two witnesses every binary
--   elaborator clause needs to narrow the environment for its branches.
≤q'-+ˡ : ∀ (q r : Quantity) → q ≤q (q +q r)
≤q'-+ˡ Zero Zero = z≤z
≤q'-+ˡ Zero One  = z≤o
≤q'-+ˡ Zero Many = z≤m
≤q'-+ˡ One  Zero = o≤o
≤q'-+ˡ One  One  = o≤m
≤q'-+ˡ One  Many = o≤m
≤q'-+ˡ Many Zero = m≤m
≤q'-+ˡ Many One  = m≤m
≤q'-+ˡ Many Many = m≤m

≤q'-+ʳ : ∀ (q r : Quantity) → r ≤q (q +q r)
≤q'-+ʳ Zero Zero = z≤z
≤q'-+ʳ Zero One  = o≤o
≤q'-+ʳ Zero Many = m≤m
≤q'-+ʳ One  Zero = z≤o
≤q'-+ʳ One  One  = o≤m
≤q'-+ʳ One  Many = m≤m
≤q'-+ʳ Many Zero = z≤m
≤q'-+ʳ Many One  = o≤m
≤q'-+ʳ Many Many = m≤m

⊑ᵘ-+ˡ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ ⊑ᵘ (Ψ₁ +ᵘ Ψ₂)
⊑ᵘ-+ˡ []        []        = []
⊑ᵘ-+ˡ (q ∷ Ψ₁) (r ∷ Ψ₂)   = ≤q'-+ˡ q r ⊑∷ ⊑ᵘ-+ˡ Ψ₁ Ψ₂

⊑ᵘ-+ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ (Ψ₁ +ᵘ Ψ₂)
⊑ᵘ-+ʳ []        []        = []
⊑ᵘ-+ʳ (q ∷ Ψ₁) (r ∷ Ψ₂)   = ≤q'-+ʳ q r ⊑∷ ⊑ᵘ-+ʳ Ψ₁ Ψ₂

-- | Transitivity, and "scaling by a non-Zero quantity only grows usage".
--   Together with `⊑ᵘ-+ʳ` these give the argument's narrowing at `app`, whose
--   usage index is `Ψ₁ +ᵘ (q *ᵘ Ψ₂)` rather than a plain sum.
⊑q'-trans : ∀ {a b c} → a ≤q b → b ≤q c → a ≤q c
⊑q'-trans z≤z p    = z≤-any p
  where z≤-any : ∀ {c} → Zero ≤q c → Zero ≤q c
        z≤-any x = x
⊑q'-trans z≤o o≤o  = z≤o
⊑q'-trans z≤o o≤m  = z≤m
⊑q'-trans z≤m m≤m  = z≤m
⊑q'-trans o≤o o≤o  = o≤o
⊑q'-trans o≤o o≤m  = o≤m
⊑q'-trans o≤m m≤m  = o≤m
⊑q'-trans m≤m m≤m  = m≤m

⊑ᵘ-trans : ∀ {n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} → Ψ₁ ⊑ᵘ Ψ₂ → Ψ₂ ⊑ᵘ Ψ₃ → Ψ₁ ⊑ᵘ Ψ₃
⊑ᵘ-trans []        []        = []
⊑ᵘ-trans (p ⊑∷ ps) (r ⊑∷ rs)   = ⊑q'-trans p r ⊑∷ ⊑ᵘ-trans ps rs

⊑ᵘ-*One : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ (One *ᵘ Ψ)
⊑ᵘ-*One []           = []
⊑ᵘ-*One (Zero ∷ Ψ)   = z≤z ⊑∷ ⊑ᵘ-*One Ψ
⊑ᵘ-*One (One  ∷ Ψ)   = o≤o ⊑∷ ⊑ᵘ-*One Ψ
⊑ᵘ-*One (Many ∷ Ψ)   = m≤m ⊑∷ ⊑ᵘ-*One Ψ

⊑ᵘ-*Many : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ (Many *ᵘ Ψ)
⊑ᵘ-*Many []          = []
⊑ᵘ-*Many (Zero ∷ Ψ)  = z≤z ⊑∷ ⊑ᵘ-*Many Ψ
⊑ᵘ-*Many (One  ∷ Ψ)  = o≤m ⊑∷ ⊑ᵘ-*Many Ψ
⊑ᵘ-*Many (Many ∷ Ψ)  = m≤m ⊑∷ ⊑ᵘ-*Many Ψ

-- | Each branch's usage is below the join — the two narrowings `case'` needs,
--   since its index is `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`.
≤q'-⊔ˡ : ∀ (q r : Quantity) → q ≤q (q ⊔q r)
≤q'-⊔ˡ Zero Zero = z≤z
≤q'-⊔ˡ Zero One  = z≤o
≤q'-⊔ˡ Zero Many = z≤m
≤q'-⊔ˡ One  Zero = o≤o
≤q'-⊔ˡ One  One  = o≤o
≤q'-⊔ˡ One  Many = o≤m
≤q'-⊔ˡ Many Zero = m≤m
≤q'-⊔ˡ Many One  = m≤m
≤q'-⊔ˡ Many Many = m≤m

≤q'-⊔ʳ : ∀ (q r : Quantity) → r ≤q (q ⊔q r)
≤q'-⊔ʳ Zero Zero = z≤z
≤q'-⊔ʳ Zero One  = o≤o
≤q'-⊔ʳ Zero Many = m≤m
≤q'-⊔ʳ One  Zero = z≤o
≤q'-⊔ʳ One  One  = o≤o
≤q'-⊔ʳ One  Many = m≤m
≤q'-⊔ʳ Many Zero = z≤m
≤q'-⊔ʳ Many One  = o≤m
≤q'-⊔ʳ Many Many = m≤m

⊑ᵘ-⊔ˡ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ ⊑ᵘ (Ψ₁ ⊔ᵘ Ψ₂)
⊑ᵘ-⊔ˡ []       []       = []
⊑ᵘ-⊔ˡ (q ∷ Ψ₁) (r ∷ Ψ₂) = ≤q'-⊔ˡ q r ⊑∷ ⊑ᵘ-⊔ˡ Ψ₁ Ψ₂

⊑ᵘ-⊔ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ (Ψ₁ ⊔ᵘ Ψ₂)
⊑ᵘ-⊔ʳ []       []       = []
⊑ᵘ-⊔ʳ (q ∷ Ψ₁) (r ∷ Ψ₂) = ≤q'-⊔ʳ q r ⊑∷ ⊑ᵘ-⊔ʳ Ψ₁ Ψ₂

-- The order is proof-irrelevant: one proof per pair.
≤q'-unique : ∀ {q r} (a b : q ≤q r) → a ≡ b
≤q'-unique z≤z z≤z = refl
≤q'-unique z≤o z≤o = refl
≤q'-unique z≤m z≤m = refl
≤q'-unique o≤o o≤o = refl
≤q'-unique o≤m o≤m = refl
≤q'-unique m≤m m≤m = refl

⊑ᵘ-unique : ∀ {n} {Ψ Φ : Usage n} (u v : Ψ ⊑ᵘ Φ) → u ≡ v
⊑ᵘ-unique []       []       = refl
⊑ᵘ-unique (a ⊑∷ u) (b ⊑∷ v) = cong₂ _⊑∷_ (≤q'-unique a b) (⊑ᵘ-unique u v)
