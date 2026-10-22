{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Context — typing contexts and usage vectors.
--
-- A context `Ctx n` lists `n` typed variables, each with a declared usage
-- quantity; variables are de Bruijn indices `Fin n`, `Fin.zero` the innermost.
-- A `Usage n` records how many times a term uses each variable; usages add
-- (`+ᵘ`, two subterms), scale (`*ᵘ`, a subterm under a binder used `q` times)
-- and join (`⊔ᵘ`, the branches of a case). `Γ ↾ Ψ` is the context of the
-- variables a usage actually uses: the environment a term's meaning receives.
------------------------------------------------------------------------

module Once.Internal.Context where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_)
open import Once.Type.Grade using (_⊔q_)
open import Once.Spec.Type using (Type; Unit; _*_)

-- | Typing context (de Bruijn indexed with quantities)
--
-- Ctx n represents a context with n variables.
-- Variables are indexed by Fin n (0 to n-1).
-- Each variable has a type and a quantity (usage annotation).
--
data Ctx : ℕ → Set where
  ∅   : Ctx 0
  _,_^_ : ∀ {n} → Ctx n → Type → Quantity → Ctx (ℕ.suc n)

infixl 5 _,_^_

-- | Smart constructor: extend context with unrestricted quantity
_,_ : ∀ {n} → Ctx n → Type → Ctx (ℕ.suc n)
Γ , A = Γ , A ^ Many

infixl 5 _,_

-- | Lookup type at position in context
lookup : ∀ {n} → Ctx n → Fin n → Type
lookup (Γ , A ^ q) Fin.zero    = A
lookup (Γ , _ ^ _) (Fin.suc i) = lookup Γ i

-- | Interpret a context as the (left-nested) product environment type.
--   (A₀,…,Aₙ₋₁) ↦ (…((Unit * A₀) * A₁) … * Aₙ₋₁). Pure `Ctx → Type` — it lives
--   here (with `Ctx`/`Type`), NOT in `Surface.Elaborate`, so the denotational
--   meaning can take it without importing the (operational) elaborator (0.47).
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ         = Unit
⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (ℕ.suc n)

infixr 5 _∷_

-- | Zero usage vector (all variables unused)
zeroUsage : ∀ {n} → Usage n
zeroUsage {0} = []
zeroUsage {ℕ.suc n} = Zero ∷ zeroUsage

-- | Single variable usage (one variable used with quantity q, rest unused)
singleUse : ∀ {n} → Fin n → Quantity → Usage n
singleUse {ℕ.suc n} Fin.zero    q = q ∷ zeroUsage
singleUse {ℕ.suc n} (Fin.suc i) q = Zero ∷ singleUse i q

-- | Add two usage vectors (combine usage from different branches)
_+ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[] +ᵘ [] = []
(q₁ ∷ ψ₁) +ᵘ (q₂ ∷ ψ₂) = (q₁ +q q₂) ∷ (ψ₁ +ᵘ ψ₂)

infixl 60 _+ᵘ_

-- | Scale usage vector by quantity (usage in a context scaled by q)
_*ᵘ_ : ∀ {n} → Quantity → Usage n → Usage n
q *ᵘ [] = []
q *ᵘ (q' ∷ ψ) = (q *q q') ∷ (q *ᵘ ψ)

infixl 70 _*ᵘ_

-- | Per-position maximum of two usage vectors (for case branches).
_⊔ᵘ_ : ∀ {n} → Usage n → Usage n → Usage n
[]        ⊔ᵘ []        = []
(q₁ ∷ ψ₁) ⊔ᵘ (q₂ ∷ ψ₂) = (q₁ ⊔q q₂) ∷ (ψ₁ ⊔ᵘ ψ₂)

infixl 55 _⊔ᵘ_

------------------------------------------------------------------------
-- A variable of the context, used once
------------------------------------------------------------------------
data SVar : ∀ {n} → Ctx n → Usage n → Type → Set where
  svar : ∀ {n} {Γ : Ctx n} (i : Fin n) → SVar Γ (singleUse i One) (lookup Γ i)

------------------------------------------------------------------------
-- Usage-restricted contexts
------------------------------------------------------------------------

-- The environment a subterm's meaning receives holds exactly the variables
-- the subterm uses, never everything bound so far: a variable it does not use
-- is not in its environment.

-- | How many variables a usage vector actually uses.
liveCount : ∀ {n} → Usage n → ℕ
liveCount []           = 0
liveCount (Zero ∷ Ψ)   = liveCount Ψ
liveCount (One  ∷ Ψ)   = ℕ.suc (liveCount Ψ)
liveCount (Many ∷ Ψ)   = ℕ.suc (liveCount Ψ)

-- | Restrict a context to the variables a usage vector uses. `Usage`'s head
--   is `Fin.zero`, which is the context's RIGHTMOST (innermost) binding, so
--   the two structures line up cons-for-cons.
_↾_ : ∀ {n} → Ctx n → (Ψ : Usage n) → Ctx (liveCount Ψ)
∅           ↾ []         = ∅
(Γ , A ^ q) ↾ (Zero ∷ Ψ) = Γ ↾ Ψ
(Γ , A ^ q) ↾ (One  ∷ Ψ) = (Γ ↾ Ψ) , A ^ q
(Γ , A ^ q) ↾ (Many ∷ Ψ) = (Γ ↾ Ψ) , A ^ q

infixl 6 _↾_

-- | The usage order `Zero ≤ One ≤ Many` as a relation (`_≤q_` in
--   `Spec.Type.Grade` is the same order as a Boolean test). Each constructor
--   names both quantities.
data _≤q'_ : Quantity → Quantity → Set where
  z≤z : Zero ≤q' Zero
  z≤o : Zero ≤q' One
  z≤m : Zero ≤q' Many
  o≤o : One  ≤q' One
  o≤m : One  ≤q' Many
  m≤m : Many ≤q' Many

-- | The pointwise order on usages: `Ψ ⊑ᵘ Φ` when `Ψ` uses each variable at
--   most as often as `Φ`. A subterm's environment is cut down from its
--   parent's along this order.
data _⊑ᵘ_ : ∀ {n} → Usage n → Usage n → Set where
  ⊑[] : [] ⊑ᵘ []
  _⊑∷_ : ∀ {n q r} {Ψ Φ : Usage n} → q ≤q' r → Ψ ⊑ᵘ Φ → (q ∷ Ψ) ⊑ᵘ (r ∷ Φ)

infixr 5 _⊑ᵘ_
infixr 5 _⊑∷_

------------------------------------------------------------------------
-- The narrowings the meaning uses: each part of a sum, scaling or join uses
-- at most what the whole does. (The core meaning cuts a subterm's
-- environment out of its parent's with these.)
------------------------------------------------------------------------

-- | The order is reflexive — every subterm may keep what it already has.
⊑ᵘ-refl : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Ψ
⊑ᵘ-refl []           = ⊑[]
⊑ᵘ-refl (Zero ∷ Ψ)   = z≤z ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (One  ∷ Ψ)   = o≤o ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (Many ∷ Ψ)   = m≤m ⊑∷ ⊑ᵘ-refl Ψ

-- | Each summand uses no more than the sum: the two witnesses every binary
--   elaborator clause needs to narrow the environment for its branches.
≤q'-+ˡ : ∀ (q r : Quantity) → q ≤q' (q +q r)
≤q'-+ˡ Zero Zero = z≤z
≤q'-+ˡ Zero One  = z≤o
≤q'-+ˡ Zero Many = z≤m
≤q'-+ˡ One  Zero = o≤o
≤q'-+ˡ One  One  = o≤m
≤q'-+ˡ One  Many = o≤m
≤q'-+ˡ Many Zero = m≤m
≤q'-+ˡ Many One  = m≤m
≤q'-+ˡ Many Many = m≤m

≤q'-+ʳ : ∀ (q r : Quantity) → r ≤q' (q +q r)
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
⊑ᵘ-+ˡ []        []        = ⊑[]
⊑ᵘ-+ˡ (q ∷ Ψ₁) (r ∷ Ψ₂)   = ≤q'-+ˡ q r ⊑∷ ⊑ᵘ-+ˡ Ψ₁ Ψ₂

⊑ᵘ-+ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ (Ψ₁ +ᵘ Ψ₂)
⊑ᵘ-+ʳ []        []        = ⊑[]
⊑ᵘ-+ʳ (q ∷ Ψ₁) (r ∷ Ψ₂)   = ≤q'-+ʳ q r ⊑∷ ⊑ᵘ-+ʳ Ψ₁ Ψ₂

-- | Transitivity, and "scaling by a non-Zero quantity only grows usage".
--   Together with `⊑ᵘ-+ʳ` these give the argument's narrowing at `app`, whose
--   usage index is `Ψ₁ +ᵘ (q *ᵘ Ψ₂)` rather than a plain sum.
⊑q'-trans : ∀ {a b c} → a ≤q' b → b ≤q' c → a ≤q' c
⊑q'-trans z≤z p    = z≤-any p
  where z≤-any : ∀ {c} → Zero ≤q' c → Zero ≤q' c
        z≤-any x = x
⊑q'-trans z≤o o≤o  = z≤o
⊑q'-trans z≤o o≤m  = z≤m
⊑q'-trans z≤m m≤m  = z≤m
⊑q'-trans o≤o o≤o  = o≤o
⊑q'-trans o≤o o≤m  = o≤m
⊑q'-trans o≤m m≤m  = o≤m
⊑q'-trans m≤m m≤m  = m≤m

⊑ᵘ-trans : ∀ {n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} → Ψ₁ ⊑ᵘ Ψ₂ → Ψ₂ ⊑ᵘ Ψ₃ → Ψ₁ ⊑ᵘ Ψ₃
⊑ᵘ-trans ⊑[]        ⊑[]        = ⊑[]
⊑ᵘ-trans (p ⊑∷ ps) (r ⊑∷ rs)   = ⊑q'-trans p r ⊑∷ ⊑ᵘ-trans ps rs

⊑ᵘ-*One : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ (One *ᵘ Ψ)
⊑ᵘ-*One []           = ⊑[]
⊑ᵘ-*One (Zero ∷ Ψ)   = z≤z ⊑∷ ⊑ᵘ-*One Ψ
⊑ᵘ-*One (One  ∷ Ψ)   = o≤o ⊑∷ ⊑ᵘ-*One Ψ
⊑ᵘ-*One (Many ∷ Ψ)   = m≤m ⊑∷ ⊑ᵘ-*One Ψ

⊑ᵘ-*Many : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ (Many *ᵘ Ψ)
⊑ᵘ-*Many []          = ⊑[]
⊑ᵘ-*Many (Zero ∷ Ψ)  = z≤z ⊑∷ ⊑ᵘ-*Many Ψ
⊑ᵘ-*Many (One  ∷ Ψ)  = o≤m ⊑∷ ⊑ᵘ-*Many Ψ
⊑ᵘ-*Many (Many ∷ Ψ)  = m≤m ⊑∷ ⊑ᵘ-*Many Ψ

-- | Each branch's usage is below the join — the two narrowings `case'` needs,
--   since its index is `Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)`.
≤q'-⊔ˡ : ∀ (q r : Quantity) → q ≤q' (q ⊔q r)
≤q'-⊔ˡ Zero Zero = z≤z
≤q'-⊔ˡ Zero One  = z≤o
≤q'-⊔ˡ Zero Many = z≤m
≤q'-⊔ˡ One  Zero = o≤o
≤q'-⊔ˡ One  One  = o≤o
≤q'-⊔ˡ One  Many = o≤m
≤q'-⊔ˡ Many Zero = m≤m
≤q'-⊔ˡ Many One  = m≤m
≤q'-⊔ˡ Many Many = m≤m

≤q'-⊔ʳ : ∀ (q r : Quantity) → r ≤q' (q ⊔q r)
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
⊑ᵘ-⊔ˡ []       []       = ⊑[]
⊑ᵘ-⊔ˡ (q ∷ Ψ₁) (r ∷ Ψ₂) = ≤q'-⊔ˡ q r ⊑∷ ⊑ᵘ-⊔ˡ Ψ₁ Ψ₂

⊑ᵘ-⊔ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ (Ψ₁ ⊔ᵘ Ψ₂)
⊑ᵘ-⊔ʳ []       []       = ⊑[]
⊑ᵘ-⊔ʳ (q ∷ Ψ₁) (r ∷ Ψ₂) = ≤q'-⊔ʳ q r ⊑∷ ⊑ᵘ-⊔ʳ Ψ₁ Ψ₂

