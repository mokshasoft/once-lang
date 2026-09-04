-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Context — the IR-FREE typing-context / QTT-usage core.
--
-- Extracted from `Once.Surface.Syntax` (Plan 0.58, OCP-0006) so that the
-- context machinery (`Ctx`/`Usage`/`⟦_⟧ᶜ`/`lookup`) is available WITHOUT the
-- `Once.IR` import that `Surface.Syntax`'s `Expr` needs (only its
-- `lift-morphism`/`morph-app` leaves carry `IR`). This is what lets the typing
-- judgment and the direct denotation `⟦_⟧ᵈ` be genuinely IR-free.
--
-- `Surface.Syntax` re-exports this module (`open … public`), so its consumers
-- are unchanged; spec/denotation modules import THIS directly to stay IR-free.
------------------------------------------------------------------------

module Once.Surface.Context where

open import Once.Type
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; _∧_)

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

-- | Lookup quantity at position in context
lookupQuantity : ∀ {n} → Ctx n → Fin n → Quantity
lookupQuantity (Γ , A ^ q) Fin.zero    = q
lookupQuantity (Γ , _ ^ _) (Fin.suc i) = lookupQuantity Γ i

------------------------------------------------------------------------
-- Usage Vectors (QTT)
------------------------------------------------------------------------

-- | Usage vector: tracks how many times each variable is used
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Usage : ℕ → Set where
  []  : Usage 0
  _∷_ : ∀ {n} → Quantity → Usage n → Usage (ℕ.suc n)

infixr 5 _∷_

-- | Zero usage vector (all variables unused)
zeroUsage : ∀ {n} → Usage n
zeroUsage {0} = []
zeroUsage {ℕ.suc n} = Zero ∷ zeroUsage

-- | Is this usage vector ALL ZERO — i.e. does the expression read no local
-- variable? (D126.)
--
-- Returns the PROOF, not a `Bool`: the closed-expression lift needs
-- `Ψ ≡ zeroUsage` to build its derivation, and a boolean would have to be
-- re-inverted at the use site. Same shape as `isRIntView` — the decision
-- carries what the caller will need.
zeroUsage? : ∀ {n} (Ψ : Usage n) → Maybe (Ψ ≡ zeroUsage)
zeroUsage? []            = just refl
zeroUsage? (Zero ∷ Ψ)    with zeroUsage? Ψ
... | just refl          = just refl
... | nothing            = nothing
zeroUsage? (One ∷ _)     = nothing
zeroUsage? (Many ∷ _)    = nothing

-- The decider says `just` on the diagonal. Completeness needs this: a closed
-- expression's usage IS `zeroUsage`, but `zeroUsage? zeroUsage` is stuck until
-- the size is known, and `nothing` carries no evidence to contradict.
zeroUsage?-just : ∀ {n} → zeroUsage? (zeroUsage {n}) ≡ just refl
zeroUsage?-just {0}       = refl
zeroUsage?-just {ℕ.suc n} rewrite zeroUsage?-just {n} = refl

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

-- | Check if usage respects declared quantities
_≤ᵘ_ : ∀ {n} → Usage n → Ctx n → Set
[] ≤ᵘ ∅ = ⊤
  where
    open import Data.Unit using (⊤)
(q ∷ ψ) ≤ᵘ (Γ , A ^ q') = (q ≤q q' ≡ true) × (ψ ≤ᵘ Γ)
  where
    open import Data.Bool using (true)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Data.Product using (_×_)

-- | Boolean version of subusaging check (for validation)
_≤ᵘ?_ : ∀ {n} → Usage n → Ctx n → Bool
[] ≤ᵘ? ∅ = true
(q ∷ ψ) ≤ᵘ? (Γ , A ^ q') = (q ≤q q') ∧ (ψ ≤ᵘ? Γ)

-- | Lookup quantity at specific index in usage vector
lookupUsage : ∀ {n} → Usage n → Fin n → Quantity
lookupUsage (q ∷ ψ) Fin.zero    = q
lookupUsage (q ∷ ψ) (Fin.suc i) = lookupUsage ψ i

-- | Drop first element from usage vector (for removing bound variable)
tailUsage : ∀ {n} → Usage (ℕ.suc n) → Usage n
tailUsage (q ∷ ψ) = ψ

------------------------------------------------------------------------
-- Plan 0.58 (OCP-0006): the IR-FREE variable witness. A de-Bruijn `Fin`
-- carrying the same type/usage indices a `var i : Expr` would — so
-- `lookupLocal`/`t-var-local` can name a local WITHOUT the IR-carrying `Expr`.
-- (`Surface.var i` rebuilds the `Expr` from `svar i` in the impl side.)
------------------------------------------------------------------------
data SVar : ∀ {n} → Ctx n → Usage n → Type → Set where
  svar : ∀ {n} {Γ : Ctx n} (i : Fin n) → SVar Γ (singleUse i One) (lookup Γ i)

------------------------------------------------------------------------
-- Usage-restricted contexts (plan 0.86 step B, D142)
------------------------------------------------------------------------

-- THE INVARIANT THIS EXISTS FOR: the environment carried into a subterm holds
-- exactly the variables that subterm USES — never "everything bound so far".
--
-- `elaborate` used to hand the whole `Γ` to every subterm, so a variable that
-- died stayed a component of a live environment product and could not be
-- reclaimed. Dead-variable elimination then had to be an OPTIMISATION anyone
-- could forget to run. Restricting the context by the usage vector makes it
-- the SHAPE of the elaborator instead: a dead variable cannot be in the
-- environment because it was never put there. (OCP-0005 rung 1 — violation is
-- ill-typed rather than merely suboptimal.)

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

-- | Pointwise usage order, RELATIONAL rather than the `Bool`-valued `_≤q_`:
--   the elaborator needs to induct on the witness, and D134 says the spec
--   names properties while deciders stay in the implementation.
-- Each constructor names BOTH quantities, so a clause can case on the larger
-- side without an unmatchable implicit.
data _≤q'_ : Quantity → Quantity → Set where
  z≤z : Zero ≤q' Zero
  z≤o : Zero ≤q' One
  z≤m : Zero ≤q' Many
  o≤o : One  ≤q' One
  o≤m : One  ≤q' Many
  m≤m : Many ≤q' Many

-- (`_≤ᵘ_` is taken: it relates a usage vector to a CONTEXT's declared
--  quantities. This one relates two usage vectors at the same context.)
data _⊑ᵘ_ : ∀ {n} → Usage n → Usage n → Set where
  ⊑[] : [] ⊑ᵘ []
  _⊑∷_ : ∀ {n q r} {Ψ Φ : Usage n} → q ≤q' r → Ψ ⊑ᵘ Φ → (q ∷ Ψ) ⊑ᵘ (r ∷ Φ)

infixr 5 _⊑ᵘ_
infixr 5 _⊑∷_

-- | The order is reflexive — every subterm may keep what it already has.
⊑ᵘ-refl : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Ψ
⊑ᵘ-refl []           = ⊑[]
⊑ᵘ-refl (Zero ∷ Ψ)   = z≤z ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (One  ∷ Ψ)   = o≤o ⊑∷ ⊑ᵘ-refl Ψ
⊑ᵘ-refl (Many ∷ Ψ)   = m≤m ⊑∷ ⊑ᵘ-refl Ψ
