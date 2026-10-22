-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Context — deciders on usages.
--
-- Contexts and usages are the Spec's (`Once.Internal.Context`). The elaborator
-- decides two things about them here.
------------------------------------------------------------------------

open import Once.Type.Grade using (_≤qᵇ_)
module Once.Surface.Context where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Zero; One; Many)
open import Once.Internal.Context using (Ctx; ∅; _,_^_; Usage; []; _∷_; zeroUsage)

-- | Is this usage vector all zero, i.e. does the expression read no local
-- variable? Returns the proof the closed-expression lift needs.
zeroUsage? : ∀ {n} (Ψ : Usage n) → Maybe (Ψ ≡ zeroUsage)
zeroUsage? []            = just refl
zeroUsage? (Zero ∷ Ψ)    with zeroUsage? Ψ
... | just refl          = just refl
... | nothing            = nothing
zeroUsage? (One ∷ _)     = nothing
zeroUsage? (Many ∷ _)    = nothing

-- The decider says `just` on the diagonal (completeness needs it: a closed
-- expression's usage is `zeroUsage`, but `zeroUsage? zeroUsage` is stuck until
-- the size is known).
zeroUsage?-just : ∀ {n} → zeroUsage? (zeroUsage {n}) ≡ just refl
zeroUsage?-just {0}       = refl
zeroUsage?-just {ℕ.suc n} rewrite zeroUsage?-just {n} = refl

-- | Does a usage respect the context's declared quantities?
_≤ᵘ?_ : ∀ {m} {n} → Usage n → Ctx m n → Bool
[] ≤ᵘ? ∅ = true
(q ∷ ψ) ≤ᵘ? (Γ , A ^ q') = (q ≤qᵇ q') ∧ (ψ ≤ᵘ? Γ)
