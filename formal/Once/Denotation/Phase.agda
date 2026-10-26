-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Phase — the QTT RUNTIME PHASE at the denotation.
--
-- `Γ ↾ Ψ` is the runtime interpretation of a graded context: the variables the
-- term actually uses, with the `Zero`-graded (erased) ones dropped. These four
-- are the value-level counterparts of `Once.Surface.Elaborate`'s `projUsed`,
-- `restrictEnv` and `bindEnv`, and of `NbEPQTT`'s `erase`:
--
--     ⟦ Γ ▷[ 𝟘 ] A ⟧run  = ⟦ Γ ⟧run
--     erase (Γ ▷[ 𝟘 ] A) = erase Γ ⊙ fstT
--
-- Used by `Denotation.SourceDenote` (meaning of a Surface term), whose
-- environment is the runtime phase.
------------------------------------------------------------------------

module Once.Denotation.Phase where

import Once.Spec.Context
open import Once.Spec.Type using (Ty)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Spec.Grade using (Quantity; Zero; One; Many)
-- Imported from `Surface.Context` (the DEFINING module) rather than through
-- `Surface.Syntax`'s re-export: `_↾_` is recursive, and a recursive function
-- reached through a re-export does not always reduce at the use site.
open import Once.Context using (⟦_⟧ᶜ; _↾_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Spec.Context using (Ctx; Usage; []; _⊑ᵘ_; lookup; singleUse; ∅)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)

--
-- `⟦_⟧ˢ` runs over `⟦ Γ ↾ Ψ ⟧ᶜ` — exactly the variables the term uses — for the
-- same reason `elaborate` does. It is forced here rather than chosen: with a
-- grade-aware meaning, a `lam` at an ERASED arrow takes no argument, so there
-- is no value to extend the environment with, and none can be conjured (`A`
-- may be uninhabited). Carrying the runtime environment is what makes the
-- clause statable at all.
--
-- These three mirror `Elaborate`'s `projUsed` / `restrictEnv` / `bindEnv`.

-- | Read the one variable a `var` uses. As in `projUsed`, the chain collapses:
--   the head IS the variable, and a `Zero` head is not in the environment.
lookupᴰUsed : ∀ {m} {n} (Γ : Ctx m n) (i : Fin n)
            → ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ → ⟦ lookup Γ i ⟧ᴰ
lookupᴰUsed (Γ ▸ A) fzero    dγ = proj₂ dγ
lookupᴰUsed (Γ ▸ A) (fsuc i) dγ = lookupᴰUsed Γ i dγ

-- | The `erase` projection at the denotation: narrow the environment to a
--   smaller usage. `fst` where a variable is dropped, keep it otherwise.
restrictᴰ : ∀ {m} {n} {Γ : Ctx m n} {Ψ Ψ' : Usage n}
          → Ψ' ⊑ᵘ Ψ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ
restrictᴰ {Γ = ∅}         []              dγ = dγ
restrictᴰ {Γ = Γ ▸ A} (z≤z ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule dγ
restrictᴰ {Γ = Γ ▸ A} (z≤o ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ)
restrictᴰ {Γ = Γ ▸ A} (z≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ)
restrictᴰ {Γ = Γ ▸ A} (o≤o ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᴰ {Γ = Γ ▸ A} (o≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᴰ {Γ = Γ ▸ A} (m≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ

-- | Extend for a binder, keyed on the bound variable's usage in the body.
bindᴰ : ∀ {m} {n} {Γ : Ctx m n} {Ψ' : Usage n} {A : Ty m} (q : Quantity)
      → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ → ⟦ A ⟧ᴰ → ⟦ ⟦ (Γ ▸ A) ↾ (q ∷ Ψ') ⟧ᶜ ⟧ᴰ
bindᴰ Zero dγ a = dγ
bindᴰ One  dγ a = dγ , a
bindᴰ Many dγ a = dγ , a

-- | The ERASED binder: no value is required, because none exists. `bindᴰ Zero`
--   still demands an `⟦ A ⟧ᴰ` it then discards, and at an erased arrow there is
--   nothing to hand it (`A` may be uninhabited).
bindᴰ0 : ∀ {m} {n} {Γ : Ctx m n} {Ψ' : Usage n} {A : Ty m}
       → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ → ⟦ ⟦ (Γ ▸ A) ↾ (Zero ∷ Ψ') ⟧ᶜ ⟧ᴰ
bindᴰ0 dγ = dγ

-- | The runtime environment at the EMPTY context. Every `Usage 0` restricts
--   `∅` to `∅`, so the environment does not depend on the usage — but `_↾_` is
--   stuck until the usage is matched, and `Usage` is a `data` (no eta), so the
--   coercion has to be written out. It is the identity.
env0 : ∀ {m} {Ψ : Usage 0} → ⟦ ⟦ Once.Spec.Context.∅ {m} ⟧ᶜ ⟧ᴰ → ⟦ ⟦ Once.Spec.Context.∅ {m} ↾ Ψ ⟧ᶜ ⟧ᴰ
env0 {Ψ = []} dγ = dγ
