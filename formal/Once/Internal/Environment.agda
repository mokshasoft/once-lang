-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Environment — the runtime environment of a derivation and its
-- operations.
--
-- SPEC. A term at usage `Ψ` reads `⟦ Γ ↾ Ψ ⟧ᶜ`: exactly the variables it uses,
-- as a nested product. `restrictᵛ` narrows it to a smaller usage, `bindᵛ`
-- extends it for a binder used `q` times (an erased binder adds nothing),
-- `lookupᵛUsed` reads a variable, and `eraseᵛ` projects a full environment
-- onto the runtime one.
------------------------------------------------------------------------

module Once.Internal.Environment where

open import Data.Fin using (Fin)
import Data.Fin
open import Data.Product using (_,_; proj₁; proj₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Internal.Context using (Ctx; Usage; lookup; _,_^_; ∅; ⟦_⟧ᶜ; _↾_; _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; singleUse; _∷_; [])
open import Once.Internal.Graded using (⟦_⟧ᵛ)

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
lookupᵛUsed : ∀ {n} (Γ : Ctx n) (i : Fin n)
            → ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᵛ → ⟦ lookup Γ i ⟧ᵛ
lookupᵛUsed (Γ , A ^ q) Data.Fin.zero    dγ = proj₂ dγ
lookupᵛUsed (Γ , A ^ q) (Data.Fin.suc i) dγ = lookupᵛUsed Γ i dγ

-- | The `erase` projection at the denotation: narrow the environment to a
--   smaller usage. `fst` where a variable is dropped, keep it otherwise.
restrictᵛ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n}
          → Ψ' ⊑ᵘ Ψ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᵛ → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ
restrictᵛ {Γ = ∅}         ⊑[]              dγ = dγ
restrictᵛ {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule dγ
restrictᵛ {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ)
restrictᵛ {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ)
restrictᵛ {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᵛ {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᵛ {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ = restrictᵛ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ

-- | Extend for a binder, keyed on the bound variable's usage in the body.
bindᵛ : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A} (q : Quantity)
      → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ → ⟦ A ⟧ᵛ → ⟦ ⟦ (Γ , A ^ Many) ↾ (q ∷ Ψ') ⟧ᶜ ⟧ᵛ
bindᵛ Zero dγ a = dγ
bindᵛ One  dγ a = dγ , a
bindᵛ Many dγ a = dγ , a

-- | The ERASED binder: no value is required, because none exists. `bindᵛ Zero`
--   still demands an `⟦ A ⟧ᵛ` it then discards, and at an erased arrow there is
--   nothing to hand it (`A` may be uninhabited).
bindᵛ0 : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A}
       → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᵛ → ⟦ ⟦ (Γ , A ^ Many) ↾ (Zero ∷ Ψ') ⟧ᶜ ⟧ᵛ
bindᵛ0 dγ = dγ


-- | `erase` at the denotation: the FULL environment projected onto the RUNTIME
--   one. The value-level twin of `Once.Surface.Elaborate.eraseCtx`, and the
--   direct counterpart of `NbEPQTT.erase : Tm ⟦Γ⟧full ⟦Γ⟧run`.
--
--   Statements quantifying over a full environment (adequacy bridges,
--   faithfulness proofs) go through this, so the narrowing lives in ONE place
--   rather than once per clause.
eraseᵛ : ∀ {n} (Γ : Ctx n) (Ψ : Usage n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᵛ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᵛ
eraseᵛ ∅           []         dγ = dγ
eraseᵛ (Γ , A ^ q) (Zero ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ)
eraseᵛ (Γ , A ^ q) (One  ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ) , proj₂ dγ
eraseᵛ (Γ , A ^ q) (Many ∷ Ψ) dγ = eraseᵛ Γ Ψ (proj₁ dγ) , proj₂ dγ

-- | The runtime environment at the EMPTY context. Every `Usage 0` restricts
--   `∅` to `∅`, so the environment does not depend on the usage — but `_↾_` is
--   stuck until the usage is matched, and `Usage` is a `data` (no eta), so the
--   coercion has to be written out. It is the identity.
env0 : ∀ {Ψ : Usage 0} → ⟦ ⟦ ∅ ⟧ᶜ ⟧ᵛ → ⟦ ⟦ ∅ ↾ Ψ ⟧ᶜ ⟧ᵛ
env0 {[]} dγ = dγ
