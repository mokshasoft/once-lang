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
-- Shared by `Denotation.SourceDenote` (meaning of a Surface term) and
-- `Denotation.Meaning` (meaning of a `⊢ᶜ` derivation), which need the same
-- three operations — `⊢ᶜ` carries a `Surface.Usage` index, so its meaning runs
-- over the runtime phase for exactly the reason the others do.
------------------------------------------------------------------------

module Once.Denotation.Phase where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (subst; sym; _≡_; refl; cong)

open import Once.Type using (Type; Quantity; Zero; One; Many)
-- Imported from `Surface.Context` (the DEFINING module) rather than through
-- `Surface.Syntax`'s re-export: `_↾_` is recursive, and a recursive function
-- reached through a re-export does not always reduce at the use site.
open import Once.Surface.Context
  using (Ctx; Usage; lookup; _,_^_; ∅; ⟦_⟧ᶜ; _↾_; _⊑ᵘ_; ⊑[]; _⊑∷_;
         z≤z; z≤o; z≤m; o≤o; o≤m; m≤m; singleUse; _∷_; [])
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
lookupᴰUsed : ∀ {n} (Γ : Ctx n) (i : Fin n)
            → ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ → ⟦ lookup Γ i ⟧ᴰ
lookupᴰUsed (Γ , A ^ q) fzero    dγ = proj₂ dγ
lookupᴰUsed (Γ , A ^ q) (fsuc i) dγ = lookupᴰUsed Γ i dγ

-- | The `erase` projection at the denotation: narrow the environment to a
--   smaller usage. `fst` where a variable is dropped, keep it otherwise.
restrictᴰ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n}
          → Ψ' ⊑ᵘ Ψ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ
restrictᴰ {Γ = ∅}         ⊑[]              dγ = dγ
restrictᴰ {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule dγ
restrictᴰ {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ)
restrictᴰ {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ)
restrictᴰ {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᴰ {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ
restrictᴰ {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ = restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ

-- | Extend for a binder, keyed on the bound variable's usage in the body.
bindᴰ : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A} (q : Quantity)
      → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ → ⟦ A ⟧ᴰ → ⟦ ⟦ (Γ , A ^ Many) ↾ (q ∷ Ψ') ⟧ᶜ ⟧ᴰ
bindᴰ Zero dγ a = dγ
bindᴰ One  dγ a = dγ , a
bindᴰ Many dγ a = dγ , a

-- | The ERASED binder: no value is required, because none exists. `bindᴰ Zero`
--   still demands an `⟦ A ⟧ᴰ` it then discards, and at an erased arrow there is
--   nothing to hand it (`A` may be uninhabited).
bindᴰ0 : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A}
       → ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ → ⟦ ⟦ (Γ , A ^ Many) ↾ (Zero ∷ Ψ') ⟧ᶜ ⟧ᴰ
bindᴰ0 dγ = dγ


-- | `erase` at the denotation: the FULL environment projected onto the RUNTIME
--   one. The value-level twin of `Once.Surface.Elaborate.eraseCtx`, and the
--   direct counterpart of `NbEPQTT.erase : Tm ⟦Γ⟧full ⟦Γ⟧run`.
--
--   Statements quantifying over a full environment (adequacy bridges,
--   faithfulness proofs) go through this, so the narrowing lives in ONE place
--   rather than once per clause.
eraseᴰ : ∀ {n} (Γ : Ctx n) (Ψ : Usage n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ
eraseᴰ ∅           []         dγ = dγ
eraseᴰ (Γ , A ^ q) (Zero ∷ Ψ) dγ = eraseᴰ Γ Ψ (proj₁ dγ)
eraseᴰ (Γ , A ^ q) (One  ∷ Ψ) dγ = eraseᴰ Γ Ψ (proj₁ dγ) , proj₂ dγ
eraseᴰ (Γ , A ^ q) (Many ∷ Ψ) dγ = eraseᴰ Γ Ψ (proj₁ dγ) , proj₂ dγ

-- | THE COHERENCE that makes the factoring work: narrowing an already-erased
--   environment is the same as erasing at the smaller usage directly.
--
--       restrictᴰ le (eraseᴰ Γ Ψ dγ) ≡ eraseᴰ Γ Ψ' dγ      (le : Ψ' ⊑ᵘ Ψ)
--
--   Without it, a proof stated over the full environment cannot apply its own
--   induction hypothesis: the goal carries `restrictᴰ … (eraseᴰ Γ Ψ dγ)` while
--   the IH is about `eraseᴰ Γ Ψ' dγ`. With it, every clause of such a proof
--   goes through unchanged.
eraseᴰ-restrict : ∀ {n} (Γ : Ctx n) {Ψ Ψ' : Usage n} (le : Ψ' ⊑ᵘ Ψ)
                  (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ)
                → restrictᴰ {Γ = Γ} le (eraseᴰ Γ Ψ dγ) ≡ eraseᴰ Γ Ψ' dγ
eraseᴰ-restrict ∅           ⊑[]            dγ = refl
eraseᴰ-restrict (Γ , A ^ q) (z≤z ⊑∷ ule) dγ = eraseᴰ-restrict Γ ule (proj₁ dγ)
eraseᴰ-restrict (Γ , A ^ q) (z≤o ⊑∷ ule) dγ = eraseᴰ-restrict Γ ule (proj₁ dγ)
eraseᴰ-restrict (Γ , A ^ q) (z≤m ⊑∷ ule) dγ = eraseᴰ-restrict Γ ule (proj₁ dγ)
eraseᴰ-restrict (Γ , A ^ q) (o≤o ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᴰ-restrict Γ ule (proj₁ dγ))
eraseᴰ-restrict (Γ , A ^ q) (o≤m ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᴰ-restrict Γ ule (proj₁ dγ))
eraseᴰ-restrict (Γ , A ^ q) (m≤m ⊑∷ ule) dγ = cong (_, proj₂ dγ) (eraseᴰ-restrict Γ ule (proj₁ dγ))

-- | The BINDER coherence, dual to `eraseᴰ-restrict`: erasing an environment that
--   has already been extended by a binder is the same as extending the erased
--   base with `bindᴰ`. Both sides case-split on `q`; with `q` a variable neither
--   reduces, so the equation has to be proved (three refls) rather than assumed.
eraseᴰ-bind : ∀ {n} (Γ : Ctx n) {A} (q : Quantity) (Ψ : Usage n)
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
            → eraseᴰ (Γ , A ^ Many) (q ∷ Ψ) (dγ , a)
                ≡ bindᴰ {Γ = Γ} {A = A} q (eraseᴰ Γ Ψ dγ) a
eraseᴰ-bind Γ Zero Ψ dγ a = refl
eraseᴰ-bind Γ One  Ψ dγ a = refl
eraseᴰ-bind Γ Many Ψ dγ a = refl

-- | The runtime environment at the EMPTY context. Every `Usage 0` restricts
--   `∅` to `∅`, so the environment does not depend on the usage — but `_↾_` is
--   stuck until the usage is matched, and `Usage` is a `data` (no eta), so the
--   coercion has to be written out. It is the identity.
env0 : ∀ {Ψ : Usage 0} → ⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ → ⟦ ⟦ ∅ ↾ Ψ ⟧ᶜ ⟧ᴰ
env0 {[]} dγ = dγ
