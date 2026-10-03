-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreRenameSem — plan 0.103 6b, step B.1: the core meaning is
-- STABLE UNDER RENAMING.
--
--   ⟦ ren-⊢ θ d ⟧ fmt δ dΔ ≡ ⟦ d ⟧ fmt δ (thinᴰ θ Ψ dΔ)
--
-- The derived combinators weaken an arm (`wk g`) and the elaboration closes
-- combinators (`close`), so the 6b bridge (surface meaning = core meaning of
-- the elaboration) needs to know what renaming MEANS. The core meaning runs
-- over the RUNTIME environment `Γ ↾ Ψ` (D143), whose shape depends on the
-- usage, and `ren-⊢` transports the usage; so besides the environment
-- thinning `thinᴰ` the proof needs:
--   * `_⊑ᵘ_` is proof-irrelevant, so `restrictᵛ` does not see its witness;
--   * `restrictᵛ` commutes with `thinᴰ`;
--   * the transports `ren-⊢` wraps its clauses in move to the environment.
-- (A formulation over FULL environments would avoid the usage transports, but
-- is false to state: an erased binder of an empty type has no value to put in
-- its slot.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Adequacy.CoreRenameSem {s : ℕ} (S : Sig s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Postulates using (extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst-sym-subst)

open import Once.Type using (Type; Quantity; Zero; One; Many)
open import Once.Target.Arch using (TargetNum)
open import Once.Surface.Context
  using (Ctx; ∅; _,_^_; Usage; []; _∷_; _↾_; lookup; singleUse; zeroUsage;
         _⊑ᵘ_; ⊑[]; _⊑∷_; _≤q'_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m;
         _+ᵘ_; _*ᵘ_; _⊔ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Surface.Thinning using (_⊆_; done; skip; keep; thin-var; thin-usage; thin-var-lookup;
  thin-usage-+ᵘ; thin-usage-*ᵘ; thin-usage-⊔ᵘ; thin-usage-zeroUsage; thin-usage-singleUse)
open import Once.Spec.Core.Rename S using (ren-⊢; ren-cong; keep-extR)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; bindM; subM)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.GradedOps using (ana-semᵛ; fmapM)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
import Once.Spec.Core.Meaning S as GM

Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

------------------------------------------------------------------------
-- The environment a thinning induces
------------------------------------------------------------------------

-- `skip` drops the slot the thinning added (its usage is `Zero`, so the
-- runtime environment has no slot for it); `keep` keeps a slot iff it is live.
thinᴰ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) (Ψ : Usage n)
      → Env Δ (thin-usage θ Ψ) → Env Γ Ψ
thinᴰ done     []         dΔ = dΔ
thinᴰ (skip θ) Ψ          dΔ = thinᴰ θ Ψ dΔ
thinᴰ (keep θ) (Zero ∷ Ψ) dΔ = thinᴰ θ Ψ dΔ
thinᴰ (keep θ) (One  ∷ Ψ) dΔ = thinᴰ θ Ψ (proj₁ dΔ) , proj₂ dΔ
thinᴰ (keep θ) (Many ∷ Ψ) dΔ = thinᴰ θ Ψ (proj₁ dΔ) , proj₂ dΔ

------------------------------------------------------------------------
-- The usage order is proof-irrelevant
------------------------------------------------------------------------

≤q'-unique : ∀ {q r} (a b : q ≤q' r) → a ≡ b
≤q'-unique z≤z z≤z = refl
≤q'-unique z≤o z≤o = refl
≤q'-unique z≤m z≤m = refl
≤q'-unique o≤o o≤o = refl
≤q'-unique o≤m o≤m = refl
≤q'-unique m≤m m≤m = refl

⊑ᵘ-unique : ∀ {n} {Ψ Φ : Usage n} (u v : Ψ ⊑ᵘ Φ) → u ≡ v
⊑ᵘ-unique ⊑[]       ⊑[]       = refl
⊑ᵘ-unique (a ⊑∷ u) (b ⊑∷ v) = cong₂ _⊑∷_ (≤q'-unique a b) (⊑ᵘ-unique u v)

restrictᵛ-irr : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (u v : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ)
              → restrictᵛ {Γ = Γ} u x ≡ restrictᵛ {Γ = Γ} v x
restrictᵛ-irr {Γ = Γ} u v x = cong (λ w → restrictᵛ {Γ = Γ} w x) (⊑ᵘ-unique u v)

------------------------------------------------------------------------
-- Thinning and restriction commute
------------------------------------------------------------------------

-- The thinned order, from the original one.
thin-⊑ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
       → Ψ' ⊑ᵘ Ψ → thin-usage θ Ψ' ⊑ᵘ thin-usage θ Ψ
thin-⊑ done     ⊑[]      = ⊑[]
thin-⊑ (skip θ) u        = z≤z ⊑∷ thin-⊑ θ u
thin-⊑ (keep θ) (a ⊑∷ u) = a ⊑∷ thin-⊑ θ u

thin-restrict : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
                (u : Ψ' ⊑ᵘ Ψ) (x : Env Δ (thin-usage θ Ψ))
              → thinᴰ θ Ψ' (restrictᵛ {Γ = Δ} (thin-⊑ θ u) x) ≡ restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ x)
thin-restrict done     ⊑[]        x = refl
thin-restrict (skip θ) u          x = thin-restrict θ u x
thin-restrict (keep θ) (z≤z ⊑∷ u) x = thin-restrict θ u x
thin-restrict (keep θ) (z≤o ⊑∷ u) x = thin-restrict θ u (proj₁ x)
thin-restrict (keep θ) (z≤m ⊑∷ u) x = thin-restrict θ u (proj₁ x)
thin-restrict (keep θ) (o≤o ⊑∷ u) x = cong (_, proj₂ x) (thin-restrict θ u (proj₁ x))
thin-restrict (keep θ) (o≤m ⊑∷ u) x = cong (_, proj₂ x) (thin-restrict θ u (proj₁ x))
thin-restrict (keep θ) (m≤m ⊑∷ u) x = cong (_, proj₂ x) (thin-restrict θ u (proj₁ x))

-- …at ANY pair of witnesses (the order is proof-irrelevant).
thin-restrict′ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
                 (u : Ψ' ⊑ᵘ Ψ) (u' : thin-usage θ Ψ' ⊑ᵘ thin-usage θ Ψ) (x : Env Δ (thin-usage θ Ψ))
               → thinᴰ θ Ψ' (restrictᵛ {Γ = Δ} u' x) ≡ restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ x)
thin-restrict′ {Δ = Δ} θ u u' x = trans (cong (thinᴰ θ _) (restrictᵛ-irr {Γ = Δ} u' (thin-⊑ θ u) x)) (thin-restrict θ u x)

-- A binder under `keep`.
thin-bind : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {A : Type} (q : Quantity) (Ψ : Usage n)
            (x : Env Δ (thin-usage θ Ψ)) (a : ⟦ A ⟧ᵛ)
          → thinᴰ (keep {A = A} {q = Many} θ) (q ∷ Ψ) (bindᵛ {Γ = Δ} {A = A} q x a) ≡ bindᵛ {Γ = Γ} {A = A} q (thinᴰ θ Ψ x) a
thin-bind θ Zero Ψ x a = refl
thin-bind θ One  Ψ x a = refl
thin-bind θ Many Ψ x a = refl

------------------------------------------------------------------------
-- Transports move to the environment
------------------------------------------------------------------------

-- A usage transport on a derivation is a transport on its environment.
⟦⟧-substΨ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {t A π} (e : Ψ ≡ Ψ')
              (d : Γ ⊢[ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ')
          → GM.⟦ subst (λ U → Γ ⊢[ U ] t ∷ A ! π) e d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (subst (Env Γ) (sym e) x)
⟦⟧-substΨ refl d fmt δ x = refl

-- …a term transport is invisible…
⟦⟧-substt : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t t' A π} (e : t ≡ t')
              (d : Γ ⊢[ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ)
          → GM.⟦ subst (λ u → Γ ⊢[ Ψ ] u ∷ A ! π) e d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ x
⟦⟧-substt refl d fmt δ x = refl

-- …and a type transport transports the result.
⟦⟧-substA : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A A' π} (e : A ≡ A')
              (d : Γ ⊢[ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ)
          → GM.⟦ subst (λ X → Γ ⊢[ Ψ ] t ∷ X ! π) e d ⟧ fmt δ x ≡ subst (λ X → M π ⟦ X ⟧ᵛ) e (GM.⟦ d ⟧ fmt δ x)
⟦⟧-substA refl d fmt δ x = refl

-- Restricting a transported environment is restricting the original.
restrict-subst : ∀ {n} {Γ : Ctx n} {U U' Ψ' : Usage n} (e : U ≡ U')
                   (u : Ψ' ⊑ᵘ U') (x : Env Γ U)
               → restrictᵛ {Γ = Γ} u (subst (Env Γ) e x) ≡ restrictᵛ {Γ = Γ} (subst (Ψ' ⊑ᵘ_) (sym e) u) x
restrict-subst refl u x = refl

------------------------------------------------------------------------
-- The general move: restriction after a usage transport, thinned.
------------------------------------------------------------------------

thin-restr : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
               (u : Ψ' ⊑ᵘ Ψ) {U : Usage m} (e : thin-usage θ Ψ ≡ U)
               (u' : thin-usage θ Ψ' ⊑ᵘ U) (x : Env Δ U)
           → thinᴰ θ Ψ' (restrictᵛ {Γ = Δ} u' x) ≡ restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ (subst (Env Δ) (sym e) x))
thin-restr θ u refl u' x = thin-restrict′ θ u u' x

-- …and with the restricted usage transported too (`case`'s nested restriction).
thin-restr₂ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
                (u : Ψ' ⊑ᵘ Ψ) {U U' : Usage m} (e : thin-usage θ Ψ ≡ U) (e' : thin-usage θ Ψ' ≡ U')
                (u' : U' ⊑ᵘ U) (x : Env Δ U)
            → thinᴰ θ Ψ' (subst (Env Δ) (sym e') (restrictᵛ {Γ = Δ} u' x))
              ≡ restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ (subst (Env Δ) (sym e) x))
thin-restr₂ θ u refl refl u' x = thin-restrict′ θ u u' x

-- Binds, pointwise in the continuation.
bindC : ∀ {π} {X Y : Set} {a a' : M π X} {f g : X → M π Y} → a ≡ a' → (∀ v → f v ≡ g v) → bindM π a f ≡ bindM π a' g
bindC {π} {a = a} refl h = cong (bindM π a) (extensionality h)

-- Undo a transport.
back : ∀ {m} {Δ : Ctx m} {U V : Usage m} (e : U ≡ V) (x : Env Δ U) → subst (Env Δ) (sym e) (subst (Env Δ) e x) ≡ x
back e x = subst-sym-subst e

------------------------------------------------------------------------
-- The variable: thinning preserves lookup, at the level of environments.
------------------------------------------------------------------------

-- UIP-style peeling of a usage equation at a cons (K is available).
tail≡ : ∀ {n} {q : Quantity} {A B : Usage n} → (Once.Surface.Context._∷_ q A) ≡ (q ∷ B) → A ≡ B
tail≡ refl = refl

peel0 : ∀ {n} {Δ : Ctx n} {X : Type} {r : Quantity} {A B : Usage n} (e : Zero ∷ A ≡ Zero ∷ B) (x : Env Δ A)
      → subst (Env (Δ , X ^ r)) e x ≡ subst (Env Δ) (tail≡ e) x
peel0 e x with tail≡ e
... | refl with e
...   | refl = refl

peel1 : ∀ {n} {Δ : Ctx n} {X : Type} {r : Quantity} {A B : Usage n} (e : One ∷ A ≡ One ∷ B) (x : Env Δ A) (a : ⟦ X ⟧ᵛ)
      → subst (Env (Δ , X ^ r)) e (x , a) ≡ (subst (Env Δ) (tail≡ e) x , a)
peel1 e x a with tail≡ e
... | refl with e
...   | refl = refl

lookup-thin : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) (i : Fin n)
                (e' : thin-usage θ (singleUse i One) ≡ singleUse (thin-var θ i) One)
                (x : Env Δ (thin-usage θ (singleUse i One)))
            → subst ⟦_⟧ᵛ (sym (thin-var-lookup θ i)) (lookupᵛUsed Δ (thin-var θ i) (subst (Env Δ) e' x))
              ≡ lookupᵛUsed Γ i (thinᴰ θ (singleUse i One) x)
lookup-thin {Δ = Δ , X ^ r} (skip θ) i e' x =
  trans (cong (λ z → subst ⟦_⟧ᵛ (sym (thin-var-lookup θ i)) (lookupᵛUsed Δ (thin-var θ i) z))
              (peel0 {Δ = Δ} {X = X} {r = r} e' x))
        (lookup-thin θ i (tail≡ e') x)
lookup-thin {Δ = Δ , X ^ r} (keep θ) zero e' x =
  cong proj₂ (peel1 {Δ = Δ} {X = X} {r = r} e' (proj₁ x) (proj₂ x))
lookup-thin {Δ = Δ , X ^ r} (keep θ) (suc i) e' x =
  trans (cong (λ z → subst ⟦_⟧ᵛ (sym (thin-var-lookup θ i)) (lookupᵛUsed Δ (thin-var θ i) z))
              (peel0 {Δ = Δ} {X = X} {r = r} e' x))
        (lookup-thin θ i (tail≡ e') x)

-- The environment of a subterm, after `ren-⊢`'s usage transport, thinned.
envEq : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n} {U : Usage m}
          (u : Ψ' ⊑ᵘ Ψ) (e : thin-usage θ Ψ ≡ U) (u' : thin-usage θ Ψ' ⊑ᵘ U) (x : Env Δ (thin-usage θ Ψ))
      → thinᴰ θ Ψ' (restrictᵛ {Γ = Δ} u' (subst (Env Δ) e x)) ≡ restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ x)
envEq {Γ = Γ} {Δ = Δ} θ {Ψ = Ψ} u e u' x =
  trans (thin-restr θ u e u' (subst (Env Δ) e x)) (cong (λ z → restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ z)) (back {Δ = Δ} e x))

-- …and `case`'s nested one.
envEq₂ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ'' Ψ' Ψ : Usage n} {U U' : Usage m}
           (v : Ψ'' ⊑ᵘ Ψ') (u : Ψ' ⊑ᵘ Ψ) (e : thin-usage θ Ψ ≡ U) (e' : thin-usage θ Ψ' ≡ U')
           (v' : thin-usage θ Ψ'' ⊑ᵘ U') (u' : U' ⊑ᵘ U) (x : Env Δ (thin-usage θ Ψ))
       → thinᴰ θ Ψ'' (restrictᵛ {Γ = Δ} v' (restrictᵛ {Γ = Δ} u' (subst (Env Δ) e x)))
         ≡ restrictᵛ {Γ = Γ} v (restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ x))
envEq₂ {Γ = Γ} {Δ = Δ} θ {Ψ = Ψ} v u e e' v' u' x =
  trans (thin-restr θ v e' v' (restrictᵛ {Γ = Δ} u' (subst (Env Δ) e x)))
        (cong (restrictᵛ {Γ = Γ} v)
          (trans (thin-restr₂ θ u e e' u' (subst (Env Δ) e x))
                 (cong (λ z → restrictᵛ {Γ = Γ} u (thinᴰ θ Ψ z)) (back {Δ = Δ} e x))))


------------------------------------------------------------------------
-- THE RENAMING LEMMA
------------------------------------------------------------------------

ren-sem : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ t A π} (θ : Γ ⊆ Δ) (d : Γ ⊢[ Ψ ] t ∷ A ! π)
            (fmt : TargetNum) (δ : GM.DefSem) (x : Env Δ (thin-usage θ Ψ))
        → GM.⟦ ren-⊢ θ d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (thinᴰ θ Ψ x)

ren-sem {Δ = Δ} θ (⊢var {Γ = Γ} i) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-singleUse θ i One)) _ fmt δ x)
  (trans (⟦⟧-substA (sym (thin-var-lookup θ i)) (⊢var (thin-var θ i)) fmt δ _)
         (lookup-thin θ i (sym (sym (thin-usage-singleUse θ i One))) x))

ren-sem θ (⊢lam {q = Zero} {q' = Zero} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)
ren-sem θ (⊢lam {q = Zero} {q' = One}  () _) fmt δ x
ren-sem θ (⊢lam {q = Zero} {q' = Many} () _) fmt δ x
ren-sem θ (⊢lam {q = One} {q' = Zero} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)
ren-sem θ (⊢lam {q = One} {q' = One} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)
ren-sem θ (⊢lam {q = One} {q' = Many} () _) fmt δ x
ren-sem θ (⊢lam {q = Many} {q' = Zero} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)
ren-sem θ (⊢lam {q = Many} {q' = One} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)
ren-sem θ (⊢lam {q = Many} {q' = Many} {t = t} le d) fmt δ x =
  extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _)

ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC {π} (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → refl))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (Zero *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ Zero Ψ₂))
ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC {π} (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → bindC {π} (trans (ren-sem θ dx fmt δ _)
                                    (cong (GM.⟦ dx ⟧ fmt δ)
                                      (envEq θ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) (sym (sym E)) _ x)))
                             (λ vx → refl)))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (One *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ One Ψ₂))
ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC {π} (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → bindC {π} (trans (ren-sem θ dx fmt δ _)
                                    (cong (GM.⟦ dx ⟧ fmt δ)
                                      (envEq θ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) (sym (sym E)) _ x)))
                             (λ vx → refl)))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (Many *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ Many Ψ₂))

ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
        (trans (ren-sem (keep θ) db fmt δ _)
               (cong (GM.⟦ db ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) (sym (sym E)) _ x))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (Zero *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ Zero Ψ₁))
ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC {π} (trans (ren-sem θ de fmt δ _)
                      (cong (GM.⟦ de ⟧ fmt δ) (envEq θ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) (sym (sym E)) _ x)))
               (λ v → trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
                      (trans (ren-sem (keep θ) db fmt δ _)
                             (cong (λ z → GM.⟦ db ⟧ fmt δ (z , v)) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) (sym (sym E)) _ x)))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (One *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ One Ψ₁))
ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC {π} (trans (ren-sem θ de fmt δ _)
                      (cong (GM.⟦ de ⟧ fmt δ) (envEq θ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) (sym (sym E)) _ x)))
               (λ v → trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
                      (trans (ren-sem (keep θ) db fmt δ _)
                             (cong (λ z → GM.⟦ db ⟧ fmt δ (z , v)) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) (sym (sym E)) _ x)))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (Many *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ Many Ψ₁))

ren-sem {Δ = Δ} θ ⊢unit fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) ⊢unit fmt δ x

ren-sem θ (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} da db) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) _ fmt δ x)
        (bindC {π} (trans (ren-sem θ da fmt δ _)
                      (cong (GM.⟦ da ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) (sym (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))) _ x)))
               (λ a → bindC {π} (trans (ren-sem θ db fmt δ _)
                                   (cong (GM.⟦ db ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) (sym (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))) _ x)))
                            (λ b → refl)))
ren-sem θ (⊢fst {π = π} d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢snd {π = π} d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢inl {π = π} d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢inr {π = π} d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢case {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {π = π} {l = l} {r = r} ds dl dr) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC {π} (trans (ren-sem θ ds fmt δ _)
                      (cong (GM.⟦ ds ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) _ x)))
               (λ { (inj₁ a) → trans (⟦⟧-substt (ren-cong (keep-extR θ) l) (ren-⊢ (keep θ) dl) fmt δ _)
                                (trans (ren-sem (keep θ) dl fmt δ _)
                                (trans (cong (GM.⟦ dl ⟧ fmt δ) (thin-bind θ qℓ Ψₗ _ a))
                                       (cong (λ z → GM.⟦ dl ⟧ fmt δ (bindᵛ qℓ z a))
                                             (envEq₂ θ (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ) (⊑ᵘ-⊔ˡ (thin-usage θ Ψₗ) (thin-usage θ Ψᵣ)) (⊑ᵘ-+ʳ (thin-usage θ Ψs) (thin-usage θ Ψₗ ⊔ᵘ thin-usage θ Ψᵣ)) x))))
                  ; (inj₂ b) → trans (⟦⟧-substt (ren-cong (keep-extR θ) r) (ren-⊢ (keep θ) dr) fmt δ _)
                                (trans (ren-sem (keep θ) dr fmt δ _)
                                (trans (cong (GM.⟦ dr ⟧ fmt δ) (thin-bind θ qr Ψᵣ _ b))
                                       (cong (λ z → GM.⟦ dr ⟧ fmt δ (bindᵛ qr z b))
                                             (envEq₂ θ (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ) (⊑ᵘ-⊔ʳ (thin-usage θ Ψₗ) (thin-usage θ Ψᵣ)) (⊑ᵘ-+ʳ (thin-usage θ Ψs) (thin-usage θ Ψₗ ⊔ᵘ thin-usage θ Ψᵣ)) x)))) }))
  where E = trans (thin-usage-+ᵘ θ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (cong (thin-usage θ Ψs +ᵘ_) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ))
ren-sem θ (⊢absurd {π = π} d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢roll {π = π} wf d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢fold {Ψa = Ψa} {Ψt = Ψt} {π = π} wf da dt) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψa Ψt)) _ fmt δ x)
        (bindC {π} (trans (ren-sem θ da fmt δ _)
                      (cong (GM.⟦ da ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψa Ψt) (sym (sym (thin-usage-+ᵘ θ Ψa Ψt))) _ x)))
               (λ valg → bindC {π} (trans (ren-sem θ dt fmt δ _)
                                      (cong (GM.⟦ dt ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψa Ψt) (sym (sym (thin-usage-+ᵘ θ Ψa Ψt))) _ x)))
                               (λ _ → refl)))
ren-sem θ (⊢unfold {Ψc = Ψc} {Ψs = Ψs} {π = π} {π′ = π′} wf dc ds) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψc Ψs)) _ fmt δ x)
        (cong₂ (λ m c → bindM π′ m (λ s → ana-semᵛ π π′ wf c s))
          (trans (ren-sem θ ds fmt δ _)
                 (cong (GM.⟦ ds ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψc Ψs) (sym (sym (thin-usage-+ᵘ θ Ψc Ψs))) _ x)))
          ((trans (ren-sem θ dc fmt δ _)
                   (cong (GM.⟦ dc ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψc Ψs) (sym (sym (thin-usage-+ᵘ θ Ψc Ψs))) _ x)))))
ren-sem θ (⊢out {π = π} wf d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢coerce {π = π} p d) fmt δ x = cong (fmapM π _) (ren-sem θ d fmt δ x)
ren-sem {Δ = Δ} θ ⊢lit-int fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) ⊢lit-int fmt δ x
ren-sem {Δ = Δ} θ ⊢lit-float fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) ⊢lit-float fmt δ x
ren-sem {Δ = Δ} θ ⊢lit-str fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) ⊢lit-str fmt δ x
ren-sem θ (⊢prim {π = π} p d) fmt δ x = bindC {π} (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem {Δ = Δ} θ (⊢sigop c k h g m) fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) (⊢sigop c k h g m) fmt δ x
ren-sem θ (⊢sub-eff g d) fmt δ x = cong (subM g) (ren-sem θ d fmt δ x)
ren-sem {Δ = Δ} θ (⊢ref d τ r) fmt δ x = ⟦⟧-substΨ {Γ = Δ} (sym (thin-usage-zeroUsage θ)) (⊢ref d τ r) fmt δ x

------------------------------------------------------------------------
-- Weakening by one unused variable (`wk-⊢′`, what the derived combinators use).
------------------------------------------------------------------------

open import Once.Surface.Thinning using (⊆-refl; thin-usage-refl)
open import Once.Spec.Core.DerivedTyping S using (wk-⊢′)
open import Once.Spec.Core.Rename S using (wk-⊢; thin-var-refl)

-- The identity thinning is the identity, across its usage transport.
thin-refl : ∀ {n} {Γ : Ctx n} (Ψ : Usage n) (e : thin-usage (⊆-refl {Γ = Γ}) Ψ ≡ Ψ) (y : Env Γ Ψ)
          → thinᴰ (⊆-refl {Γ = Γ}) Ψ (subst (Env Γ) (sym e) y) ≡ y
thin-refl {Γ = ∅} [] refl y = refl
thin-refl {Γ = Γ , X ^ r} (Zero ∷ Ψ) e y = trans (cong (thinᴰ (⊆-refl {Γ = Γ}) Ψ) (peel0' e y)) (thin-refl {Γ = Γ} Ψ (tail≡ e) y)
  where
    peel0' : ∀ {A B : Usage _} (e : Zero ∷ A ≡ Zero ∷ B) (y : Env Γ B)
           → subst (Env (Γ , X ^ r)) (sym e) y ≡ subst (Env Γ) (sym (tail≡ e)) y
    peel0' e y with tail≡ e
    ... | refl with e
    ...   | refl = refl
thin-refl {Γ = Γ , X ^ r} (One ∷ Ψ) e (y , a) =
  trans (cong (λ z → thinᴰ (⊆-refl {Γ = Γ}) Ψ (proj₁ z) , proj₂ z) (peel1' e y a)) (cong (_, a) (thin-refl {Γ = Γ} Ψ (tail≡ e) y))
  where
    peel1' : ∀ {A B : Usage _} (e : One ∷ A ≡ One ∷ B) (y : Env Γ B) (a : ⟦ X ⟧ᵛ)
           → subst (Env (Γ , X ^ r)) (sym e) (y , a) ≡ (subst (Env Γ) (sym (tail≡ e)) y , a)
    peel1' e y a with tail≡ e
    ... | refl with e
    ...   | refl = refl
thin-refl {Γ = Γ , X ^ r} (Many ∷ Ψ) e (y , a) =
  trans (cong (λ z → thinᴰ (⊆-refl {Γ = Γ}) Ψ (proj₁ z) , proj₂ z) (peelm' e y a)) (cong (_, a) (thin-refl {Γ = Γ} Ψ (tail≡ e) y))
  where
    peelm' : ∀ {A B : Usage _} (e : Many ∷ A ≡ Many ∷ B) (y : Env Γ B) (a : ⟦ X ⟧ᵛ)
           → subst (Env (Γ , X ^ r)) (sym e) (y , a) ≡ (subst (Env Γ) (sym (tail≡ e)) y , a)
    peelm' e y a with tail≡ e
    ... | refl with e
    ...   | refl = refl

-- `wk-⊢′`'s usage transport sits under `Zero ∷_`.
⟦⟧-substΨ0 : ∀ {n} {Γ : Ctx n} {B : Type} {Ψ Ψ' : Usage n} {t A π} (e : Ψ ≡ Ψ')
               (d : (Γ , B ^ Many) ⊢[ Zero ∷ Ψ ] t ∷ A ! π) (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ')
           → GM.⟦ subst (λ U → (Γ , B ^ Many) ⊢[ Zero ∷ U ] t ∷ A ! π) e d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (subst (Env Γ) (sym e) x)
⟦⟧-substΨ0 refl d fmt δ x = refl

-- THE WEAKENING LEMMA: a term weakened by one unused variable means what it meant.
wk-sem : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A π} (B : Type) (d : Γ ⊢[ Ψ ] t ∷ A ! π)
           (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ)
       → GM.⟦ wk-⊢′ B d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ x
wk-sem {Γ = Γ} {Ψ = Ψ} {t = t} B d fmt δ x =
  trans (⟦⟧-substΨ0 (thin-usage-refl {Γ = Γ} Ψ) (wk-⊢ B d) fmt δ x)
  (trans (⟦⟧-substt (ren-cong (λ i → cong suc (thin-var-refl {Γ = Γ} i)) t) (ren-⊢ (skip {A = B} {q = Many} ⊆-refl) d) fmt δ _)
  (trans (ren-sem (skip ⊆-refl) d fmt δ _)
         (cong (GM.⟦ d ⟧ fmt δ) (thin-refl {Γ = Γ} Ψ (thin-usage-refl {Γ = Γ} Ψ) x))))

------------------------------------------------------------------------
-- A closed term, embedded in any context (`⊢close`), means what it meant.
------------------------------------------------------------------------

open import Once.Spec.Core.Rename S using (⊢close; ∅⊆; close)
open import Once.Surface.Thinning using (thin-usage-zeroUsage)

close-sem : ∀ {n} {Γ : Ctx n} {t A π} (d : ∅ ⊢[ zeroUsage ] t ∷ A ! π)
              (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ zeroUsage)
          → GM.⟦ ⊢close {Γ = Γ} d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ tt
close-sem {Γ = Γ} {t = t} d fmt δ x =
  trans (⟦⟧-substt (ren-cong {ρ = thin-var (∅⊆ {Γ = Γ})} {ρ′ = λ ()} (λ ()) t) _ fmt δ x)
  (trans (⟦⟧-substΨ (thin-usage-zeroUsage (∅⊆ {Γ = Γ})) (ren-⊢ (∅⊆ {Γ = Γ}) d) fmt δ x)
         (ren-sem (∅⊆ {Γ = Γ}) d fmt δ _))
