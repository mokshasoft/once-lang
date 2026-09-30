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
--   * `_⊑ᵘ_` is proof-irrelevant, so `restrictᴰ` does not see its witness;
--   * `restrictᴰ` commutes with `thinᴰ`;
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
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; _>>=T_; returnT; fmapT)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0; lookupᴰUsed)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
import Once.Spec.Core.Meaning S as GM

Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ

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

restrictᴰ-irr : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (u v : Ψ' ⊑ᵘ Ψ) (x : Env Γ Ψ)
              → restrictᴰ {Γ = Γ} u x ≡ restrictᴰ {Γ = Γ} v x
restrictᴰ-irr {Γ = Γ} u v x = cong (λ w → restrictᴰ {Γ = Γ} w x) (⊑ᵘ-unique u v)

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
              → thinᴰ θ Ψ' (restrictᴰ {Γ = Δ} (thin-⊑ θ u) x) ≡ restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ x)
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
               → thinᴰ θ Ψ' (restrictᴰ {Γ = Δ} u' x) ≡ restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ x)
thin-restrict′ {Δ = Δ} θ u u' x = trans (cong (thinᴰ θ _) (restrictᴰ-irr {Γ = Δ} u' (thin-⊑ θ u) x)) (thin-restrict θ u x)

-- A binder under `keep`.
thin-bind : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {A : Type} (q : Quantity) (Ψ : Usage n)
            (x : Env Δ (thin-usage θ Ψ)) (a : ⟦ A ⟧ᴰ)
          → thinᴰ (keep {A = A} {q = Many} θ) (q ∷ Ψ) (bindᴰ {Γ = Δ} {A = A} q x a) ≡ bindᴰ {Γ = Γ} {A = A} q (thinᴰ θ Ψ x) a
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
          → GM.⟦ subst (λ X → Γ ⊢[ Ψ ] t ∷ X ! π) e d ⟧ fmt δ x ≡ subst (λ X → T ⟦ X ⟧ᴰ) e (GM.⟦ d ⟧ fmt δ x)
⟦⟧-substA refl d fmt δ x = refl

-- Restricting a transported environment is restricting the original.
restrict-subst : ∀ {n} {Γ : Ctx n} {U U' Ψ' : Usage n} (e : U ≡ U')
                   (u : Ψ' ⊑ᵘ U') (x : Env Γ U)
               → restrictᴰ {Γ = Γ} u (subst (Env Γ) e x) ≡ restrictᴰ {Γ = Γ} (subst (Ψ' ⊑ᵘ_) (sym e) u) x
restrict-subst refl u x = refl

------------------------------------------------------------------------
-- The general move: restriction after a usage transport, thinned.
------------------------------------------------------------------------

thin-restr : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
               (u : Ψ' ⊑ᵘ Ψ) {U : Usage m} (e : thin-usage θ Ψ ≡ U)
               (u' : thin-usage θ Ψ' ⊑ᵘ U) (x : Env Δ U)
           → thinᴰ θ Ψ' (restrictᴰ {Γ = Δ} u' x) ≡ restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ (subst (Env Δ) (sym e) x))
thin-restr θ u refl u' x = thin-restrict′ θ u u' x

-- …and with the restricted usage transported too (`case`'s nested restriction).
thin-restr₂ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n}
                (u : Ψ' ⊑ᵘ Ψ) {U U' : Usage m} (e : thin-usage θ Ψ ≡ U) (e' : thin-usage θ Ψ' ≡ U')
                (u' : U' ⊑ᵘ U) (x : Env Δ U)
            → thinᴰ θ Ψ' (subst (Env Δ) (sym e') (restrictᴰ {Γ = Δ} u' x))
              ≡ restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ (subst (Env Δ) (sym e) x))
thin-restr₂ θ u refl refl u' x = thin-restrict′ θ u u' x

-- Binds, pointwise in the continuation.
bindC : ∀ {X Y : Set} {a a' : T X} {f g : X → T Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=T f) ≡ (a' >>=T g)
bindC {a = a} refl h = cong (a >>=T_) (extensionality h)

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

peel1 : ∀ {n} {Δ : Ctx n} {X : Type} {r : Quantity} {A B : Usage n} (e : One ∷ A ≡ One ∷ B) (x : Env Δ A) (a : ⟦ X ⟧ᴰ)
      → subst (Env (Δ , X ^ r)) e (x , a) ≡ (subst (Env Δ) (tail≡ e) x , a)
peel1 e x a with tail≡ e
... | refl with e
...   | refl = refl

lookup-thin : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) (i : Fin n)
                (e' : thin-usage θ (singleUse i One) ≡ singleUse (thin-var θ i) One)
                (x : Env Δ (thin-usage θ (singleUse i One)))
            → subst ⟦_⟧ᴰ (sym (thin-var-lookup θ i)) (lookupᴰUsed Δ (thin-var θ i) (subst (Env Δ) e' x))
              ≡ lookupᴰUsed Γ i (thinᴰ θ (singleUse i One) x)
lookup-thin {Δ = Δ , X ^ r} (skip θ) i e' x =
  trans (cong (λ z → subst ⟦_⟧ᴰ (sym (thin-var-lookup θ i)) (lookupᴰUsed Δ (thin-var θ i) z))
              (peel0 {Δ = Δ} {X = X} {r = r} e' x))
        (lookup-thin θ i (tail≡ e') x)
lookup-thin {Δ = Δ , X ^ r} (keep θ) zero e' x =
  cong proj₂ (peel1 {Δ = Δ} {X = X} {r = r} e' (proj₁ x) (proj₂ x))
lookup-thin {Δ = Δ , X ^ r} (keep θ) (suc i) e' x =
  trans (cong (λ z → subst ⟦_⟧ᴰ (sym (thin-var-lookup θ i)) (lookupᴰUsed Δ (thin-var θ i) z))
              (peel0 {Δ = Δ} {X = X} {r = r} e' x))
        (lookup-thin θ i (tail≡ e') x)

-- The environment of a subterm, after `ren-⊢`'s usage transport, thinned.
envEq : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ' Ψ : Usage n} {U : Usage m}
          (u : Ψ' ⊑ᵘ Ψ) (e : thin-usage θ Ψ ≡ U) (u' : thin-usage θ Ψ' ⊑ᵘ U) (x : Env Δ (thin-usage θ Ψ))
      → thinᴰ θ Ψ' (restrictᴰ {Γ = Δ} u' (subst (Env Δ) e x)) ≡ restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ x)
envEq {Γ = Γ} {Δ = Δ} θ {Ψ = Ψ} u e u' x =
  trans (thin-restr θ u e u' (subst (Env Δ) e x)) (cong (λ z → restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ z)) (back {Δ = Δ} e x))

-- …and `case`'s nested one.
envEq₂ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} (θ : Γ ⊆ Δ) {Ψ'' Ψ' Ψ : Usage n} {U U' : Usage m}
           (v : Ψ'' ⊑ᵘ Ψ') (u : Ψ' ⊑ᵘ Ψ) (e : thin-usage θ Ψ ≡ U) (e' : thin-usage θ Ψ' ≡ U')
           (v' : thin-usage θ Ψ'' ⊑ᵘ U') (u' : U' ⊑ᵘ U) (x : Env Δ (thin-usage θ Ψ))
       → thinᴰ θ Ψ'' (restrictᴰ {Γ = Δ} v' (restrictᴰ {Γ = Δ} u' (subst (Env Δ) e x)))
         ≡ restrictᴰ {Γ = Γ} v (restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ x))
envEq₂ {Γ = Γ} {Δ = Δ} θ {Ψ = Ψ} v u e e' v' u' x =
  trans (thin-restr θ v e' v' (restrictᴰ {Γ = Δ} u' (subst (Env Δ) e x)))
        (cong (restrictᴰ {Γ = Γ} v)
          (trans (thin-restr₂ θ u e e' u' (subst (Env Δ) e x))
                 (cong (λ z → restrictᴰ {Γ = Γ} u (thinᴰ θ Ψ z)) (back {Δ = Δ} e x))))

subst-returnT : ∀ {A B : Type} (e : A ≡ B) (v : ⟦ A ⟧ᴰ)
              → subst (λ X → T ⟦ X ⟧ᴰ) e (returnT v) ≡ returnT (subst ⟦_⟧ᴰ e v)
subst-returnT refl v = refl

------------------------------------------------------------------------
-- THE RENAMING LEMMA
------------------------------------------------------------------------

ren-sem : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ t A π} (θ : Γ ⊆ Δ) (d : Γ ⊢[ Ψ ] t ∷ A ! π)
            (fmt : TargetNum) (δ : GM.DefSem) (x : Env Δ (thin-usage θ Ψ))
        → GM.⟦ ren-⊢ θ d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (thinᴰ θ Ψ x)

ren-sem {Δ = Δ} θ (⊢var {Γ = Γ} i) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-singleUse θ i One)) _ fmt δ x)
  (trans (⟦⟧-substA (sym (thin-var-lookup θ i)) (⊢var (thin-var θ i)) fmt δ _)
  (trans (subst-returnT (sym (thin-var-lookup θ i)) _)
         (cong returnT (lookup-thin θ i (sym (sym (thin-usage-singleUse θ i One))) x))))

ren-sem θ (⊢lam {q = Zero} {q' = Zero} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))
ren-sem θ (⊢lam {q = Zero} {q' = One}  () _) fmt δ x
ren-sem θ (⊢lam {q = Zero} {q' = Many} () _) fmt δ x
ren-sem θ (⊢lam {q = One} {q' = Zero} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))
ren-sem θ (⊢lam {q = One} {q' = One} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))
ren-sem θ (⊢lam {q = One} {q' = Many} () _) fmt δ x
ren-sem θ (⊢lam {q = Many} {q' = Zero} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))
ren-sem θ (⊢lam {q = Many} {q' = One} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))
ren-sem θ (⊢lam {q = Many} {q' = Many} {t = t} le d) fmt δ x =
  cong returnT (extensionality λ a → trans (⟦⟧-substt (ren-cong (keep-extR θ) t) (ren-⊢ (keep θ) d) fmt δ _) (ren-sem (keep θ) d fmt δ _))

ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → refl))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (Zero *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ Zero Ψ₂))
ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → bindC (trans (ren-sem θ dx fmt δ _)
                                    (cong (GM.⟦ dx ⟧ fmt δ)
                                      (envEq θ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) (sym (sym E)) _ x)))
                             (λ vx → refl)))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (One *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ One Ψ₂))
ren-sem θ (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} df dx) fmt δ x =
  trans (⟦⟧-substΨ (sym E) (⊢app (ren-⊢ θ df) (ren-⊢ θ dx)) fmt δ x)
        (bindC (trans (ren-sem θ df fmt δ _)
                      (cong (GM.⟦ df ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) (sym (sym E)) _ x)))
               (λ vf → bindC (trans (ren-sem θ dx fmt δ _)
                                    (cong (GM.⟦ dx ⟧ fmt δ)
                                      (envEq θ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) (sym (sym E)) _ x)))
                             (λ vx → refl)))
  where E = trans (thin-usage-+ᵘ θ Ψ₁ (Many *ᵘ Ψ₂)) (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ Many Ψ₂))

ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
        (trans (ren-sem (keep θ) db fmt δ _)
               (cong (GM.⟦ db ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) (sym (sym E)) _ x))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (Zero *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ Zero Ψ₁))
ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC (trans (ren-sem θ de fmt δ _)
                      (cong (GM.⟦ de ⟧ fmt δ) (envEq θ (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) (sym (sym E)) _ x)))
               (λ v → trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
                      (trans (ren-sem (keep θ) db fmt δ _)
                             (cong (λ z → GM.⟦ db ⟧ fmt δ (z , v)) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) (sym (sym E)) _ x)))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (One *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ One Ψ₁))
ren-sem θ (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {b = b} de db) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC (trans (ren-sem θ de fmt δ _)
                      (cong (GM.⟦ de ⟧ fmt δ) (envEq θ (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) (sym (sym E)) _ x)))
               (λ v → trans (⟦⟧-substt (ren-cong (keep-extR θ) b) (ren-⊢ (keep θ) db) fmt δ _)
                      (trans (ren-sem (keep θ) db fmt δ _)
                             (cong (λ z → GM.⟦ db ⟧ fmt δ (z , v)) (envEq θ (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) (sym (sym E)) _ x)))))
  where E = trans (thin-usage-+ᵘ θ Ψ₂ (Many *ᵘ Ψ₁)) (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ Many Ψ₁))

ren-sem θ ⊢unit fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) ⊢unit fmt δ x

ren-sem θ (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) _ fmt δ x)
        (bindC (trans (ren-sem θ da fmt δ _)
                      (cong (GM.⟦ da ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) (sym (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))) _ x)))
               (λ a → bindC (trans (ren-sem θ db fmt δ _)
                                   (cong (GM.⟦ db ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψ₁ Ψ₂) (sym (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))) _ x)))
                            (λ b → refl)))
ren-sem θ (⊢fst d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢snd d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢inl d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢inr d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢case {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {l = l} {r = r} ds dl dr) fmt δ x =
  trans (⟦⟧-substΨ (sym E) _ fmt δ x)
        (bindC (trans (ren-sem θ ds fmt δ _)
                      (cong (GM.⟦ ds ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) _ x)))
               (λ { (inj₁ a) → trans (⟦⟧-substt (ren-cong (keep-extR θ) l) (ren-⊢ (keep θ) dl) fmt δ _)
                                (trans (ren-sem (keep θ) dl fmt δ _)
                                (trans (cong (GM.⟦ dl ⟧ fmt δ) (thin-bind θ qℓ Ψₗ _ a))
                                       (cong (λ z → GM.⟦ dl ⟧ fmt δ (bindᴰ qℓ z a))
                                             (envEq₂ θ (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ) (⊑ᵘ-⊔ˡ (thin-usage θ Ψₗ) (thin-usage θ Ψᵣ)) (⊑ᵘ-+ʳ (thin-usage θ Ψs) (thin-usage θ Ψₗ ⊔ᵘ thin-usage θ Ψᵣ)) x))))
                  ; (inj₂ b) → trans (⟦⟧-substt (ren-cong (keep-extR θ) r) (ren-⊢ (keep θ) dr) fmt δ _)
                                (trans (ren-sem (keep θ) dr fmt δ _)
                                (trans (cong (GM.⟦ dr ⟧ fmt δ) (thin-bind θ qr Ψᵣ _ b))
                                       (cong (λ z → GM.⟦ dr ⟧ fmt δ (bindᴰ qr z b))
                                             (envEq₂ θ (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (sym (sym E)) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ) (⊑ᵘ-⊔ʳ (thin-usage θ Ψₗ) (thin-usage θ Ψᵣ)) (⊑ᵘ-+ʳ (thin-usage θ Ψs) (thin-usage θ Ψₗ ⊔ᵘ thin-usage θ Ψᵣ)) x)))) }))
  where E = trans (thin-usage-+ᵘ θ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) (cong (thin-usage θ Ψs +ᵘ_) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ))
ren-sem θ (⊢absurd d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢roll wf d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢fold {Ψa = Ψa} {Ψt = Ψt} wf da dt) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψa Ψt)) _ fmt δ x)
        (bindC (trans (ren-sem θ da fmt δ _)
                      (cong (GM.⟦ da ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψa Ψt) (sym (sym (thin-usage-+ᵘ θ Ψa Ψt))) _ x)))
               (λ valg → bindC (trans (ren-sem θ dt fmt δ _)
                                      (cong (GM.⟦ dt ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψa Ψt) (sym (sym (thin-usage-+ᵘ θ Ψa Ψt))) _ x)))
                               (λ _ → refl)))
ren-sem θ (⊢unfold {Ψc = Ψc} {Ψs = Ψs} wf dc ds) fmt δ x =
  trans (⟦⟧-substΨ (sym (thin-usage-+ᵘ θ Ψc Ψs)) _ fmt δ x)
        (bindC (trans (ren-sem θ dc fmt δ _)
                      (cong (GM.⟦ dc ⟧ fmt δ) (envEq θ (⊑ᵘ-+ˡ Ψc Ψs) (sym (sym (thin-usage-+ᵘ θ Ψc Ψs))) _ x)))
               (λ vc → bindC (trans (ren-sem θ ds fmt δ _)
                                    (cong (GM.⟦ ds ⟧ fmt δ) (envEq θ (⊑ᵘ-+ʳ Ψc Ψs) (sym (sym (thin-usage-+ᵘ θ Ψc Ψs))) _ x)))
                             (λ _ → refl)))
ren-sem θ (⊢out wf d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢coerce p d) fmt δ x = cong (fmapT _) (ren-sem θ d fmt δ x)
ren-sem θ ⊢lit-int fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) ⊢lit-int fmt δ x
ren-sem θ ⊢lit-float fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) ⊢lit-float fmt δ x
ren-sem θ ⊢lit-str fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) ⊢lit-str fmt δ x
ren-sem θ (⊢prim p d) fmt δ x = bindC (ren-sem θ d fmt δ x) (λ _ → refl)
ren-sem θ (⊢sigop c k h g) fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) (⊢sigop c k h g) fmt δ x
ren-sem θ (⊢sub-eff g d) fmt δ x = ren-sem θ d fmt δ x
ren-sem θ (⊢ref d τ r) fmt δ x = ⟦⟧-substΨ (sym (thin-usage-zeroUsage θ)) (⊢ref d τ r) fmt δ x
