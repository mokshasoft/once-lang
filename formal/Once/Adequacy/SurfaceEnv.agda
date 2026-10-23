-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SurfaceEnv — the implementation's environment shape against
-- the Spec's (plan 0.122 §5.5 M4).
--
-- The realization runs over the values of the variables a term uses as one
-- product, `⟦ Γ ↾ Ψ ⟧ᶜ` (a variable used zero times has no slot); the Spec's
-- core meaning over `Env σ Γ Ψ`, a slot per variable (`⊤` at `Zero`). They
-- agree when every live slot holds the same value (`EnvR`, the graph of
-- `fromSurf`). Each of the Spec's splits of an environment is a restriction
-- (`Coherence.Env`), so a split keeps related environments related; so does
-- binding a variable.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (TySub)

module Once.Adequacy.SurfaceEnv (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) (σ : TySub 0 0) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Type)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _⊑∷_; _⊑ᵘ_; singleUse; lookup)
open import Once.Internal.Context using (_↾_; ⊑ᵘ-unique) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.SpecDomain Σ σ using (⟦_⟧ᵛ; restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Spec.Core.Meaning Σ fmt S using (Env; restrict; slot; lookupᵛ; envˡ; envʳ; env*One; env*Many)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict; env*Many-envˡ-restrict)
open import Once.Internal.Context using (_+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)

-- The surface's environment.
SEnv : ∀ {n} → Ctx 0 n → Usage n → Set
SEnv Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

EnvR : ∀ {n} (Γ : Ctx 0 n) (Ψ : Usage n) → SEnv Γ Ψ → Env σ Γ Ψ → Set
EnvR ∅       []         _       _        = ⊤
EnvR (Γ ▸ A) (Zero ∷ Ψ) x       (γ , _)  = EnvR Γ Ψ x γ
EnvR (Γ ▸ A) (One  ∷ Ψ) (x , a) (γ , a′) = EnvR Γ Ψ x γ × a ≡ a′
EnvR (Γ ▸ A) (Many ∷ Ψ) (x , a) (γ , a′) = EnvR Γ Ψ x γ × a ≡ a′

-- The Spec's environment holding a surface environment's values: `EnvR` is
-- its graph.
fromSurf : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} → SEnv Γ Ψ → Env σ Γ Ψ
fromSurf {Γ = ∅}     {[]}       _       = tt
fromSurf {Γ = Γ ▸ A} {Zero ∷ Ψ} x       = fromSurf {Γ = Γ} x , tt
fromSurf {Γ = Γ ▸ A} {One  ∷ Ψ} (x , a) = fromSurf {Γ = Γ} x , a
fromSurf {Γ = Γ ▸ A} {Many ∷ Ψ} (x , a) = fromSurf {Γ = Γ} x , a

fromR : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {x : SEnv Γ Ψ} → EnvR Γ Ψ x (fromSurf {Γ = Γ} x)
fromR {Γ = ∅}     {[]}       = tt
fromR {Γ = Γ ▸ A} {Zero ∷ Ψ} = fromR {Γ = Γ}
fromR {Γ = Γ ▸ A} {One  ∷ Ψ} = fromR {Γ = Γ} , refl
fromR {Γ = Γ ▸ A} {Many ∷ Ψ} = fromR {Γ = Γ} , refl

fromR≡ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {x : SEnv Γ Ψ} {γ : Env σ Γ Ψ} → EnvR Γ Ψ x γ → fromSurf {Γ = Γ} x ≡ γ
fromR≡ {Γ = ∅}     {[]}                       r       = refl
fromR≡ {Γ = Γ ▸ A} {Zero ∷ Ψ} {γ = _ , _}     r       = cong (_, tt) (fromR≡ {Γ = Γ} r)
fromR≡ {Γ = Γ ▸ A} {One  ∷ Ψ} {_ , _} {_ , _} (r , e) = cong₂ _,_ (fromR≡ {Γ = Γ} r) e
fromR≡ {Γ = Γ ▸ A} {Many ∷ Ψ} {_ , _} {_ , _} (r , e) = cong₂ _,_ (fromR≡ {Γ = Γ} r) e

-- A restriction, on both sides (one proof per pair, `⊑ᵘ-unique`).
restrict-R : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ′ : Usage n} (p q : Ψ′ ⊑ᵘ Ψ) {x γ}
           → EnvR Γ Ψ x γ → EnvR Γ Ψ′ (restrictᵛ {Γ = Γ} p x) (restrict σ q γ)
restrict-R {Γ = Γ} p q {x} {γ} r = subst (λ q′ → EnvR Γ _ (restrictᵛ {Γ = Γ} p x) (restrict σ q′ γ)) (⊑ᵘ-unique p q) (go {Γ = Γ} p r)
  where
    go : ∀ {n} {Γ : Ctx 0 n} {Ψ Ψ′ : Usage n} (p : Ψ′ ⊑ᵘ Ψ) {x γ}
       → EnvR Γ Ψ x γ → EnvR Γ Ψ′ (restrictᵛ {Γ = Γ} p x) (restrict σ p γ)
    go {Γ = ∅}     []                         r       = tt
    go {Γ = Γ ▸ A} (0≤q {Zero} ⊑∷ p) {γ = _ , _} r       = go {Γ = Γ} p r
    go {Γ = Γ ▸ A} (0≤q {One}  ⊑∷ p) {_ , _} {_ , _} (r , _) = go {Γ = Γ} p r
    go {Γ = Γ ▸ A} (0≤q {Many} ⊑∷ p) {_ , _} {_ , _} (r , _) = go {Γ = Γ} p r
    go {Γ = Γ ▸ A} (1≤1 ⊑∷ p) {_ , _} {_ , _} (r , e) = go {Γ = Γ} p r , e
    go {Γ = Γ ▸ A} (1≤ω ⊑∷ p) {_ , _} {_ , _} (r , e) = go {Γ = Γ} p r , e
    go {Γ = Γ ▸ A} (ω≤ω ⊑∷ p) {_ , _} {_ , _} (r , e) = go {Γ = Γ} p r , e

-- One of the Spec's splits (a restriction along `u`), after a transport of the
-- usage, against the surface's restriction along `p`.
split-R : ∀ {n} {Γ : Ctx 0 n} {U V Ψ′ : Usage n} (E : U ≡ V) (p : Ψ′ ⊑ᵘ V) (u : Ψ′ ⊑ᵘ U)
            (f : Env σ Γ U → Env σ Γ Ψ′) → (∀ γ → f γ ≡ restrict σ u γ)
          → ∀ {x γ} → EnvR Γ V x γ → EnvR Γ Ψ′ (restrictᵛ {Γ = Γ} p x) (f (subst (Env σ Γ) (sym E) γ))
split-R {Γ = Γ} refl p u f ef {x} {γ} r = subst (EnvR Γ _ (restrictᵛ {Γ = Γ} p x)) (sym (ef γ)) (restrict-R {Γ = Γ} p u r)

-- The same with no transport.
split-R′ : ∀ {n} {Γ : Ctx 0 n} {V Ψ′ : Usage n} (p : Ψ′ ⊑ᵘ V) (u : Ψ′ ⊑ᵘ V)
             (f : Env σ Γ V → Env σ Γ Ψ′) → (∀ γ → f γ ≡ restrict σ u γ)
           → ∀ {x γ} → EnvR Γ V x γ → EnvR Γ Ψ′ (restrictᵛ {Γ = Γ} p x) (f γ)
split-R′ = split-R refl

-- The Spec's splits, against the surface's restrictions.
module _ {n} {Γ : Ctx 0 n} where

  envˡ-R : ∀ (Ψ₁ Ψ₂ : Usage n) {x γ} → EnvR Γ (Ψ₁ +ᵘ Ψ₂) x γ
         → EnvR Γ Ψ₁ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) (envˡ σ Ψ₁ Ψ₂ γ)
  envˡ-R Ψ₁ Ψ₂ = split-R′ {Γ = Γ} _ _ (envˡ σ Ψ₁ Ψ₂) (envˡ-restrict σ Ψ₁ Ψ₂)

  envʳ-R : ∀ (Ψ₁ Ψ₂ : Usage n) {x γ} → EnvR Γ (Ψ₁ +ᵘ Ψ₂) x γ
         → EnvR Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) (envʳ σ Ψ₁ Ψ₂ γ)
  envʳ-R Ψ₁ Ψ₂ = split-R′ {Γ = Γ} _ _ (envʳ σ Ψ₁ Ψ₂) (envʳ-restrict σ Ψ₁ Ψ₂)

  env*One-envʳ-R : ∀ (Ψ₁ Ψ₂ : Usage n) {x γ} → EnvR Γ (Ψ₁ +ᵘ One *ᵘ Ψ₂) x γ
                 → EnvR Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) x)
                        (env*One σ Ψ₂ (envʳ σ Ψ₁ (One *ᵘ Ψ₂) γ))
  env*One-envʳ-R Ψ₁ Ψ₂ = split-R′ {Γ = Γ} _ _ (λ y → env*One σ Ψ₂ (envʳ σ Ψ₁ (One *ᵘ Ψ₂) y)) (env*One-envʳ-restrict σ Ψ₁ Ψ₂)

  env*Many-envʳ-R : ∀ (Ψ₁ Ψ₂ : Usage n) {x γ} → EnvR Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂) x γ
                  → EnvR Γ Ψ₂ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x)
                         (env*Many σ Ψ₂ (envʳ σ Ψ₁ (Many *ᵘ Ψ₂) γ))
  env*Many-envʳ-R Ψ₁ Ψ₂ = split-R′ {Γ = Γ} _ _ (λ y → env*Many σ Ψ₂ (envʳ σ Ψ₁ (Many *ᵘ Ψ₂) y)) (env*Many-envʳ-restrict σ Ψ₁ Ψ₂)

  env*Many-envˡ-R : ∀ (Ψ₁ Ψ₂ : Usage n) {x γ} → EnvR Γ (Many *ᵘ Ψ₁ +ᵘ Ψ₂) x γ
                  → EnvR Γ Ψ₁ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ˡ (Many *ᵘ Ψ₁) Ψ₂)) x)
                         (env*Many σ Ψ₁ (envˡ σ (Many *ᵘ Ψ₁) Ψ₂ γ))
  env*Many-envˡ-R Ψ₁ Ψ₂ = split-R′ {Γ = Γ} _ _ (λ y → env*Many σ Ψ₁ (envˡ σ (Many *ᵘ Ψ₁) Ψ₂ y)) (env*Many-envˡ-restrict σ Ψ₁ Ψ₂)

-- Binding a variable.
bind-R : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type} (q : Quantity) {x γ} (a : ⟦ A ⟧ᵛ)
       → EnvR Γ Ψ x γ → EnvR (Γ ▸ A) (q ∷ Ψ) (bindᵛ {Γ = Γ} {A = A} q x a) (γ , slot q a)
bind-R Zero a r = r
bind-R One  a r = r , refl
bind-R Many a r = r , refl

bind0-R : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Type} {x γ} (v : ⊤)
        → EnvR Γ Ψ x γ → EnvR (Γ ▸ A) (Zero ∷ Ψ) (bindᵛ0 {Γ = Γ} {A = A} x) (γ , v)
bind0-R v r = r

-- A variable, looked up on both sides.
lookup-R : ∀ {n} (Γ : Ctx 0 n) (i : Fin n) {x γ}
         → EnvR Γ (singleUse i One) x γ → lookupᵛUsed Γ i x ≡ lookupᵛ σ Γ i γ
lookup-R (Γ ▸ A) zero    {_ , _} {_ , _} (_ , e) = e
lookup-R (Γ ▸ A) (suc i) {_} {_ , _} r = lookup-R Γ i r
