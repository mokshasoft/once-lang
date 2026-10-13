-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Env — two environments of one context at two
-- usages AGREE when every variable live in BOTH holds related values
-- (plan 0.116 D1c).
--
-- Two derivations of one term may claim different usages (`⊢sub-use`, `⊢lam`'s
-- body head usage), so their environments hold different variables. A
-- variable live on one side only is never read: the only rule that reads one
-- is `⊢var`, at `singleUse i One` on both sides. Agreement is preserved by
-- restricting either side and by binding related values.
------------------------------------------------------------------------

module Once.Metatheory.Coherence.Env where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.Spec.Type.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Type)
open import Once.Spec.Context using (Ctx; ∅; _,_^_; lookup; Usage; []; _∷_; _↾_; ⟦_⟧ᶜ; singleUse; zeroUsage;
  _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Spec.Equivalence using (Same)
open import Once.Spec.Graded using (⟦_⟧ᵛ)
open import Once.Spec.Environment using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Metatheory.Coherence.Relation using (S; Same→S)

Env : ∀ {n} → Ctx n → Usage n → Set
Env Γ Ψ = ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᵛ

-- The environment below the head, and whether the head is held.
tl : ∀ {n} {Γ : Ctx n} {A r} (q : Quantity) {Ψ : Usage n} → Env (Γ , A ^ r) (q ∷ Ψ) → Env Γ Ψ
tl Zero x = x
tl One  x = proj₁ x
tl Many x = proj₁ x

-- Related heads, when both sides hold one.
Head : ∀ {n} {Γ : Ctx n} {A r} (q q′ : Quantity) {Ψ Ψ′ : Usage n}
     → Env (Γ , A ^ r) (q ∷ Ψ) → Env (Γ , A ^ r) (q′ ∷ Ψ′) → Set
Head Zero _    _ _ = ⊤
Head One  Zero _ _ = ⊤
Head Many Zero _ _ = ⊤
Head {A = A} One  One  x x′ = S A (proj₂ x) (proj₂ x′)
Head {A = A} One  Many x x′ = S A (proj₂ x) (proj₂ x′)
Head {A = A} Many One  x x′ = S A (proj₂ x) (proj₂ x′)
Head {A = A} Many Many x x′ = S A (proj₂ x) (proj₂ x′)

Agree : ∀ {n} (Γ : Ctx n) (Ψ Ψ′ : Usage n) → Env Γ Ψ → Env Γ Ψ′ → Set
Agree ∅           []       []         _ _  = ⊤
Agree (Γ , A ^ r) (q ∷ Ψ) (q′ ∷ Ψ′) x x′ = Agree Γ Ψ Ψ′ (tl q x) (tl q′ x′) × Head q q′ x x′

------------------------------------------------------------------------
-- Restriction, on either side
------------------------------------------------------------------------

restrictˡ : ∀ {n} {Γ : Ctx n} {Φ Ψ Ψ′ : Usage n} (p : Φ ⊑ᵘ Ψ) {x : Env Γ Ψ} {x′ : Env Γ Ψ′}
          → Agree Γ Ψ Ψ′ x x′ → Agree Γ Φ Ψ′ (restrictᵛ {Γ = Γ} p x) x′
restrictˡ {Γ = ∅} {Ψ′ = []} ⊑[] h = tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = q′ ∷ Ψ′} (z≤z ⊑∷ u) (h , _) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = q′ ∷ Ψ′} (z≤o ⊑∷ u) (h , _) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = q′ ∷ Ψ′} (z≤m ⊑∷ u) (h , _) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Zero ∷ Ψ′} (o≤o ⊑∷ u) (h , e) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = One  ∷ Ψ′} (o≤o ⊑∷ u) (h , e) = restrictˡ u h , e
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Many ∷ Ψ′} (o≤o ⊑∷ u) (h , e) = restrictˡ u h , e
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Zero ∷ Ψ′} (o≤m ⊑∷ u) (h , e) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = One  ∷ Ψ′} (o≤m ⊑∷ u) (h , e) = restrictˡ u h , e
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Many ∷ Ψ′} (o≤m ⊑∷ u) (h , e) = restrictˡ u h , e
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Zero ∷ Ψ′} (m≤m ⊑∷ u) (h , e) = restrictˡ u h , tt
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = One  ∷ Ψ′} (m≤m ⊑∷ u) (h , e) = restrictˡ u h , e
restrictˡ {Γ = Γ , A ^ r} {Ψ′ = Many ∷ Ψ′} (m≤m ⊑∷ u) (h , e) = restrictˡ u h , e

restrictʳ : ∀ {n} {Γ : Ctx n} {Ψ Φ′ Ψ′ : Usage n} (p : Φ′ ⊑ᵘ Ψ′) {x : Env Γ Ψ} {x′ : Env Γ Ψ′}
          → Agree Γ Ψ Ψ′ x x′ → Agree Γ Ψ Φ′ x (restrictᵛ {Γ = Γ} p x′)
restrictʳ {Γ = ∅} {Ψ = []} ⊑[] h = tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (z≤z ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (z≤z ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (z≤z ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (z≤o ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (z≤o ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (z≤o ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (z≤m ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (z≤m ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (z≤m ⊑∷ u) (h , _) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (o≤o ⊑∷ u) (h , e) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (o≤o ⊑∷ u) (h , e) = restrictʳ u h , e
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (o≤o ⊑∷ u) (h , e) = restrictʳ u h , e
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (o≤m ⊑∷ u) (h , e) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (o≤m ⊑∷ u) (h , e) = restrictʳ u h , e
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (o≤m ⊑∷ u) (h , e) = restrictʳ u h , e
restrictʳ {Γ = Γ , A ^ r} {Ψ = Zero ∷ Ψ} (m≤m ⊑∷ u) (h , e) = restrictʳ u h , tt
restrictʳ {Γ = Γ , A ^ r} {Ψ = One  ∷ Ψ} (m≤m ⊑∷ u) (h , e) = restrictʳ u h , e
restrictʳ {Γ = Γ , A ^ r} {Ψ = Many ∷ Ψ} (m≤m ⊑∷ u) (h , e) = restrictʳ u h , e

-- Both sides at once.
restrict₂ : ∀ {n} {Γ : Ctx n} {Φ Ψ Φ′ Ψ′ : Usage n} (p : Φ ⊑ᵘ Ψ) (p′ : Φ′ ⊑ᵘ Ψ′) {x : Env Γ Ψ} {x′ : Env Γ Ψ′}
          → Agree Γ Ψ Ψ′ x x′ → Agree Γ Φ Φ′ (restrictᵛ {Γ = Γ} p x) (restrictᵛ {Γ = Γ} p′ x′)
restrict₂ p p′ h = restrictʳ p′ (restrictˡ p h)

------------------------------------------------------------------------
-- Binding
------------------------------------------------------------------------

-- A held argument on each side (the binder used at `q`, `q′`).
bind₂ : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A} (q q′ : Quantity) {x : Env Γ Ψ} {x′ : Env Γ Ψ′} {a a′ : ⟦ A ⟧ᵛ}
      → Agree Γ Ψ Ψ′ x x′ → S A a a′
      → Agree (Γ , A ^ Many) (q ∷ Ψ) (q′ ∷ Ψ′) (bindᵛ {Γ = Γ} {A = A} q x a) (bindᵛ {Γ = Γ} {A = A} q′ x′ a′)
bind₂ Zero Zero h s = h , tt
bind₂ Zero One  h s = h , tt
bind₂ Zero Many h s = h , tt
bind₂ One  Zero h s = h , tt
bind₂ One  One  h s = h , s
bind₂ One  Many h s = h , s
bind₂ Many Zero h s = h , tt
bind₂ Many One  h s = h , s
bind₂ Many Many h s = h , s

-- An erased binder (no argument exists) on the left, on the right, or on both.
bind0ˡ : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A} (q′ : Quantity) {x : Env Γ Ψ} {x′ : Env Γ Ψ′} {a′ : ⟦ A ⟧ᵛ}
       → Agree Γ Ψ Ψ′ x x′
       → Agree (Γ , A ^ Many) (Zero ∷ Ψ) (q′ ∷ Ψ′) (bindᵛ0 {Γ = Γ} {A = A} x) (bindᵛ {Γ = Γ} {A = A} q′ x′ a′)
bind0ˡ Zero h = h , tt
bind0ˡ One  h = h , tt
bind0ˡ Many h = h , tt

bind0ʳ : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A} (q : Quantity) {x : Env Γ Ψ} {x′ : Env Γ Ψ′} {a : ⟦ A ⟧ᵛ}
       → Agree Γ Ψ Ψ′ x x′
       → Agree (Γ , A ^ Many) (q ∷ Ψ) (Zero ∷ Ψ′) (bindᵛ {Γ = Γ} {A = A} q x a) (bindᵛ0 {Γ = Γ} {A = A} x′)
bind0ʳ Zero h = h , tt
bind0ʳ One  h = h , tt
bind0ʳ Many h = h , tt

bind00 : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A} {x : Env Γ Ψ} {x′ : Env Γ Ψ′}
       → Agree Γ Ψ Ψ′ x x′
       → Agree (Γ , A ^ Many) (Zero ∷ Ψ) (Zero ∷ Ψ′) (bindᵛ0 {Γ = Γ} {A = A} x) (bindᵛ0 {Γ = Γ} {A = A} x′)
bind00 h = h , tt

------------------------------------------------------------------------
-- Reading the one variable a `var` uses
------------------------------------------------------------------------

lookup-S : ∀ {n} (Γ : Ctx n) (i : Fin n) {x x′ : Env Γ (singleUse i One)}
         → Agree Γ (singleUse i One) (singleUse i One) x x′
         → S (lookup Γ i) (lookupᵛUsed Γ i x) (lookupᵛUsed Γ i x′)
lookup-S (Γ , A ^ r) fzero    (_ , s) = s
lookup-S (Γ , A ^ r) (fsuc i) (h , _) = lookup-S Γ i h

------------------------------------------------------------------------
-- The identity: an environment the same as itself agrees with itself
------------------------------------------------------------------------

S-Agree : ∀ {n} (Γ : Ctx n) (Ψ : Usage n) {x x′ : Env Γ Ψ} → S ⟦ Γ ↾ Ψ ⟧ᶜ x x′ → Agree Γ Ψ Ψ x x′
S-Agree ∅           []         s = tt
S-Agree (Γ , A ^ r) (Zero ∷ Ψ) s = S-Agree Γ Ψ s , tt
S-Agree (Γ , A ^ r) (One  ∷ Ψ) (s , a) = S-Agree Γ Ψ s , a
S-Agree (Γ , A ^ r) (Many ∷ Ψ) (s , a) = S-Agree Γ Ψ s , a

Same-Agree : ∀ {n} (Γ : Ctx n) (Ψ : Usage n) {x : Env Γ Ψ} → Same ⟦ Γ ↾ Ψ ⟧ᶜ x x → Agree Γ Ψ Ψ x x
Same-Agree Γ Ψ h = S-Agree Γ Ψ (Same→S ⟦ Γ ↾ Ψ ⟧ᶜ h)
