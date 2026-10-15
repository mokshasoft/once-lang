{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Equivalence — when two meanings are the same.
--
-- Two values of a type are the same when no finite observation tells them
-- apart: base values are equal; functions take the same arguments to the same
-- computations; computations make the same calls with the same arguments,
-- continue the same way from every answer, and end with the same values; a
-- stream's first `n` layers agree. Every grade is observed through its
-- embedding into `T∞`. Infinite objects are never compared by `≡`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Equivalence (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; Req)
open import Once.Spec.Signature using (Layer; call)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ using (M; T∞; Step; StepEq; toT∞; νM; module T∞; module νM)
open T∞ using (force)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)

-- A tree to depth `n`: its first `n` nodes agree.
UpTo : ∀ {X : Set} → ℕ → (X → X → Set) → T∞ X → T∞ X → Set
data NodeUpTo {X : Set} (n : ℕ) (R : X → X → Set) : Step X (T∞ X) → Step X (T∞ X) → Set where
  done≈ : ∀ {x y} → R x y → NodeUpTo n R (Step.done x) (Step.done y)
  node≈ : ∀ {o a k k′} → (∀ b → UpTo n R (k b) (k′ b)) → NodeUpTo n R (Step.node (call o a k)) (Step.node (call o a k′))
UpTo zero    R m m′ = ⊤
UpTo (suc n) R m m′ = NodeUpTo n R (force m) (force m′)

-- One layer of a stream: equal constants, related recursive positions.
LayerEq : ∀ (G : SFunctor) {X : Set} → (X → X → Set) → ⟦ G ⟧SF X → ⟦ G ⟧SF X → Set
LayerEq (SK B)   R x y = x ≡ y
LayerEq SId      R x y = R x y
LayerEq (G S⊕ H) R (inj₁ x) (inj₁ y) = LayerEq G R x y
LayerEq (G S⊕ H) R (inj₂ x) (inj₂ y) = LayerEq H R x y
LayerEq (G S⊕ H) R (inj₁ _) (inj₂ _) = ⊥
LayerEq (G S⊕ H) R (inj₂ _) (inj₁ _) = ⊥
LayerEq (G S⊗ H) R (x , x′) (y , y′) = LayerEq G R x y × LayerEq H R x′ y′

-- A stream to depth `n`: its first `n` layers agree.
νUpTo : ∀ π (G : SFunctor) → ℕ → νM π G → νM π G → Set
νUpTo π G zero    v w = ⊤
νUpTo π G (suc n) v w = UpTo (suc n) (LayerEq G (νUpTo π G n)) (toT∞ π (outν v)) (toT∞ π (outν w))

-- A request: the same call, continuations related.
data ReqEq {X : Set} (R : X → X → Set) : Layer Σ X → Layer Σ X → Set where
  req≈ : ∀ {o a k k′} → (∀ b → R (k b) (k′ b)) → ReqEq R (call o a k) (call o a k′)

Obs  : ℕ → (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
ObsM : ℕ → (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
ObsM n π A m m′ = UpTo n (Obs n A) (toT∞ π m) (toT∞ π m′)
Obs n (var ())
Obs n Unit    _ _ = ⊤
Obs n Void    _ _ = ⊤
Obs n Int     x y = x ≡ y
Obs n Float   x y = x ≡ y
Obs n (μ F)   x y = x ≡ y
Obs n (A * B) (a , b) (a′ , b′) = Obs n A a a′ × Obs n B b b′
Obs n (A + B) (inj₁ a) (inj₁ a′) = Obs n A a a′
Obs n (A + B) (inj₂ b) (inj₂ b′) = Obs n B b b′
Obs n (A + B) (inj₁ _) (inj₂ _)  = ⊥
Obs n (A + B) (inj₂ _) (inj₁ _)  = ⊥
Obs n (A ⇒[ mk-kind Zero π ] B) f g = ObsM n π B (f _) (g _)
Obs n (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → (∀ k → Obs k A a a′) → ObsM n π B (f a) (g a′)
Obs n (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → (∀ k → Obs k A a a′) → ObsM n π B (f a) (g a′)
Obs n (ν F π) v w = νUpTo π (code F) n v w
Obs n (Req A) l l′ = ReqEq (Obs n A) l l′

-- No finite observation tells them apart.
Same : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
Same A x y = ∀ n → Obs n A x y

SameM : (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SameM π A m m′ = ∀ n → ObsM n π A m m′
