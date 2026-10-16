{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Equivalence — when two meanings are the same.
--
-- Two values of a type are the same when no finite observation tells them
-- apart, by recursion on the type: base values are equal; functions take the
-- same arguments to the same computations; a stream's first `n` layers agree,
-- for every `n`.
--
-- Two computations are the same when observing them cannot tell them apart:
-- against every Interpretation and to every depth `n`, they make the same
-- first `n` calls and end the same way, with values that are the same — or
-- neither run gets that far (D317). This is the kernel of observation lifted
-- by sameness of the values, so it respects `return` and `>>=`. The depth
-- counts calls only; the values a run returns are compared whole, never to
-- the depth they were observed at. Every grade is observed through its
-- embedding into `T∞`; where a block of calls ends is not observed. Infinite
-- objects are never compared by `≡`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Equivalence (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ using (M; T∞; toT∞; νM; module νM)
open νM using (outν)
open import Once.Spec.Observation Σ using (Interp; History; End; returned; halted; cut; observe)
open import Once.Spec.Delay using (_≈⟨_⟩_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)

-- Two ends of runs: the same way, the values related.
data EndRel {X : Set} (R : X → X → Set) : End X → End X → Set where
  returned≈ : ∀ {x y} → R x y → EndRel R (returned x) (returned y)
  halted≈   : EndRel R halted halted
  cut≈      : EndRel R cut cut

-- The same calls, and the same end.
Outcome≈ : ∀ {X : Set} → (X → X → Set) → History × End X → History × End X → Set
Outcome≈ R o o′ = proj₁ o ≡ proj₁ o′ × EndRel R (proj₂ o) (proj₂ o′)

-- Two computations to depth `n`: against every Interpretation, their first
-- `n` calls and their ends agree, or neither run gets that far.
UpTo : ∀ {X : Set} → ℕ → (X → X → Set) → T∞ X → T∞ X → Set
UpTo n R m m′ = ∀ (ι : Interp) → observe ι [] m n ≈⟨ Outcome≈ R ⟩ observe ι [] m′ n

-- One layer of a stream: equal constants, related recursive positions.
LayerEq : ∀ (G : SFunctor) {X : Set} → (X → X → Set) → ⟦ G ⟧SF X → ⟦ G ⟧SF X → Set
LayerEq (SK B)   R x y = x ≡ y
LayerEq SId      R x y = R x y
LayerEq (G S⊕ H) R (inj₁ x) (inj₁ y) = LayerEq G R x y
LayerEq (G S⊕ H) R (inj₂ x) (inj₂ y) = LayerEq H R x y
LayerEq (G S⊕ H) R (inj₁ _) (inj₂ _) = ⊥
LayerEq (G S⊕ H) R (inj₂ _) (inj₁ _) = ⊥
LayerEq (G S⊗ H) R (x , x′) (y , y′) = LayerEq G R x y × LayerEq H R x′ y′

-- A stream to `n` layers: its first `n` layers agree, each layer's
-- computation observed to every depth.
νUpTo : ∀ π (G : SFunctor) → ℕ → νM π G → νM π G → Set
νUpTo π G zero    v w = ⊤
νUpTo π G (suc n) v w = ∀ k → UpTo k (LayerEq G (νUpTo π G n)) (toT∞ π (outν v)) (toT∞ π (outν w))

-- No finite observation tells them apart.
Same  : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
SameM : (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SameM π A m m′ = ∀ n → UpTo n (Same A) (toT∞ π m) (toT∞ π m′)
Same (var ())
Same Unit    _ _ = ⊤
Same Void    _ _ = ⊤
Same Int     x y = x ≡ y
Same Float   x y = x ≡ y
Same (μ F)   x y = x ≡ y
Same (A * B) (a , b) (a′ , b′) = Same A a a′ × Same B b b′
Same (A + B) (inj₁ a) (inj₁ a′) = Same A a a′
Same (A + B) (inj₂ b) (inj₂ b′) = Same B b b′
Same (A + B) (inj₁ _) (inj₂ _)  = ⊥
Same (A + B) (inj₂ _) (inj₁ _)  = ⊥
Same (A ⇒[ mk-kind Zero π ] B) f g = SameM π B (f _) (g _)
Same (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → Same A a a′ → SameM π B (f a) (g a′)
Same (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → Same A a a′ → SameM π B (f a) (g a′)
Same (ν F π) v w = ∀ n → νUpTo π (code F) n v w
