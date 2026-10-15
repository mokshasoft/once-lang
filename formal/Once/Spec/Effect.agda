{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Effect — what an effectful computation is.
--
-- One functor, `Step X Y = X + H_Σ Y`: the computation is done with a value,
-- or it makes one call and continues from the answer. Its fixed points are
-- the two monads of effects:
--
--   T X  = μY. X + H_Σ Y   finite trees: finitely many events, then it
--                          returns (or halts) — the free monad;
--   T∞ X = νY. X + H_Σ Y   possibly infinite trees: each next event after
--                          finite work, and it need not stop — the free
--                          completely iterative monad.
--
-- Every node is an event or the end; there is no silent step, so every
-- computation is productive by the shape of the functor. Equality of `T∞`
-- trees is bisimilarity.
--
-- A grade chooses the monad: `M pure = Id`, `M act = T`, `M eff = T∞`, with
-- the monad morphisms `Id → T → T∞` along the chain (`sub`).
--
-- A SERVER is the anamorphism into `T∞` (`unfoldEff`): `T∞ B` is the final
-- coalgebra of `B + H_Σ(−)`, and a round that returns either the result or the
-- next call as data (`A → T (B + H_Σ A)`) determines a unique map into it.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call)

module Once.Spec.Effect (Σ : Signature) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; pure; act; eff; _⊔p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF)

------------------------------------------------------------------------
-- The functor and its two fixed points
------------------------------------------------------------------------

data Step (X Y : Set) : Set where
  done : X → Step X Y
  node : Layer Σ Y → Step X Y

data T (X : Set) : Set where
  roll : Step X (T X) → T X

record T∞ (X : Set) : Set where
  coinductive
  field force : Step X (T∞ X)
open T∞

------------------------------------------------------------------------
-- The monads
------------------------------------------------------------------------

returnT : ∀ {X} → X → T X
returnT x = roll (done x)

infixl 1 _>>=T_ _>>=∞_
_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
roll (done x)              >>=T f = f x
roll (node (call o a k))   >>=T f = roll (node (call o a (λ b → k b >>=T f)))

return∞ : ∀ {X} → X → T∞ X
force (return∞ x) = done x

_>>=∞_   : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindStep : ∀ {X Y} → Step X (T∞ X) → (X → T∞ Y) → Step Y (T∞ Y)
force (m >>=∞ f) = bindStep (force m) f
bindStep (done x)            f = force (f x)
bindStep (node (call o a k)) f = node (call o a (λ b → k b >>=∞ f))

-- Every finite tree is one: the monad morphism `T → T∞`.
embed : ∀ {X} → T X → T∞ X
force (embed (roll (done x)))            = done x
force (embed (roll (node (call o a k)))) = node (call o a (λ b → embed (k b)))

------------------------------------------------------------------------
-- Bisimilarity: the same nodes forever, equal values at the leaves
------------------------------------------------------------------------

data StepEq {X Y Y′ : Set} (R : Y → Y′ → Set) : Step X Y → Step X Y′ → Set where
  done≈ : ∀ {x} → StepEq R (done x) (done x)
  node≈ : ∀ {o a k k′} → (∀ b → R (k b) (k′ b)) → StepEq R (node (call o a k)) (node (call o a k′))

record _≈_ {X : Set} (m m′ : T∞ X) : Set where
  coinductive
  field force≈ : StepEq _≈_ (force m) (force m′)
open _≈_

infix 4 _≈_

------------------------------------------------------------------------
-- The grades
------------------------------------------------------------------------

M : Purity → Set → Set
M pure X = X
M act  X = T X
M eff  X = T∞ X

return : ∀ π {X} → X → M π X
return pure x = x
return act  x = returnT x
return eff  x = return∞ x

bind : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bind pure m f = f m
bind act  m f = m >>=T f
bind eff  m f = m >>=∞ f

-- The monad morphisms along the chain.
sub : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
sub ⊑-pure m = m
sub ⊑-pa   m = returnT m
sub ⊑-pe   m = return∞ m
sub ⊑-act  m = m
sub ⊑-ae   m = embed m
sub ⊑-eff  m = m

-- Every grade embeds into `T∞`: what a computation is observed as.
toT∞ : ∀ π {X} → M π X → T∞ X
toT∞ pure m = return∞ m
toT∞ act  m = embed m
toT∞ eff  m = m

-- Running a `π₁` computation, then a `π₂` one: the whole is at their join.
bindᵍ : ∀ π₁ π₂ {X Y} → M π₁ X → (X → M π₂ Y) → M (π₁ ⊔p π₂) Y
bindᵍ pure π₂   m f = f m
bindᵍ act  pure m f = m >>=T λ x → returnT (f x)
bindᵍ act  act  m f = m >>=T f
bindᵍ act  eff  m f = embed m >>=∞ f
bindᵍ eff  pure m f = m >>=∞ λ x → return∞ (f x)
bindᵍ eff  act  m f = m >>=∞ λ x → embed (f x)
bindᵍ eff  eff  m f = m >>=∞ f

fmap : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmap π f m = bind π m λ x → return π (f x)

-- Equal computations: equal values and finite trees; bisimilar infinite ones.
EqM : ∀ π {X : Set} → M π X → M π X → Set
EqM pure m m′ = m ≡ m′
EqM act  m m′ = m ≡ m′
EqM eff  m m′ = m ≈ m′

------------------------------------------------------------------------
-- Codata whose layers are produced at a grade: the final coalgebra of
-- `M π ∘ F`
------------------------------------------------------------------------

record νM (π : Purity) (F : SFunctor) : Set where
  coinductive
  field outν : M π (⟦ F ⟧SF (νM π F))
open νM

------------------------------------------------------------------------
-- The server: the anamorphism into `T∞`
------------------------------------------------------------------------

-- Performing a request: its call, then the continuation's value — in a
-- computation that returns, and in one that need not.
performT : ∀ {A} → Layer Σ A → T A
performT (call o a k) = roll (node (call o a (λ b → returnT (k b))))

perform : ∀ {A} → Layer Σ A → T∞ A
force (perform (call o a k)) = node (call o a (λ b → return∞ (k b)))

-- The unique map into `T∞ B` determined by a round `c`: run the round; at its
-- result stop, at a request make the call and run the next round from the
-- answer (`Spec.Metatheory`: the universal property).
unfoldEff  : ∀ {A B : Set} → (A → T (B ⊎ Layer Σ A)) → A → T∞ B
roundTree  : ∀ {A B : Set} → (A → T (B ⊎ Layer Σ A)) → T (B ⊎ Layer Σ A) → T∞ B
roundStep  : ∀ {A B : Set} → (A → T (B ⊎ Layer Σ A)) → T (B ⊎ Layer Σ A) → Step B (T∞ B)
force (unfoldEff c a)  = roundStep c (c a)
force (roundTree c m)  = roundStep c m
roundStep c (roll (done (inj₁ b)))            = done b
roundStep c (roll (done (inj₂ (call o a k)))) = node (call o a (λ b → unfoldEff c (k b)))
roundStep c (roll (node (call o a k)))        = node (call o a (λ b → roundTree c (k b)))
