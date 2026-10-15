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
-- A GUARDED computation performs an event first: `T⁺ X = H_Σ (T∞ X)`, one
-- call, then anything (D311).
--
-- A grade chooses the monad: `M pure = Id`, `M act = T`, `M eff⁺ = T⁺`,
-- `M eff = T∞`, with the monad morphisms along the order (`sub`).
--
-- A SERVER is GUARDED ITERATION (`iter∞`): a step that either ends with a `B`
-- or performs an event first and then continues, with a `B` or the next
-- state. Every round performs an event, so its equation has a unique
-- solution in `T∞`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call)

module Once.Spec.Effect (Σ : Signature) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; pure; act; eff⁺; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-g; ⊑-ge; ⊑-eff)
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
-- Guarded computations: an event first
------------------------------------------------------------------------

data T⁺ (X : Set) : Set where
  call⁺ : Layer Σ (T∞ X) → T⁺ X

forget⁺ : ∀ {X} → T⁺ X → T∞ X
force (forget⁺ (call⁺ l)) = node l

infixl 1 _>>=⁺_
_>>=⁺_ : ∀ {X Y} → T⁺ X → (X → T∞ Y) → T⁺ Y
call⁺ (call o a k) >>=⁺ f = call⁺ (call o a (λ b → k b >>=∞ f))

-- A computation, then a guarded one: the guard comes before any return.
_⁺=<<_ : ∀ {X Y} → T∞ X → (X → T⁺ Y) → T⁺ Y
bindF⁺ : ∀ {X Y} → Step X (T∞ X) → (X → T⁺ Y) → T⁺ Y
m ⁺=<< f = bindF⁺ (force m) f
bindF⁺ (done x)            f = f x
bindF⁺ (node (call o a k)) f = call⁺ (call o a (λ b → k b >>=∞ λ x → forget⁺ (f x)))

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
M eff⁺ X = T⁺ X
M eff  X = T∞ X

bind : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bind pure m f = f m
bind act  m f = m >>=T f
bind eff⁺ m f = m >>=⁺ λ x → forget⁺ (f x)
bind eff  m f = m >>=∞ f

-- The monad morphisms along the order.
sub : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
sub ⊑-pure m = m
sub ⊑-pa   m = returnT m
sub ⊑-pe   m = return∞ m
sub ⊑-act  m = m
sub ⊑-ae   m = embed m
sub ⊑-g    m = m
sub ⊑-ge   m = forget⁺ m
sub ⊑-eff  m = m

-- A grade with a unit (every grade but the guard) returns a value.
return : ∀ {π} → pure ⊑π π → ∀ {X} → X → M π X
return u x = sub u x

fmap : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmap pure f m = f m
fmap act  f m = m >>=T λ x → returnT (f x)
fmap eff⁺ f m = m >>=⁺ λ x → return∞ (f x)
fmap eff  f m = m >>=∞ λ x → return∞ (f x)

-- Every grade embeds into `T∞`: what a computation is observed as.
toT∞ : ∀ π {X} → M π X → T∞ X
toT∞ pure m = return∞ m
toT∞ act  m = embed m
toT∞ eff⁺ m = forget⁺ m
toT∞ eff  m = m

-- Running a `π₁` computation, then a `π₂` one: the whole is at `π₁ ·p π₂`.
bindᵍ : ∀ π₁ π₂ {X Y} → M π₁ X → (X → M π₂ Y) → M (π₁ ·p π₂) Y
bindᵍ pure π₂   m f = f m
bindᵍ act  pure m f = m >>=T λ x → returnT (f x)
bindᵍ act  act  m f = m >>=T f
bindᵍ act  eff⁺ m f = embed m ⁺=<< f
bindᵍ act  eff  m f = embed m >>=∞ f
bindᵍ eff⁺ pure m f = m >>=⁺ λ x → return∞ (f x)
bindᵍ eff⁺ act  m f = m >>=⁺ λ x → embed (f x)
bindᵍ eff⁺ eff⁺ m f = m >>=⁺ λ x → forget⁺ (f x)
bindᵍ eff⁺ eff  m f = m >>=⁺ f
bindᵍ eff  pure m f = m >>=∞ λ x → return∞ (f x)
bindᵍ eff  act  m f = m >>=∞ λ x → embed (f x)
bindᵍ eff  eff⁺ m f = m ⁺=<< f
bindᵍ eff  eff  m f = m >>=∞ f

-- Equal computations: equal values and finite trees; bisimilar infinite ones.
EqM : ∀ π {X : Set} → M π X → M π X → Set
EqM pure m m′ = m ≡ m′
EqM act  m m′ = m ≡ m′
EqM eff⁺ m m′ = forget⁺ m ≈ forget⁺ m′
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
-- The server: guarded iteration
------------------------------------------------------------------------

-- Performing one call of an operation: the generic effect — in a computation
-- that returns, in one that need not, and guarded.
performT : ∀ {A} → Layer Σ A → T A
performT (call o a k) = roll (node (call o a (λ b → returnT (k b))))

perform : ∀ {A} → Layer Σ A → T∞ A
force (perform (call o a k)) = node (call o a (λ b → return∞ (k b)))

perform⁺ : ∀ {A} → Layer Σ A → T⁺ A
perform⁺ (call o a k) = call⁺ (call o a (λ b → return∞ (k b)))

-- The unique solution of `iter∞ f a = [ return , (λ m → m >>= [ return , iter∞ f ]) ] (f a)`
-- (`Spec.Metatheory`): end at once with a `B`, or perform the guarded round
-- and continue from its result.
iter∞     : ∀ {A B : Set} → (A → B ⊎ T⁺ (B ⊎ A)) → A → T∞ B
iterStart : ∀ {A B : Set} → (A → B ⊎ T⁺ (B ⊎ A)) → B ⊎ T⁺ (B ⊎ A) → Step B (T∞ B)
iterTree  : ∀ {A B : Set} → (A → B ⊎ T⁺ (B ⊎ A)) → T∞ (B ⊎ A) → T∞ B
iterStep  : ∀ {A B : Set} → (A → B ⊎ T⁺ (B ⊎ A)) → Step (B ⊎ A) (T∞ (B ⊎ A)) → Step B (T∞ B)
force (iter∞ f a) = iterStart f (f a)
iterStart f (inj₁ b)                   = done b
iterStart f (inj₂ (call⁺ (call o x k))) = node (call o x (λ r → iterTree f (k r)))
force (iterTree f m) = iterStep f (force m)
iterStep f (done (inj₁ b))     = done b
iterStep f (done (inj₂ a))     = iterStart f (f a)
iterStep f (node (call o x k)) = node (call o x (λ r → iterTree f (k r)))
