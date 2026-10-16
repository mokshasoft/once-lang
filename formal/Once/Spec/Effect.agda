{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Effect — what an effectful computation is.
--
-- One functor, `Step X Y = X + H_Σ Y`: the computation is done with a value,
-- or it makes one call and continues from the answer. Its initial algebra is
-- a finite BLOCK of calls:
--
--   T X  = μY. X + H_Σ Y      finitely many events, then a value (or it
--                             halts) — the free monad;
--
-- and a computation that need not stop runs such blocks forever, each one
-- ending with the result or with what to run next (D317):
--
--   T∞ X = νY. T (X + Y)      the coinductive resumption monad over `T`.
--
-- So programs and effects have one shape: finite folds inside the rounds of a
-- loop, finite blocks inside `T∞`. A block may perform no event: a silent
-- round is an empty block, observed as a step of `Delay` (`Spec.Observation`).
-- Equality of `T∞` computations as trees is bisimilarity (`_≈_`), which sees
-- where the blocks end; when two meanings are the same is decided by what
-- they do (`Spec.Equivalence`).
--
-- A grade chooses the monad: `M pure = Id`, `M act = T`, `M eff = T∞`, with
-- the monad morphisms along the chain (`sub`).
--
-- THE LOOP (`loop`) is the anamorphism into `T∞ B`, the final coalgebra of
-- `T (B + −)`: any round `A → T (B + A)` that either ends with a `B` or
-- continues with the next state.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call)

module Once.Spec.Effect (Σ : Signature) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF)

------------------------------------------------------------------------
-- Blocks: the free monad
------------------------------------------------------------------------

data Step (X Y : Set) : Set where
  done : X → Step X Y
  node : Layer Σ Y → Step X Y

data T (X : Set) : Set where
  roll : Step X (T X) → T X

returnT : ∀ {X} → X → T X
returnT x = roll (done x)

infixl 1 _>>=T_ _>>=∞_
_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
roll (done x)              >>=T f = f x
roll (node (call o a k))   >>=T f = roll (node (call o a (λ b → k b >>=T f)))

mapT : ∀ {X Y} → (X → Y) → T X → T Y
mapT f m = m >>=T λ x → returnT (f x)

------------------------------------------------------------------------
-- Blocks forever: the coinductive resumption monad
------------------------------------------------------------------------

record T∞ (X : Set) : Set where
  coinductive
  field force : T (X ⊎ T∞ X)
open T∞

return∞ : ∀ {X} → X → T∞ X
force (return∞ x) = returnT (inj₁ x)

-- Run the first block; at its result, the continuation's first block follows
-- in the same block; at a block's end, continue.
_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
force (m >>=∞ f) = bindBlock (force m) f
bindBlock (roll (done (inj₁ x)))     f = force (f x)
bindBlock (roll (done (inj₂ m)))     f = roll (done (inj₂ (m >>=∞ f)))
bindBlock (roll (node (call o a k))) f = roll (node (call o a (λ b → bindBlock (k b) f)))

-- One block is a computation: the monad morphism `T → T∞`.
embed : ∀ {X} → T X → T∞ X
force (embed m) = mapT inj₁ m

------------------------------------------------------------------------
-- Bisimilarity: the same blocks forever, equal values at the ends
------------------------------------------------------------------------

data BlockEq {X : Set} (R : T∞ X → T∞ X → Set) : T (X ⊎ T∞ X) → T (X ⊎ T∞ X) → Set where
  return≈ : ∀ {x} → BlockEq R (roll (done (inj₁ x))) (roll (done (inj₁ x)))
  next≈   : ∀ {m m′} → R m m′ → BlockEq R (roll (done (inj₂ m))) (roll (done (inj₂ m′)))
  node≈   : ∀ {o a k k′} → (∀ b → BlockEq R (k b) (k′ b))
          → BlockEq R (roll (node (call o a k))) (roll (node (call o a k′)))

record _≈_ {X : Set} (m m′ : T∞ X) : Set where
  coinductive
  field force≈ : BlockEq _≈_ (force m) (force m′)
open _≈_

infix 4 _≈_

------------------------------------------------------------------------
-- The grades
------------------------------------------------------------------------

M : Purity → Set → Set
M pure X = X
M act  X = T X
M eff  X = T∞ X

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

return : ∀ π {X} → X → M π X
return pure x = x
return act  x = returnT x
return eff  x = return∞ x

fmap : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmap π f m = bind π m λ x → return π (f x)

-- Every grade embeds into `T∞`: what a computation is observed as.
toT∞ : ∀ π {X} → M π X → T∞ X
toT∞ pure m = return∞ m
toT∞ act  m = embed m
toT∞ eff  m = m

-- Running a `π₁` computation, then a `π₂` one: the whole is at the join.
bindᵍ : ∀ π₁ π₂ {X Y} → M π₁ X → (X → M π₂ Y) → M (π₁ ·p π₂) Y
bindᵍ pure π₂   m f = f m
bindᵍ act  pure m f = m >>=T λ x → returnT (f x)
bindᵍ act  act  m f = m >>=T f
bindᵍ act  eff  m f = embed m >>=∞ f
bindᵍ eff  pure m f = m >>=∞ λ x → return∞ (f x)
bindᵍ eff  act  m f = m >>=∞ λ x → embed (f x)
bindᵍ eff  eff  m f = m >>=∞ f

-- Equal computations as trees: equal values and blocks; bisimilar loops.
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
-- Calls, and the loop
------------------------------------------------------------------------

-- Performing one call of an operation: the generic effect, as one block.
performT : ∀ {A} → Layer Σ A → T A
performT (call o a k) = roll (node (call o a (λ b → returnT (k b))))

perform : ∀ {A} → Layer Σ A → T∞ A
perform l = embed (performT l)

-- THE LOOP: the anamorphism into the final coalgebra of `T (B + −)`. Each
-- round runs the block `c a`; where it ends with a `B` the loop returns it,
-- where it ends with the next state the loop continues from it.
loop      : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loopBlock : ∀ {A B : Set} → (A → T (B ⊎ A)) → T (B ⊎ A) → T (B ⊎ T∞ B)
force (loop c a) = loopBlock c (c a)
loopBlock c (roll (done (inj₁ b)))     = returnT (inj₁ b)
loopBlock c (roll (done (inj₂ a)))     = roll (done (inj₂ (loop c a)))
loopBlock c (roll (node (call o x k))) = roll (node (call o x (λ r → loopBlock c (k r))))
