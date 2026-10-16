{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Effect — what an effectful computation is.
--
-- One functor, `Step X Y = X + H_Σ Y`: the computation is done with a value,
-- or it makes one call and continues from the answer. Its initial algebra is
-- a finite BLOCK of calls — `T X = μY. X + H_Σ Y`, the free monad.
--
-- A STREAM `νM f F` is the final coalgebra of `M f ∘ F`: each layer produced
-- at a finite grade `f` (as a value, or by a block). A computation that need
-- not stop runs blocks forever, each ending with the result or with what to
-- run next (D317) — the stream of blocks that ends with a value:
--
--   T∞ X = νY. T (X + Y) = νM act (K X ⊕ Id)
--
-- the coinductive resumption monad over `T`. So programs and effects have one
-- shape: finite folds inside the rounds of a loop, finite blocks inside
-- `T∞`; and THE LOOP is the stream unfold at `K B ⊕ Id`: any round
-- `A → T (B + A)` that ends with a `B` or continues with the next state. A
-- block may perform no event: a silent round is an empty block.
--
-- Equality of streams (and so of `T∞` computations) as trees is
-- bisimilarity (`_≈ν_`), which sees where the blocks end; when two meanings
-- are the same is decided by what they do (`Spec.Equivalence`).
--
-- A grade chooses the monad: `M pure = Id`, `M act = T`, `M eff = T∞`, with
-- the monad morphisms along the chain (`sub`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call)

module Once.Spec.Effect (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Finite; pureᶠ; actᶠ; fin; Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)

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
-- Streams: the final coalgebras of `M f ∘ F`, at a finite grade
------------------------------------------------------------------------

-- The monad of a finite grade.
Mᶠ : Finite → Set → Set
Mᶠ pureᶠ X = X
Mᶠ actᶠ  X = T X

record νM (f : Finite) (F : SFunctor) : Set where
  coinductive
  field outν : Mᶠ f (⟦ F ⟧SF (νM f F))
open νM

-- The unfold (anamorphism): each forced layer runs the coalgebra.
ana : ∀ (f : Finite) (G : SFunctor) {X : Set} → (X → Mᶠ f (⟦ G ⟧SF X)) → X → νM f G
private
  anaP   : ∀ (G : SFunctor) {X : Set} → (X → ⟦ G ⟧SF X) → X → νM pureᶠ G
  mapP   : ∀ (G H : SFunctor) {X : Set} → (X → ⟦ G ⟧SF X) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM pureᶠ G)
  outν (anaP G c x) = mapP G G c (c x)
  mapP G (SK B)     c x        = x
  mapP G SId        c x        = anaP G c x
  mapP G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapP G H₁ c x)
  mapP G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapP G H₂ c y)
  mapP G (H₁ S⊗ H₂) c (x , y)  = mapP G H₁ c x , mapP G H₂ c y

  anaA   : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → X → νM actᶠ G
  treeA  : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → T (⟦ G ⟧SF X) → T (⟦ G ⟧SF (νM actᶠ G))
  mapA   : ∀ (G H : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM actᶠ G)
  outν (anaA G c x) = treeA G c (c x)
  treeA G c (roll (done l))            = roll (done (mapA G G c l))
  treeA G c (roll (node (call o a k))) = roll (node (call o a (λ b → treeA G c (k b))))
  mapA G (SK B)     c x        = x
  mapA G SId        c x        = anaA G c x
  mapA G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapA G H₁ c x)
  mapA G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapA G H₂ c y)
  mapA G (H₁ S⊗ H₂) c (x , y)  = mapA G H₁ c x , mapA G H₂ c y
ana pureᶠ = anaP
ana actᶠ  = anaA

------------------------------------------------------------------------
-- Bisimilarity of streams: equal constants, the same blocks, bisimilar
-- recursive positions
------------------------------------------------------------------------

LayerEq : ∀ (G : SFunctor) {X : Set} → (X → X → Set) → ⟦ G ⟧SF X → ⟦ G ⟧SF X → Set
LayerEq (SK B)   R x y = x ≡ y
LayerEq SId      R x y = R x y
LayerEq (G S⊕ H) R (inj₁ x) (inj₁ y) = LayerEq G R x y
LayerEq (G S⊕ H) R (inj₂ x) (inj₂ y) = LayerEq H R x y
LayerEq (G S⊕ H) R (inj₁ _) (inj₂ _) = ⊥
LayerEq (G S⊕ H) R (inj₂ _) (inj₁ _) = ⊥
LayerEq (G S⊗ H) R (x , x′) (y , y′) = LayerEq G R x y × LayerEq H R x′ y′

-- Two blocks: the same calls, related layers where they end.
data BlockEq {Z : Set} (R : Z → Z → Set) : T Z → T Z → Set where
  done≈ : ∀ {z z′} → R z z′ → BlockEq R (roll (done z)) (roll (done z′))
  node≈ : ∀ {o a k k′} → (∀ b → BlockEq R (k b) (k′ b))
        → BlockEq R (roll (node (call o a k))) (roll (node (call o a k′)))

-- One layer at a finite grade.
EqLayer : ∀ (f : Finite) {Z : Set} → (Z → Z → Set) → Mᶠ f Z → Mᶠ f Z → Set
EqLayer pureᶠ R = R
EqLayer actᶠ  R = BlockEq R

record _≈ν_ {f : Finite} {G : SFunctor} (v w : νM f G) : Set where
  coinductive
  field force≈ : EqLayer f (LayerEq G _≈ν_) (outν v) (outν w)
open _≈ν_

infix 4 _≈ν_

------------------------------------------------------------------------
-- Blocks forever: the resumption monad, the stream of blocks
------------------------------------------------------------------------

T∞ : Set → Set
T∞ X = νM actᶠ (SK X S⊕ SId)

-- One block, ending with the value or with what to run next.
force : ∀ {X} → T∞ X → T (X ⊎ T∞ X)
force = outν

-- Bisimilar computations: the same blocks forever, equal values at the ends.
_≈_ : ∀ {X} → T∞ X → T∞ X → Set
_≈_ = _≈ν_

infix 4 _≈_

return∞ : ∀ {X} → X → T∞ X
outν (return∞ x) = returnT (inj₁ x)

-- Run the first block; at its result, the continuation's first block follows
-- in the same block; at a block's end, continue.
_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
outν (m >>=∞ f) = bindBlock (outν m) f
bindBlock (roll (done (inj₁ x)))     f = outν (f x)
bindBlock (roll (done (inj₂ m)))     f = roll (done (inj₂ (m >>=∞ f)))
bindBlock (roll (node (call o a k))) f = roll (node (call o a (λ b → bindBlock (k b) f)))

-- One block is a computation: the monad morphism `T → T∞`.
embed : ∀ {X} → T X → T∞ X
outν (embed m) = mapT inj₁ m

-- THE LOOP: the anamorphism at `K B ⊕ Id`. Each round runs the block `c a`; where
-- it ends with a `B` the loop returns it, where it ends with the next state
-- the loop continues from it.
loop : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loop {B = B} c = ana actᶠ (SK B S⊕ SId) c

------------------------------------------------------------------------
-- The grades
------------------------------------------------------------------------

M : Purity → Set → Set
M (fin f) X = Mᶠ f X
M eff     X = T∞ X

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

-- Equal computations as trees, at every grade: bisimilar in `T∞`.
EqM : ∀ π {X : Set} → M π X → M π X → Set
EqM π m m′ = toT∞ π m ≈ toT∞ π m′

------------------------------------------------------------------------
-- Calls
------------------------------------------------------------------------

-- Performing one call of an operation: the generic effect, as one block.
performT : ∀ {A} → Layer Σ A → T A
performT (call o a k) = roll (node (call o a (λ b → returnT (k b))))
