{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- POC 0.120-A — the resumption monad IS a stream type.
--
-- Claim: `T∞ X` can be defined as `νM act (K X ⊕ Id)`, the final coalgebra
-- of `T ∘ (X + −)`, so that the effect monad and the streams are one
-- construction and the loop is the stream unfold at `K B ⊕ Id`.
-- Finding: in one mutual block with `M` (allowing `ν F eff`), positivity
-- fails — an `eff` stream's layer type puts the stream inside a functor code.
-- Without `ν F eff` (streams have `pure` or `act` layers) no mutual block is
-- needed: `νM` first, then `T∞`, then `M`.
-- Checks: positivity, guardedness of bind and of the unfold, and the loop's
-- computation law by `refl`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; Layer; call)

module POC0120.ResumptionAsStream (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)

data Purity : Set where
  pure act eff : Purity

-- Blocks: the free monad.
data Step (X Y : Set) : Set where
  done : X → Step X Y
  node : Layer Σ Y → Step X Y

data T (X : Set) : Set where
  roll : Step X (T X) → T X

returnT : ∀ {X} → X → T X
returnT x = roll (done x)

_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
roll (done x)            >>=T f = f x
roll (node (call o a k)) >>=T f = roll (node (call o a (λ b → k b >>=T f)))

mapT : ∀ {X Y} → (X → Y) → T X → T Y
mapT f m = m >>=T λ x → returnT (f x)

-- Streams have `pure` or `act` layers (no `ν F eff`: no unfold builds one).
data SGrade : Set where
  spure sact : SGrade

MS : SGrade → Set → Set
MS spure X = X
MS sact  X = T X

record νM (g : SGrade) (F : SFunctor) : Set where
  coinductive
  field outν : MS g (⟦ F ⟧SF (νM g F))
open νM

-- The resumption monad is the stream of `act` blocks that ends with a value.
T∞ : Set → Set
T∞ X = νM sact (SK X S⊕ SId)

M : Purity → Set → Set
M pure X = X
M act  X = T X
M eff  X = T∞ X

-- `force` is `outν`: one block, ending with the value or the rest.
force : ∀ {X} → T∞ X → T (X ⊎ T∞ X)
force = outν

return∞ : ∀ {X} → X → T∞ X
outν (return∞ x) = returnT (inj₁ x)

_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
outν (m >>=∞ f) = bindBlock (outν m) f
bindBlock (roll (done (inj₁ x)))     f = outν (f x)
bindBlock (roll (done (inj₂ m)))     f = roll (done (inj₂ (m >>=∞ f)))
bindBlock (roll (node (call o a k))) f = roll (node (call o a (λ b → bindBlock (k b) f)))

embed : ∀ {X} → T X → T∞ X
outν (embed m) = mapT inj₁ m

-- The stream unfold at `act` (as `Spec.Domain.anaA`).
anaA  : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → X → νM sact G
treeA : ∀ (G : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → T (⟦ G ⟧SF X) → T (⟦ G ⟧SF (νM sact G))
mapA  : ∀ (G H : SFunctor) {X : Set} → (X → T (⟦ G ⟧SF X)) → ⟦ H ⟧SF X → ⟦ H ⟧SF (νM sact G)
outν (anaA G c x) = treeA G c (c x)
treeA G c (roll (done l))            = roll (done (mapA G G c l))
treeA G c (roll (node (call o a k))) = roll (node (call o a (λ b → treeA G c (k b))))
mapA G (SK B)     c x        = x
mapA G SId        c x        = anaA G c x
mapA G (H₁ S⊕ H₂) c (inj₁ x) = inj₁ (mapA G H₁ c x)
mapA G (H₁ S⊕ H₂) c (inj₂ y) = inj₂ (mapA G H₂ c y)
mapA G (H₁ S⊗ H₂) c (x , y)  = mapA G H₁ c x , mapA G H₂ c y

-- THE LOOP is the unfold at `K B ⊕ Id`: no definition of its own.
loop : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loop {A} {B} c = anaA (SK B S⊕ SId) c

-- Its computation law, by `refl`: a round, then the result or the loop again.
loop-out : ∀ {A B : Set} (c : A → T (B ⊎ A)) (a : A)
         → force (loop c a) ≡ treeA (SK B S⊕ SId) c (c a)
loop-out c a = refl

-- … and at a finished round, the next round is the loop from the next state.
loop-next : ∀ {A B : Set} (c : A → T (B ⊎ A)) (a′ : A)
          → treeA (SK B S⊕ SId) c (returnT (inj₂ a′)) ≡ roll (done (inj₂ (loop c a′)))
loop-next c a′ = refl

------------------------------------------------------------------------
-- One bisimilarity for streams; `T∞`'s is its instance at `K X ⊕ Id`
------------------------------------------------------------------------

-- One layer: equal constants, related recursive positions.
LayerEq : ∀ (G : SFunctor) {X : Set} → (X → X → Set) → ⟦ G ⟧SF X → ⟦ G ⟧SF X → Set
LayerEq (SK B)   R x y = x ≡ y
LayerEq SId      R x y = R x y
LayerEq (G S⊕ H) R (inj₁ x) (inj₁ y) = LayerEq G R x y
LayerEq (G S⊕ H) R (inj₂ x) (inj₂ y) = LayerEq H R x y
LayerEq (G S⊕ H) R (inj₁ _) (inj₂ _) = ⊥
LayerEq (G S⊕ H) R (inj₂ _) (inj₁ _) = ⊥
LayerEq (G S⊗ H) R (x , x′) (y , y′) = LayerEq G R x y × LayerEq H R x′ y′

-- The same blocks, with related layers at their ends.
data BlockEq (G : SFunctor) (R : νM sact G → νM sact G → Set) : T (⟦ G ⟧SF (νM sact G)) → T (⟦ G ⟧SF (νM sact G)) → Set where
  done≈ : ∀ {l l′} → LayerEq G R l l′ → BlockEq G R (roll (done l)) (roll (done l′))
  node≈ : ∀ {o a k k′} → (∀ b → BlockEq G R (k b) (k′ b)) → BlockEq G R (roll (node (call o a k))) (roll (node (call o a k′)))

record Bisim (G : SFunctor) (v w : νM sact G) : Set where
  coinductive
  field force≈ : BlockEq G (Bisim G) (outν v) (outν w)
open Bisim

-- `T∞`'s bisimilarity: at `K X ⊕ Id`, a layer is the value (`≡`) or the
-- rest of the computation (bisimilar) — exactly `Spec.Effect`'s `BlockEq`.
_≈_ : ∀ {X} → T∞ X → T∞ X → Set
_≈_ {X} = Bisim (SK X S⊕ SId)

returned≈ : ∀ {X} {x : X} → BlockEq (SK X S⊕ SId) _≈_ (roll (done (inj₁ x))) (roll (done (inj₁ x)))
returned≈ = done≈ refl

next≈ : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → BlockEq (SK X S⊕ SId) _≈_ (roll (done (inj₂ m))) (roll (done (inj₂ m′)))
next≈ p = done≈ p

-- Bisimilarity is reflexive (a coinductive proof through the generic layer).
≈-refl  : ∀ (G : SFunctor) (v : νM sact G) → Bisim G v v
≈-reflB : ∀ (G : SFunctor) (t : T (⟦ G ⟧SF (νM sact G))) → BlockEq G (Bisim G) t t
≈-reflL : ∀ (G H : SFunctor) (l : ⟦ H ⟧SF (νM sact G)) → LayerEq H (Bisim G) l l
force≈ (≈-refl G v) = ≈-reflB G (outν v)
≈-reflB G (roll (done l))            = done≈ (≈-reflL G G l)
≈-reflB G (roll (node (call o a k))) = node≈ λ b → ≈-reflB G (k b)
≈-reflL G (SK B)     x        = refl
≈-reflL G SId        v        = ≈-refl G v
≈-reflL G (H₁ S⊕ H₂) (inj₁ x) = ≈-reflL G H₁ x
≈-reflL G (H₁ S⊕ H₂) (inj₂ y) = ≈-reflL G H₂ y
≈-reflL G (H₁ S⊗ H₂) (x , y)  = ≈-reflL G H₁ x , ≈-reflL G H₂ y
