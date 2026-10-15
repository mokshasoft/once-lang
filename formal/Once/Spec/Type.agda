{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type — the types: the objects of the category.
--
--   Unit, Void      the terminal and the initial object;
--   A * B, A + B    product and coproduct;
--   A ⇒[ k ] B      the exponential, graded by `k` (`Spec.Grade`);
--   μ F             the initial algebra of the polynomial functor `F`;
--   ν F π           the final coalgebra of `F`, each layer produced at
--                   effect `π` (`ν F eff` is the final `T∞ ∘ F`-coalgebra);
--   Int, Float      the target's machine integer and floating-point number;
--   var i           the `i`-th type variable of a polymorphic definition.
--
-- `Ty m` has `m` type variables; a GROUND type is a `Ty 0` (`Type`). A
-- polymorphic definition is typed once over its variables, each of a KIND:
-- `base` (it may occur under a functor constant) or `any`.
------------------------------------------------------------------------

module Once.Spec.Type where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (ArrowKind; Purity)

mutual
  data Ty (m : ℕ) : Set where
    var            : Fin m → Ty m
    Unit Void      : Ty m
    _*_ _+_        : Ty m → Ty m → Ty m
    _⇒[_]_         : Ty m → ArrowKind → Ty m → Ty m
    μ              : Fun m → Ty m
    ν              : Fun m → Purity → Ty m
    Int Float      : Ty m

  -- The polynomial functors: a constant, the recursive position, sum and
  -- product.
  data Fun (m : ℕ) : Set where
    K       : Ty m → Fun m
    Id      : Fun m
    _⊕_ _⊗_ : Fun m → Fun m → Fun m

infixr 30 _⇒[_]_
infixr 40 _+_
infixr 50 _*_
infixr 40 _⊕_
infixr 50 _⊗_

Type : Set
Type = Ty 0

-- A functor applied to a type.
⟦_⟧F : ∀ {m} → Fun m → Ty m → Ty m
⟦ K A ⟧F   X = A
⟦ Id ⟧F    X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X + ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X * ⟦ G ⟧F X

------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------

data Kind : Set where
  base any : Kind

KCtx : ℕ → Set
KCtx m = Fin m → Kind

-- The BASE types: first-order data, what an operation of the signature takes
-- and returns and what a functor constant may be.
data Base {m} (Δ : KCtx m) : Ty m → Set where
  b-var   : ∀ {i} → Δ i ≡ base → Base Δ (var i)
  b-Unit  : Base Δ Unit
  b-Void  : Base Δ Void
  b-Int   : Base Δ Int
  b-Float : Base Δ Float
  b-*     : ∀ {A B} → Base Δ A → Base Δ B → Base Δ (A * B)
  b-+     : ∀ {A B} → Base Δ A → Base Δ B → Base Δ (A + B)

-- A functor is well formed when each constant is a base type.
data WFFun {m} (Δ : KCtx m) : Fun m → Set where
  wf-K  : ∀ {A} → Base Δ A → WFFun Δ (K A)
  wf-Id : WFFun Δ Id
  wf-⊕  : ∀ {F G} → WFFun Δ F → WFFun Δ G → WFFun Δ (F ⊕ G)
  wf-⊗  : ∀ {F G} → WFFun Δ F → WFFun Δ G → WFFun Δ (F ⊗ G)

-- No type variables: the kinding context of a ground type.
∅ₖ : KCtx 0
∅ₖ ()

------------------------------------------------------------------------
-- Substitution: a polymorphic definition used at an instance
------------------------------------------------------------------------

TySub : ℕ → ℕ → Set
TySub m k = Fin m → Ty k

mutual
  _⟨_⟩ : ∀ {m k} → Ty m → TySub m k → Ty k
  var i        ⟨ σ ⟩ = σ i
  Unit         ⟨ σ ⟩ = Unit
  Void         ⟨ σ ⟩ = Void
  (A * B)      ⟨ σ ⟩ = A ⟨ σ ⟩ * B ⟨ σ ⟩
  (A + B)      ⟨ σ ⟩ = A ⟨ σ ⟩ + B ⟨ σ ⟩
  (A ⇒[ k ] B) ⟨ σ ⟩ = A ⟨ σ ⟩ ⇒[ k ] B ⟨ σ ⟩
  μ F          ⟨ σ ⟩ = μ (F ⟨ σ ⟩F)
  ν F π        ⟨ σ ⟩ = ν (F ⟨ σ ⟩F) π
  Int          ⟨ σ ⟩ = Int
  Float        ⟨ σ ⟩ = Float

  _⟨_⟩F : ∀ {m k} → Fun m → TySub m k → Fun k
  K A     ⟨ σ ⟩F = K (A ⟨ σ ⟩)
  Id      ⟨ σ ⟩F = Id
  (F ⊕ G) ⟨ σ ⟩F = F ⟨ σ ⟩F ⊕ G ⟨ σ ⟩F
  (F ⊗ G) ⟨ σ ⟩F = F ⟨ σ ⟩F ⊗ G ⟨ σ ⟩F

infixl 60 _⟨_⟩ _⟨_⟩F

-- An instance RESPECTS the kinds when each base variable becomes a base type.
Respects : ∀ {m k} → KCtx m → KCtx k → TySub m k → Set
Respects Δ Δ′ σ = ∀ i → Δ i ≡ base → Base Δ′ (σ i)

-- What the meaning of a reference to a definition at an instance needs: an
-- instance of an instance is an instance — it composes, and it keeps
-- respecting the kinds.
base-⟨⟩ : ∀ {m k} {Δ : KCtx m} {Δ′ : KCtx k} {σ : TySub m k} {A} → Respects Δ Δ′ σ → Base Δ A → Base Δ′ (A ⟨ σ ⟩)
base-⟨⟩ r (b-var e) = r _ e
base-⟨⟩ r b-Unit    = b-Unit
base-⟨⟩ r b-Void    = b-Void
base-⟨⟩ r b-Int     = b-Int
base-⟨⟩ r b-Float   = b-Float
base-⟨⟩ r (b-* a b) = b-* (base-⟨⟩ r a) (base-⟨⟩ r b)
base-⟨⟩ r (b-+ a b) = b-+ (base-⟨⟩ r a) (base-⟨⟩ r b)

respects-∘ : ∀ {m k l} {Δ : KCtx m} {Δ′ : KCtx k} {Δ″ : KCtx l} {σ : TySub m k} {τ : TySub k l}
           → Respects Δ Δ′ σ → Respects Δ′ Δ″ τ → Respects Δ Δ″ (λ i → σ i ⟨ τ ⟩)
respects-∘ rσ rτ i e = base-⟨⟩ rτ (rσ i e)

mutual
  ⟨⟩-∘ : ∀ {m k l} (A : Ty m) (σ : TySub m k) (τ : TySub k l) → A ⟨ σ ⟩ ⟨ τ ⟩ ≡ A ⟨ (λ i → σ i ⟨ τ ⟩) ⟩
  ⟨⟩-∘ (var i)      σ τ = refl
  ⟨⟩-∘ Unit         σ τ = refl
  ⟨⟩-∘ Void         σ τ = refl
  ⟨⟩-∘ (A * B)      σ τ = cong₂ _*_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A + B)      σ τ = cong₂ _+_ (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (A ⇒[ k ] B) σ τ = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-∘ A σ τ) (⟨⟩-∘ B σ τ)
  ⟨⟩-∘ (μ F)        σ τ = cong μ (⟨⟩F-∘ F σ τ)
  ⟨⟩-∘ (ν F π)      σ τ = cong (λ G → ν G π) (⟨⟩F-∘ F σ τ)
  ⟨⟩-∘ Int          σ τ = refl
  ⟨⟩-∘ Float        σ τ = refl

  ⟨⟩F-∘ : ∀ {m k l} (F : Fun m) (σ : TySub m k) (τ : TySub k l) → F ⟨ σ ⟩F ⟨ τ ⟩F ≡ F ⟨ (λ i → σ i ⟨ τ ⟩) ⟩F
  ⟨⟩F-∘ (K A)   σ τ = cong K (⟨⟩-∘ A σ τ)
  ⟨⟩F-∘ Id      σ τ = refl
  ⟨⟩F-∘ (F ⊕ G) σ τ = cong₂ _⊕_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)
  ⟨⟩F-∘ (F ⊗ G) σ τ = cong₂ _⊗_ (⟨⟩F-∘ F σ τ) (⟨⟩F-∘ G σ τ)

------------------------------------------------------------------------
-- Occurrence of a type variable
------------------------------------------------------------------------

-- A type variable occurs in a type.
data Occurs  {m} (i : Fin m) : Ty m → Set
data OccursF {m} (i : Fin m) : Fun m → Set
data Occurs i where
  o-var  : Occurs i (var i)
  o-*ˡ   : ∀ {A B} → Occurs i A → Occurs i (A * B)
  o-*ʳ   : ∀ {A B} → Occurs i B → Occurs i (A * B)
  o-+ˡ   : ∀ {A B} → Occurs i A → Occurs i (A + B)
  o-+ʳ   : ∀ {A B} → Occurs i B → Occurs i (A + B)
  o-⇒ˡ   : ∀ {A k B} → Occurs i A → Occurs i (A ⇒[ k ] B)
  o-⇒ʳ   : ∀ {A k B} → Occurs i B → Occurs i (A ⇒[ k ] B)
  o-μ    : ∀ {F} → OccursF i F → Occurs i (μ F)
  o-ν    : ∀ {F π} → OccursF i F → Occurs i (ν F π)
data OccursF i where
  o-K  : ∀ {A} → Occurs i A → OccursF i (K A)
  o-⊕ˡ : ∀ {F G} → OccursF i F → OccursF i (F ⊕ G)
  o-⊕ʳ : ∀ {F G} → OccursF i G → OccursF i (F ⊕ G)
  o-⊗ˡ : ∀ {F G} → OccursF i F → OccursF i (F ⊗ G)
  o-⊗ʳ : ∀ {F G} → OccursF i G → OccursF i (F ⊗ G)
