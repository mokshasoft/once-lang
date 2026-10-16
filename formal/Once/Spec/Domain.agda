{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Domain — what a value of each type is.
--
-- One value domain. A pure arrow is a total function, an effectful one a
-- function into its grade's monad (`Spec.Effect`); an erased arrow takes no
-- argument. `μ F` is the initial algebra of `F`'s polynomial functor, `ν F f`
-- the final coalgebra of `M f ∘ F` (its unfold is `Spec.Effect.ana`).
--
-- With it: the fold on the polynomial functors (a product layer left first),
-- the action of `ν` on the monad morphism `pure → act`, and the conversion
-- each subtyping derivation means. Everything is stated at a closed instance
-- `σ` of the type variables.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Domain (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Once.Spec.Grade using (Finite; pureᶠ; actᶠ; fin; Purity; pure; act; eff; mk-kind; Zero; One; Many; _⊑π_; ⊑-pure; ⊑-pa; ⊑-act)
open import Once.Spec.Type
  using (Ty; Type; Fun; var; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; Int; Float; K; Id; _⊕_; _⊗_; ⟦_⟧F; TySub; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Signature using (BTy; unit; void; int; float; ⌜_⌝; ⟦_⟧ᵇ; Layer; call)
import Once.Spec.Signature as S
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS)
open import Once.Spec.Effect Σ using (M; return; bind; fmap; sub; T; roll; done; returnT; νM; module νM; ana)
open νM using (outν)

------------------------------------------------------------------------
-- The value domain
------------------------------------------------------------------------

⟦_⟧ᵛ : Type → Set
code : Fun 0 → SFunctor
⟦ var () ⟧ᵛ
⟦ Unit ⟧ᵛ  = ⊤
⟦ Void ⟧ᵛ  = ⊥
⟦ A * B ⟧ᵛ = ⟦ A ⟧ᵛ × ⟦ B ⟧ᵛ
⟦ A + B ⟧ᵛ = ⟦ A ⟧ᵛ ⊎ ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᵛ = ⊤ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind One  π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ μ F ⟧ᵛ   = μS (code F)
⟦ ν F f ⟧ᵛ = νM f (code F)
⟦ Int ⟧ᵛ   = Carrier
⟦ Float ⟧ᵛ = Carrier
code (K A)   = SK ⟦ A ⟧ᵛ
code Id      = SId
code (F ⊕ G) = code F S⊕ code G
code (F ⊗ G) = code F S⊗ code G

------------------------------------------------------------------------
-- A base type's values are its values as a type; a functor applied to a type
-- is the polynomial functor applied to its values
--
-- (Two value domains meet here, canonically isomorphic: a first-order type's
-- values do not depend on Σ — they are what the world takes and answers —
-- while a general type's do, since an arrow runs Σ's calls. `toB`/`fromB` is
-- that isomorphism, the identity on each value.)
------------------------------------------------------------------------

module _ {m : ℕ} (σ : TySub m 0) where

  toB   : ∀ b → ⟦ ⌜ b ⌝ ⟨ σ ⟩ ⟧ᵛ → ⟦ b ⟧ᵇ
  fromB : ∀ b → ⟦ b ⟧ᵇ → ⟦ ⌜ b ⌝ ⟨ σ ⟩ ⟧ᵛ
  toB unit  x = x
  toB void  x = x
  toB int   x = x
  toB float x = x
  toB (a S.* b) (x , y)  = toB a x , toB b y
  toB (a S.+ b) (inj₁ x) = inj₁ (toB a x)
  toB (a S.+ b) (inj₂ y) = inj₂ (toB b y)
  fromB unit  x = x
  fromB void  x = x
  fromB int   x = x
  fromB float x = x
  fromB (a S.* b) (x , y)  = fromB a x , fromB b y
  fromB (a S.+ b) (inj₁ x) = inj₁ (fromB a x)
  fromB (a S.+ b) (inj₂ y) = inj₂ (fromB b y)

  toL   : ∀ (F : Fun m) (X : Ty m) → ⟦ ⟦ F ⟧F X ⟨ σ ⟩ ⟧ᵛ → ⟦ code (F ⟨ σ ⟩F) ⟧SF ⟦ X ⟨ σ ⟩ ⟧ᵛ
  fromL : ∀ (F : Fun m) (X : Ty m) → ⟦ code (F ⟨ σ ⟩F) ⟧SF ⟦ X ⟨ σ ⟩ ⟧ᵛ → ⟦ ⟦ F ⟧F X ⟨ σ ⟩ ⟧ᵛ
  toL (K A)   X x        = x
  toL Id      X x        = x
  toL (F ⊕ G) X (inj₁ x) = inj₁ (toL F X x)
  toL (F ⊕ G) X (inj₂ y) = inj₂ (toL G X y)
  toL (F ⊗ G) X (x , y)  = toL F X x , toL G X y
  fromL (K A)   X x        = x
  fromL Id      X x        = x
  fromL (F ⊕ G) X (inj₁ x) = inj₁ (fromL F X x)
  fromL (F ⊕ G) X (inj₂ y) = inj₂ (fromL G X y)
  fromL (F ⊗ G) X (x , y)  = fromL F X x , fromL G X y

------------------------------------------------------------------------
-- The fold: the algebra at each layer, the layer's recursive positions first,
-- left to right
------------------------------------------------------------------------

foldM  : ∀ π (G : SFunctor) {X : Set} → (⟦ G ⟧SF X → M π X) → μS G → M π X
layerM : ∀ π (G : SFunctor) (H : SFunctor) {X : Set} → (⟦ G ⟧SF X → M π X) → ⟦ H ⟧SF (μS G) → M π (⟦ H ⟧SF X)
foldM π G alg (inS x) = bind π (layerM π G G alg x) alg
layerM π G (SK B)     alg x        = return π x
layerM π G SId        alg x        = foldM π G alg x
layerM π G (H₁ S⊕ H₂) alg (inj₁ x) = fmap π inj₁ (layerM π G H₁ alg x)
layerM π G (H₁ S⊕ H₂) alg (inj₂ y) = fmap π inj₂ (layerM π G H₂ alg y)
layerM π G (H₁ S⊗ H₂) alg (x , y)  =
  bind π (layerM π G H₁ alg x) λ u → bind π (layerM π G H₂ alg y) λ v → return π (u , v)

------------------------------------------------------------------------
-- ν on the monad morphism `pure → act`: the unfold that returns each layer
-- as a block with no call
------------------------------------------------------------------------

subν : ∀ {f f′} → fin f ⊑π fin f′ → ∀ (G : SFunctor) → νM f G → νM f′ G
subν ⊑-pure G v = v
subν ⊑-pa   G v = ana actᶠ G (λ u → returnT (outν u)) v
subν ⊑-act  G v = v

------------------------------------------------------------------------
-- What a subtyping derivation means: its conversion
------------------------------------------------------------------------

conv : ∀ {m} (σ : TySub m 0) {A B : Ty m} → A <: B → ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ
conv σ sub-void  x = ⊥-elim x
conv σ sub-var   x = x
conv σ sub-unit  x = x
conv σ sub-int   x = x
conv σ sub-float x = x
conv σ (sub-arr {q = Zero} {π = π} a b g) f = λ u → sub g (fmap π (conv σ b) (f u))
conv σ (sub-arr {q = One}  {π = π} a b g) f = λ x → sub g (fmap π (conv σ b) (f (conv σ a x)))
conv σ (sub-arr {q = Many} {π = π} a b g) f = λ x → sub g (fmap π (conv σ b) (f (conv σ a x)))
conv σ (sub-* a b) (x , y)  = conv σ a x , conv σ b y
conv σ (sub-+ a b) (inj₁ x) = inj₁ (conv σ a x)
conv σ (sub-+ a b) (inj₂ y) = inj₂ (conv σ b y)
conv σ sub-μ x = x
conv σ (sub-ν {F = F} g) v = subν g (code (F ⟨ σ ⟩F)) v

------------------------------------------------------------------------
-- A function run at each recursive position of a layer, left to right: what
-- the fold's laws are stated with
------------------------------------------------------------------------

traverseM : ∀ π (H : SFunctor) {X Y : Set} → (X → M π Y) → ⟦ H ⟧SF X → M π (⟦ H ⟧SF Y)
traverseM π (SK B)     f x        = return π x
traverseM π SId        f x        = f x
traverseM π (H₁ S⊕ H₂) f (inj₁ x) = fmap π inj₁ (traverseM π H₁ f x)
traverseM π (H₁ S⊕ H₂) f (inj₂ y) = fmap π inj₂ (traverseM π H₂ f y)
traverseM π (H₁ S⊗ H₂) f (x , y)  =
  bind π (traverseM π H₁ f x) λ u → bind π (traverseM π H₂ f y) λ v → return π (u , v)
