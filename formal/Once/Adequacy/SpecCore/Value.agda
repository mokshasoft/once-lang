{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Value — two Spec meanings, related (plan 0.121
-- §3.5, the meaning relation; plan 0.122: the compiler's meaning IS the
-- Spec's, at the instance, so both sides are Spec values).
--
-- At ground types, `GR A A′` (a type read at a ground instance against the
-- type, `g⟨⟩`). Over it, a logical relation between Spec values:
--   * values: the same word at `Int`/`Float`; pairwise at `*`, the same side
--     at `+`; at an arrow, related arguments go to related computations; `μ`
--     layer by layer (`μR`); a stream coinductively, layer by layer (`νpR`,
--     and `νdR`, whose layers are blocks);
--   * computations at a grade (`MR`): a value at `pure`, a block at `act`
--     (`TR`: the same calls, related where they end), and at `eff` the
--     closure of blocks under going on (`T∞R`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Value (Σ : Signature) where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Spec.Signature as SSig
import Once.Spec.Polynomial as SPoly
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecCore.Index

------------------------------------------------------------------------
-- Base values
------------------------------------------------------------------------

-- A functor's constant (only base types occur).
BR : ∀ {A A′} → GR A A′ → SD.⟦ A ⟧ᵛ → SD.⟦ A′ ⟧ᵛ → Set
BR g-unit  _ _ = ⊤
BR g-void  _ _ = ⊤
BR g-int   x y = x ≡ y
BR g-float x y = x ≡ y
BR (g-* a b) (x , x′) (y , y′) = BR a x y × BR b x′ y′
BR (g-+ a b) (inj₁ x) (inj₁ y) = BR a x y
BR (g-+ a b) (inj₂ x) (inj₂ y) = BR b x y
BR (g-+ a b) (inj₁ _) (inj₂ _) = ⊥
BR (g-+ a b) (inj₂ _) (inj₁ _) = ⊥
BR (g-⇒ _ _) _ _ = ⊤
BR (g-μ _)   _ _ = ⊤
BR (g-ν _)   _ _ = ⊤

------------------------------------------------------------------------
-- Layers and data
------------------------------------------------------------------------

LayerR : ∀ {F F′} → GF F F′ → ∀ {X Y : Set} → (X → Y → Set)
       → SPoly.⟦ SD.code F ⟧SF X → SPoly.⟦ SD.code F′ ⟧SF Y → Set
LayerR (g-K a)   R x y = BR a x y
LayerR g-Id      R x y = R x y
LayerR (g-⊕ f g) R (inj₁ x) (inj₁ y) = LayerR f R x y
LayerR (g-⊕ f g) R (inj₂ x) (inj₂ y) = LayerR g R x y
LayerR (g-⊕ f g) R (inj₁ _) (inj₂ _) = ⊥
LayerR (g-⊕ f g) R (inj₂ _) (inj₁ _) = ⊥
LayerR (g-⊗ f g) R (x , x′) (y , y′) = LayerR f R x y × LayerR g R x′ y′

data μR {F F′} (f : GF F F′) : SPoly.μS (SD.code F) → SPoly.μS (SD.code F′) → Set where
  inR : ∀ {x y} → LayerR f (μR f) x y → μR f (SPoly.inS x) (SPoly.inS y)

------------------------------------------------------------------------
-- Blocks
------------------------------------------------------------------------

-- The same calls, related where they end.
data TR {X Y : Set} (R : X → Y → Set) : SE.T X → SE.T Y → Set where
  ret  : ∀ {x y} → R x y → TR R (SE.roll (SE.done x)) (SE.roll (SE.done y))
  call : ∀ {o a k k′} → (∀ b → TR R (k b) (k′ b))
       → TR R (SE.roll (SE.node (SSig.call o a k))) (SE.roll (SE.node (SSig.call o a k′)))

data SumR {X X′ Y Y′ : Set} (R : X → Y → Set) (S : X′ → Y′ → Set) : X ⊎ X′ → Y ⊎ Y′ → Set where
  left  : ∀ {x y} → R x y → SumR R S (inj₁ x) (inj₁ y)
  right : ∀ {x y} → S x y → SumR R S (inj₂ x) (inj₂ y)

record T∞R {X Y : Set} (R : X → Y → Set) (m : SE.T∞ X) (m′ : SE.T∞ Y) : Set where
  coinductive
  field force∞ : TR (SumR R (T∞R R)) (SE.force m) (SE.force m′)

-- A computation at a grade.
MR : ∀ {π π′} → PR π π′ → ∀ {X Y : Set} → (X → Y → Set) → SE.M π X → SE.M π′ Y → Set
MR pr-pure R = R
MR pr-act  R = TR R
MR pr-eff  R = T∞R R

------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------

record νpR {F F′} (f : GF F F′) (v : SE.νM SG.pureᶠ (SD.code F)) (w : SE.νM SG.pureᶠ (SD.code F′)) : Set where
  coinductive
  field forceᵖR : LayerR f (νpR f) (SE.νM.outν v) (SE.νM.outν w)

record νdR {F F′} (f : GF F F′) (v : SE.νM SG.actᶠ (SD.code F)) (w : SE.νM SG.actᶠ (SD.code F′)) : Set where
  coinductive
  field forceᵈR : TR (LayerR f (νdR f)) (SE.νM.outν v) (SE.νM.outν w)

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

ValR : ∀ {A A′} → GR A A′ → SD.⟦ A ⟧ᵛ → SD.⟦ A′ ⟧ᵛ → Set
ValR g-unit  _ _ = ⊤
ValR g-void  _ _ = ⊤
ValR g-int   x y = x ≡ y
ValR g-float x y = x ≡ y
ValR (g-* a b) (x , x′) (y , y′) = ValR a x y × ValR b x′ y′
ValR (g-+ a b) (inj₁ x) (inj₁ y) = ValR a x y
ValR (g-+ a b) (inj₂ x) (inj₂ y) = ValR b x y
ValR (g-+ a b) (inj₁ _) (inj₂ _) = ⊥
ValR (g-+ a b) (inj₂ _) (inj₁ _) = ⊥
ValR (g-⇒ {q = LG.Zero} {π} a b) f g = MR (pr π) (ValR b) (f _) (g _)
ValR (g-⇒ {q = LG.One}  {π} a b) f g = ∀ {x y} → ValR a x y → MR (pr π) (ValR b) (f x) (g y)
ValR (g-⇒ {q = LG.Many} {π} a b) f g = ∀ {x y} → ValR a x y → MR (pr π) (ValR b) (f x) (g y)
ValR (g-μ f) x y = μR f x y
ValR (g-ν {φ = LG.pureᶠ} f) v w = νpR f v w
ValR (g-ν {φ = LG.actᶠ}  f) v w = νdR f v w
