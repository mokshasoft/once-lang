{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Value — the compiler's values and computations as
-- the Spec's (plan 0.121 §3.5, the meaning relation).
--
-- At ground types, `GR A A′`: the compiler's type `A` is the Spec's `A′` (the
-- graph of the translation; a `rigid` constant, which has no values, goes to
-- `Unit`). Over it, a logical relation:
--   * values: the same word at `Int`/`Float`; pairwise at `*`, the same side
--     at `+`; at an arrow, related arguments go to related computations; `μ`
--     layer by layer (`μR`); a stream coinductively, layer by layer (`νpR`,
--     and `νdR`, whose layers are blocks);
--   * computations at a grade (`MR`): a value at `pure`, a block at `act`
--     (`TR`: a compiler call is the Spec's call of the same declaration, its
--     argument and answers related; a halt is a call whose answer is `void`),
--     and at `eff` the closure of blocks under going on (`T∞R`).
-- The calls are against the Spec's signature Σ, a declaration being the
-- compiler's operation of the same name at the translated types (`CallR`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecCore.Value (Σ : Signature) where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Spec.Word using (Carrier)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Grade as SG
open import Once.Spec.Signature using (BTy; ⟦_⟧ᵇ; Op; op; _∶_; operation)
import Once.Spec.Signature as SSig
import Once.Internal.Value Carrier Carrier as V
import Once.Internal.Graded as LGr
import Once.Internal.Polynomial as LPoly
import Once.Spec.Polynomial as SPoly
open import Once.Internal.FunctorMeaning using (translateF; ⟦_,_⟧-base)
import Once.Internal.Trace as LTr
import Once.Internal.Iterative as LI
import Once.Internal.Stream as LSt
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Index
import Once.Adequacy.SpecInterp as SI

------------------------------------------------------------------------
-- Base values
------------------------------------------------------------------------

-- A functor's constant, as each side stores it (only base types occur).
BR : ∀ {A A′} → GR A A′ → ⟦ Carrier , Carrier ⟧-base A → SD.⟦ A′ ⟧ᵛ → Set
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
BR g-rigid   _ _ = ⊤

------------------------------------------------------------------------
-- Layers and data
------------------------------------------------------------------------

LayerR : ∀ {F F′} → GF F F′ → ∀ {X Y : Set} → (X → Y → Set)
       → LPoly.⟦ translateF Carrier Carrier F ⟧SF X → SPoly.⟦ SD.code F′ ⟧SF Y → Set
LayerR (g-K a)   R x y = BR a x y
LayerR g-Id      R x y = R x y
LayerR (g-⊕ f g) R (inj₁ x) (inj₁ y) = LayerR f R x y
LayerR (g-⊕ f g) R (inj₂ x) (inj₂ y) = LayerR g R x y
LayerR (g-⊕ f g) R (inj₁ _) (inj₂ _) = ⊥
LayerR (g-⊕ f g) R (inj₂ _) (inj₁ _) = ⊥
LayerR (g-⊗ f g) R (x , x′) (y , y′) = LayerR f R x y × LayerR g R x′ y′

data μR {F F′} (f : GF F F′) : LPoly.μS (translateF Carrier Carrier F) → SPoly.μS (SD.code F′) → Set where
  inR : ∀ {x y} → LayerR f (μR f) x y → μR f LPoly.⟨ x ⟩ (SPoly.inS y)

------------------------------------------------------------------------
-- Calls and blocks
------------------------------------------------------------------------

-- A compiler call is the Spec call of the declaration of its name, at the
-- declaration's types read as the compiler's (`⌞_⌟`); its argument and its
-- answer cross by the base conversions.
data CallR : LTr.CallOp → Op Σ → Set where
  cr : ∀ {cn a b bA} (m : (cn ∶ operation a SG.Many b) ∈ Σ) → SSig.NotEmpty b → CallR (LTr.callOp cn SI.⌞ a ⌟ bA SI.⌞ b ⌟) (op m)

argR : ∀ {o o′} → CallR o o′ → V.⟦ LTr.CallOp.cdom o ⟧ → ⟦ SSig.arg o′ ⟧ᵇ → Set
argR (cr {a = a} m _) x y = SI.toB a x ≡ y

ansR : ∀ {o o′} → CallR o o′ → V.⟦ LTr.CallOp.ccod o ⟧ → ⟦ Op.ans o′ ⟧ᵇ → Set
ansR (cr {b = b} m _) x y = x ≡ SI.fromB b y

-- A halt is the Spec call of a declaration answering `void`.
data HaltR : LTr.HaltOp → Op Σ → Set where
  hr : ∀ {cn a bA} (m : (cn ∶ operation a SG.Many SSig.void) ∈ Σ) → HaltR (LTr.haltOp cn SI.⌞ a ⌟ bA) (op m)

hargR : ∀ {o o′} → HaltR o o′ → V.⟦ LTr.HaltOp.hdom o ⟧ → ⟦ SSig.arg o′ ⟧ᵇ → Set
hargR (hr {a = a} m) x y = SI.toB a x ≡ y

data TR {X Y : Set} (R : X → Y → Set) : LTr.T X → SE.T Y → Set where
  ret  : ∀ {x y} → R x y → TR R (LTr.ret x) (SE.roll (SE.done y))
  call : ∀ {o o′ a a′ k k′} (c : CallR o o′) → argR c a a′
       → (∀ {b b′} → ansR c b b′ → TR R (k b) (k′ b′))
       → TR R (LTr.call o a k) (SE.roll (SE.node (SSig.call o′ a′ k′)))
  halt : ∀ {o o′ a a′ k′} (h : HaltR o o′) → hargR h a a′
       → TR R (LTr.halt o a) (SE.roll (SE.node (SSig.call o′ a′ k′)))

data SumR {X X′ Y Y′ : Set} (R : X → Y → Set) (S : X′ → Y′ → Set) : X ⊎ X′ → Y ⊎ Y′ → Set where
  left  : ∀ {x y} → R x y → SumR R S (inj₁ x) (inj₁ y)
  right : ∀ {x y} → S x y → SumR R S (inj₂ x) (inj₂ y)

record T∞R {X Y : Set} (R : X → Y → Set) (m : LI.T∞ X) (m′ : SE.T∞ Y) : Set where
  coinductive
  field force∞ : TR (SumR R (T∞R R)) (LI.T∞.force m) (SE.force m′)

-- A computation at a grade.
MR : ∀ {π π′} → PR π π′ → ∀ {X Y : Set} → (X → Y → Set) → LGr.M π X → SE.M π′ Y → Set
MR pr-pure R = R
MR pr-act  R = TR R
MR pr-eff  R = T∞R R

------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------

record νpR {F F′} (f : GF F F′) (v : LGr.νᵖ (translateF Carrier Carrier F)) (w : SE.νM SG.pureᶠ (SD.code F′)) : Set where
  coinductive
  field forceᵖR : LayerR f (νpR f) (LGr.νᵖ.forceᵖ v) (SE.νM.outν w)

record νdR {F F′} (f : GF F F′) (v : LSt.νᵈ (translateF Carrier Carrier F)) (w : SE.νM SG.actᶠ (SD.code F′)) : Set where
  coinductive
  field forceᵈR : TR (LayerR f (νdR f)) (LSt.νᵈ.forceᵈ v) (SE.νM.outν w)

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

ValR : ∀ {A A′} → GR A A′ → LGr.⟦ A ⟧ᵛ → SD.⟦ A′ ⟧ᵛ → Set
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
ValR g-rigid _ _ = ⊤
