{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type.Sub — subtyping `A <: B`.
--
-- A conversion is admitted only if it is canonical (forced, not chosen) and
-- loses nothing a program can observe:
--   * `Void <: B`: the unique map out of the initial object, which never runs;
--   * `pure ⊑ eff` on an arrow's grade: a pure arrow is an effectful one with
--     no effects.
-- Not admitted: `A <: Unit` (the map is unique, but it discards a value and
-- breaks linearity) and `Int <: Float` (a chosen map, not injective at fixed
-- width).
--
-- The rules are closed under the type formers: arrows are contravariant in
-- the domain and covariant in the codomain and the grade; products and sums
-- are covariant; `μ` is invariant and `ν` covariant in its grade only; the
-- usage is not varied (that is sub-usage, in the typing rules).
--
-- There is one rule per head of the left type and no transitivity rule, so
-- each `A <: B` has at most one derivation: subtyping is a thin category, and
-- every derivation denotes the same conversion. Reflexivity and transitivity
-- are admissible (`Spec.Metatheory`).
------------------------------------------------------------------------

module Once.Spec.Type.Sub where

open import Once.Spec.Type.Grade using (Purity; pure; eff; mk-kind)
open import Once.Spec.Type
  using (Type; rigid; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)

infix 4 _⊑π_ _<:_

-- The effect order.
data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-eff  : eff  ⊑π eff
  ⊑-pe   : pure ⊑π eff

-- `pure` is below every grade.
pure⊑ : ∀ π → pure ⊑π π
pure⊑ pure = ⊑-pure
pure⊑ eff  = ⊑-pe

data _<:_ : Type → Type → Set where
  sub-void   : ∀ {B} → Void <: B
  sub-unit   : Unit <: Unit
  sub-int    : Int <: Int
  sub-float  : Float <: Float
  sub-arr    : ∀ {A A′ B B′ q π π′}
             → A′ <: A → B <: B′ → π ⊑π π′
             → (A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q π′ ] B′)
  sub-prod   : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A * B) <: (A′ * B′)
  sub-sum    : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A + B) <: (A′ + B′)
  sub-μ      : ∀ {F} → μ-type F <: μ-type F
  sub-ν      : ∀ {F π π′} → π ⊑π π′ → ν-type F π <: ν-type F π′
  sub-rigid  : ∀ {k i} → rigid k i <: rigid k i
