{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Type.Sub — subtyping `A <: B`.
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
--
-- `A <:ᶜ B`: `A <: B` with every domain kept (`Spec.Sub._<:ᶜ_`, D321).
-- `A ⊔ B ≔ C`: `C` is the join of `A` and `B` in `<:ᶜ` (D322): two branches
-- of one `case` meet there. `Once.Lang.Type.Join` decides it.
------------------------------------------------------------------------

module Once.Lang.Type.Sub where

open import Once.Lang.Type.Grade using (Purity; pure; act; eff; mk-kind; _·p_; fin)
open import Once.Lang.Type
  using (Type; rigid; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)

infix 4 _⊑π_ _<:_ _<:ᶜ_ _⊔_≔_

-- The effect order: the chain `pure ⊑ act ⊑ eff` (D314), one derivation per
-- pair.
data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-eff  : eff  ⊑π eff
  ⊑-pe   : pure ⊑π eff
  ⊑-act  : act  ⊑π act
  ⊑-pa   : pure ⊑π act
  ⊑-ae   : act  ⊑π eff

-- Running a grade twice stays within it (the product is idempotent). What a rule with one grade for two sequenced parts
-- reads its product as.
·p-diag : ∀ π → (π ·p π) ⊑π π
·p-diag pure = ⊑-pure
·p-diag act  = ⊑-act
·p-diag eff  = ⊑-eff

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
  sub-ν      : ∀ {F φ φ′} → fin φ ⊑π fin φ′ → ν-type F φ <: ν-type F φ′
  sub-rigid  : ∀ {k i} → rigid k i <: rigid k i

-- The identities of the order and of the thin category of types.
⊑π-refl : ∀ π → π ⊑π π
⊑π-refl pure = ⊑-pure
⊑π-refl act = ⊑-act
⊑π-refl eff = ⊑-eff

<:-refl : ∀ A → A <: A
<:-refl Unit   = sub-unit
<:-refl Void   = sub-void
<:-refl Int    = sub-int
<:-refl Float  = sub-float
<:-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:-refl A) (<:-refl B) (⊑π-refl π)
<:-refl (A * B) = sub-prod (<:-refl A) (<:-refl B)
<:-refl (A + B) = sub-sum (<:-refl A) (<:-refl B)
<:-refl (μ-type F) = sub-μ
<:-refl (ν-type F φ) = sub-ν (⊑π-refl (fin φ))
<:-refl (rigid _ _) = sub-rigid

data _<:ᶜ_ : Type → Type → Set where
  subᶜ-void   : ∀ {B} → Void <:ᶜ B
  subᶜ-unit   : Unit <:ᶜ Unit
  subᶜ-int    : Int <:ᶜ Int
  subᶜ-float  : Float <:ᶜ Float
  subᶜ-arr    : ∀ {A B B′ q π π′}
              → B <:ᶜ B′ → π ⊑π π′
              → (A ⇒[ mk-kind q π ] B) <:ᶜ (A ⇒[ mk-kind q π′ ] B′)
  subᶜ-prod   : ∀ {A A′ B B′} → A <:ᶜ A′ → B <:ᶜ B′ → (A * B) <:ᶜ (A′ * B′)
  subᶜ-sum    : ∀ {A A′ B B′} → A <:ᶜ A′ → B <:ᶜ B′ → (A + B) <:ᶜ (A′ + B′)
  subᶜ-μ      : ∀ {F} → μ-type F <:ᶜ μ-type F
  subᶜ-ν      : ∀ {F φ φ′} → fin φ ⊑π fin φ′ → ν-type F φ <:ᶜ ν-type F φ′
  subᶜ-rigid  : ∀ {k i} → rigid k i <:ᶜ rigid k i

-- Keeping the domains is a special case of converting.
<:ᶜ⇒<: : ∀ {A B} → A <:ᶜ B → A <: B
<:ᶜ⇒<: subᶜ-void        = sub-void
<:ᶜ⇒<: subᶜ-unit        = sub-unit
<:ᶜ⇒<: subᶜ-int         = sub-int
<:ᶜ⇒<: subᶜ-float       = sub-float
<:ᶜ⇒<: (subᶜ-arr {A = A} b g) = sub-arr (<:-refl A) (<:ᶜ⇒<: b) g
<:ᶜ⇒<: (subᶜ-prod a b)  = sub-prod (<:ᶜ⇒<: a) (<:ᶜ⇒<: b)
<:ᶜ⇒<: (subᶜ-sum a b)   = sub-sum (<:ᶜ⇒<: a) (<:ᶜ⇒<: b)
<:ᶜ⇒<: subᶜ-μ           = sub-μ
<:ᶜ⇒<: (subᶜ-ν g)       = sub-ν g
<:ᶜ⇒<: subᶜ-rigid       = sub-rigid

<:ᶜ-refl : ∀ A → A <:ᶜ A
<:ᶜ-refl Unit   = subᶜ-unit
<:ᶜ-refl Void   = subᶜ-void
<:ᶜ-refl Int    = subᶜ-int
<:ᶜ-refl Float  = subᶜ-float
<:ᶜ-refl (A ⇒[ mk-kind q π ] B) = subᶜ-arr (<:ᶜ-refl B) (⊑π-refl π)
<:ᶜ-refl (A * B) = subᶜ-prod (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (A + B) = subᶜ-sum (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (μ-type F) = subᶜ-μ
<:ᶜ-refl (ν-type F φ) = subᶜ-ν (⊑π-refl (fin φ))
<:ᶜ-refl (rigid _ _) = subᶜ-rigid

record _⊔_≔_ (A B C : Type) : Set where
  field
    left  : A <:ᶜ C
    right : B <:ᶜ C
    least : ∀ {D} → A <:ᶜ D → B <:ᶜ D → C <:ᶜ D
