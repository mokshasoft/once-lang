{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Sub — subtyping `A <: B`.
--
-- A conversion is admitted only if it is canonical (forced, not chosen) and
-- loses nothing a program can observe:
--   * `Void <: B`: the unique map out of the initial object;
--   * `π ⊑ π′` on an arrow's or a stream's effect: the monad morphism between
--     their monads (a value is a computation with no events; a block of
--     events is one round of a computation that need not stop); a stream's
--     layers are at a finite grade, so it varies only from `pure` to `act`.
-- Closed under the type formers: arrows are contravariant in the domain;
-- products and sums are covariant; `μ` is invariant. The usage is
-- not varied (that is sub-usage, in the typing rules).
--
-- One rule per head of the left type and no transitivity rule, so each
-- `A <: B` has at most one derivation: every derivation denotes the same
-- conversion.
--
-- `A <:ᶜ B`: `A <: B` with every domain kept — smaller only in what a term
-- produces (codomains, grades, `Void` for a whole type). A term is a morphism
-- out of a given object: its domains are annotations, and its principal type
-- is the least codomain over them (`Spec.Surface.Program.Principal`).
------------------------------------------------------------------------

module Once.Spec.Sub where

open import Once.Spec.Grade using (mk-kind; fin; _⊑π_)
open import Once.Spec.Type using (Ty; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)

infix 4 _<:_ _<:ᶜ_

data _<:_ {m} : Ty m → Ty m → Set where
  sub-void  : ∀ {B} → Void <: B
  sub-var   : ∀ {i} → var i <: var i
  sub-unit  : Unit <: Unit
  sub-int   : Int <: Int
  sub-float : Float <: Float
  sub-arr   : ∀ {A A′ B B′ q π π′}
            → A′ <: A → B <: B′ → π ⊑π π′
            → (A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q π′ ] B′)
  sub-*     : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A * B) <: (A′ * B′)
  sub-+     : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A + B) <: (A′ + B′)
  sub-μ     : ∀ {F} → μ F <: μ F
  sub-ν     : ∀ {F f f′} → fin f ⊑π fin f′ → ν F f <: ν F f′

data _<:ᶜ_ {m} : Ty m → Ty m → Set where
  subᶜ-void  : ∀ {B} → Void <:ᶜ B
  subᶜ-var   : ∀ {i} → var i <:ᶜ var i
  subᶜ-unit  : Unit <:ᶜ Unit
  subᶜ-int   : Int <:ᶜ Int
  subᶜ-float : Float <:ᶜ Float
  subᶜ-arr   : ∀ {A B B′ q π π′}
             → B <:ᶜ B′ → π ⊑π π′
             → (A ⇒[ mk-kind q π ] B) <:ᶜ (A ⇒[ mk-kind q π′ ] B′)
  subᶜ-*     : ∀ {A A′ B B′} → A <:ᶜ A′ → B <:ᶜ B′ → (A * B) <:ᶜ (A′ * B′)
  subᶜ-+     : ∀ {A A′ B B′} → A <:ᶜ A′ → B <:ᶜ B′ → (A + B) <:ᶜ (A′ + B′)
  subᶜ-μ     : ∀ {F} → μ F <:ᶜ μ F
  subᶜ-ν     : ∀ {F f f′} → fin f ⊑π fin f′ → ν F f <:ᶜ ν F f′
