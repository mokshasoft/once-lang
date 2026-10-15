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
--     their monads (a value is a computation with no events; a computation
--     that returns is one that need not).
-- Closed under the type formers: arrows are contravariant in the domain;
-- products, sums and requests are covariant; `μ` is invariant. The usage is
-- not varied (that is sub-usage, in the typing rules).
--
-- One rule per head of the left type and no transitivity rule, so each
-- `A <: B` has at most one derivation: every derivation denotes the same
-- conversion.
------------------------------------------------------------------------

module Once.Spec.Sub where

open import Once.Spec.Grade using (mk-kind; _⊑π_)
open import Once.Spec.Type using (Ty; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; Req)

infix 4 _<:_

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
  sub-ν     : ∀ {F π π′} → π ⊑π π′ → ν F π <: ν F π′
  sub-req   : ∀ {A A′} → A <: A′ → Req A <: Req A′
