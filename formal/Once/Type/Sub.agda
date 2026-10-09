-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Sub — the subtyping judgment `A <: B` (plan 0.99, D226).
--
-- ONE judgment on types. A generator is admitted iff its conversion is
-- CANONICAL (forced, not chosen) and OBSERVATION-FREE (it can never lose
-- anything the program observes):
--
--   * `Void <: B` — `¡`, the unique map out of the initial object, which never
--     runs because there is no value to run it on;
--   * `pure ⊑ eff` on an arrow's grade — the Freyd embedding (D068), which `⟦_⟧`
--     erases.
--
-- NOT admitted: `A <: Unit` (`!` is unique too, but it ERASES a value and breaks
-- linearity) and `Int <: Float` (a chosen map, not injective at fixed width; D125).
--
-- Closed under the type formers: arrows contravariant in the domain, covariant in
-- the codomain and grade; products and sums covariant; `μ`/`ν` reflexive only (no
-- functor variance yet); the quantity is not varied (sub-usage is QTT's axis).
--
-- COHERENCE BY CONSTRUCTION. The rules are syntax-directed on the LEFT type and
-- there is no transitivity rule, so each `A <: B` has at most one derivation
-- (`<:-unique`): every derivation denotes the same conversion. Reflexivity and
-- transitivity are admissible (`<:-refl`, `<:-trans`). Every premise is a
-- judgment on types, never a computation on syntax (plan 0.94 §2).
------------------------------------------------------------------------

module Once.Type.Sub where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Type using (Type; rigid; Purity; pure; eff; mk-kind; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; _≟q_)
open import Once.Type.DecEq using (_≟F_; _≟T_)

------------------------------------------------------------------------
-- The grade order: pure ⊑ eff.
------------------------------------------------------------------------

infix 4 _⊑π_ _<:_

data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-eff  : eff  ⊑π eff
  ⊑-pe   : pure ⊑π eff

-- Every grade is above `pure` (D068; D250: the unit of every grade's monad is
-- this subeffecting applied to a pure value).
pure⊑ : ∀ π → pure ⊑π π
pure⊑ pure = ⊑-pure
pure⊑ eff  = ⊑-pe

_⊑π?_ : (π π′ : Purity) → Dec (π ⊑π π′)
pure ⊑π? pure = yes ⊑-pure
pure ⊑π? eff  = yes ⊑-pe
eff  ⊑π? pure = no λ ()
eff  ⊑π? eff  = yes ⊑-eff




------------------------------------------------------------------------
-- The judgment. One rule per head of the LEFT type — that disjointness is
-- what makes derivations unique.
------------------------------------------------------------------------

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
  -- D233: a pure stream is an effectful one with no effects — covariant in the grade.
  sub-ν      : ∀ {F π π′} → π ⊑π π′ → ν-type F π <: ν-type F π′
  -- D243: a rigid parameter is related only to itself (and, as every type, above Void).
  sub-rigid  : ∀ {k i} → rigid k i <: rigid k i

------------------------------------------------------------------------
-- Coherence: at most one derivation.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Admissible reflexivity and transitivity.
------------------------------------------------------------------------



------------------------------------------------------------------------
-- Decidability. Mismatched heads are refuted clause by clause (no catch-all:
-- a catch-all carries no negative information, so `λ ()` could not fire).
------------------------------------------------------------------------

private
  arr-aux : ∀ {A A′ B B′ q q′ π π′}
          → Dec (q ≡ q′) → Dec (A′ <: A) → Dec (B <: B′) → Dec (π ⊑π π′)
          → Dec ((A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q′ π′ ] B′))
  arr-aux (yes refl) (yes a) (yes b) (yes g) = yes (sub-arr a b g)
  arr-aux (no ¬q)    _       _       _       = no λ { (sub-arr _ _ _) → ¬q refl }
  arr-aux (yes refl) (no ¬a) _       _       = no λ { (sub-arr a _ _) → ¬a a }
  arr-aux (yes refl) (yes _) (no ¬b) _       = no λ { (sub-arr _ b _) → ¬b b }
  arr-aux (yes refl) (yes _) (yes _) (no ¬g) = no λ { (sub-arr _ _ g) → ¬g g }

  prod-aux : ∀ {A A′ B B′} → Dec (A <: A′) → Dec (B <: B′) → Dec ((A * B) <: (A′ * B′))
  prod-aux (yes a) (yes b) = yes (sub-prod a b)
  prod-aux (no ¬a) _       = no λ { (sub-prod a _) → ¬a a }
  prod-aux (yes _) (no ¬b) = no λ { (sub-prod _ b) → ¬b b }

  sum-aux : ∀ {A A′ B B′} → Dec (A <: A′) → Dec (B <: B′) → Dec ((A + B) <: (A′ + B′))
  sum-aux (yes a) (yes b) = yes (sub-sum a b)
  sum-aux (no ¬a) _       = no λ { (sub-sum a _) → ¬a a }
  sum-aux (yes _) (no ¬b) = no λ { (sub-sum _ b) → ¬b b }

  μ-aux : ∀ {F G} → Dec (F ≡ G) → Dec (μ-type F <: μ-type G)
  μ-aux (yes refl) = yes sub-μ
  μ-aux (no ¬e)    = no λ { sub-μ → ¬e refl }

  ν-aux : ∀ {F G π π′} → Dec (F ≡ G) → Dec (π ⊑π π′) → Dec (ν-type F π <: ν-type G π′)
  ν-aux (yes refl) (yes g) = yes (sub-ν g)
  ν-aux (no ¬e)    _       = no λ { (sub-ν _) → ¬e refl }
  ν-aux (yes refl) (no ¬g) = no λ { (sub-ν g) → ¬g g }
  rigid-aux : ∀ {k k′ i i′} → Dec (rigid k i ≡ rigid k′ i′) → Dec (rigid k i <: rigid k′ i′)
  rigid-aux (yes refl) = yes sub-rigid
  rigid-aux (no ¬e)    = no λ { sub-rigid → ¬e refl }

_<:?_ : (A B : Type) → Dec (A <: B)
Void <:? _ = yes sub-void
Unit <:? Unit = yes sub-unit
Unit <:? Void = no λ ()
Unit <:? Int = no λ ()
Unit <:? Float = no λ ()
Unit <:? (_ * _) = no λ ()
Unit <:? (_ + _) = no λ ()
Unit <:? (_ ⇒[ _ ] _) = no λ ()
Unit <:? (μ-type _) = no λ ()
Unit <:? (ν-type _ _) = no λ ()
Int <:? Int = yes sub-int
Int <:? Unit = no λ ()
Int <:? Void = no λ ()
Int <:? Float = no λ ()
Int <:? (_ * _) = no λ ()
Int <:? (_ + _) = no λ ()
Int <:? (_ ⇒[ _ ] _) = no λ ()
Int <:? (μ-type _) = no λ ()
Int <:? (ν-type _ _) = no λ ()
Float <:? Float = yes sub-float
Float <:? Unit = no λ ()
Float <:? Void = no λ ()
Float <:? Int = no λ ()
Float <:? (_ * _) = no λ ()
Float <:? (_ + _) = no λ ()
Float <:? (_ ⇒[ _ ] _) = no λ ()
Float <:? (μ-type _) = no λ ()
Float <:? (ν-type _ _) = no λ ()
(A ⇒[ mk-kind q π ] B) <:? (A′ ⇒[ mk-kind q′ π′ ] B′) = arr-aux (q ≟q q′) (A′ <:? A) (B <:? B′) (π ⊑π? π′)
(_ ⇒[ _ ] _) <:? Unit = no λ ()
(_ ⇒[ _ ] _) <:? Void = no λ ()
(_ ⇒[ _ ] _) <:? Int = no λ ()
(_ ⇒[ _ ] _) <:? Float = no λ ()
(_ ⇒[ _ ] _) <:? (_ * _) = no λ ()
(_ ⇒[ _ ] _) <:? (_ + _) = no λ ()
(_ ⇒[ _ ] _) <:? (μ-type _) = no λ ()
(_ ⇒[ _ ] _) <:? (ν-type _ _) = no λ ()
(A * B) <:? (A′ * B′) = prod-aux (A <:? A′) (B <:? B′)
(_ * _) <:? Unit = no λ ()
(_ * _) <:? Void = no λ ()
(_ * _) <:? Int = no λ ()
(_ * _) <:? Float = no λ ()
(_ * _) <:? (_ + _) = no λ ()
(_ * _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ * _) <:? (μ-type _) = no λ ()
(_ * _) <:? (ν-type _ _) = no λ ()
(A + B) <:? (A′ + B′) = sum-aux (A <:? A′) (B <:? B′)
(_ + _) <:? Unit = no λ ()
(_ + _) <:? Void = no λ ()
(_ + _) <:? Int = no λ ()
(_ + _) <:? Float = no λ ()
(_ + _) <:? (_ * _) = no λ ()
(_ + _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ + _) <:? (μ-type _) = no λ ()
(_ + _) <:? (ν-type _ _) = no λ ()
μ-type F <:? μ-type G = μ-aux (F ≟F G)
μ-type _ <:? Unit = no λ ()
μ-type _ <:? Void = no λ ()
μ-type _ <:? Int = no λ ()
μ-type _ <:? Float = no λ ()
μ-type _ <:? (_ * _) = no λ ()
μ-type _ <:? (_ + _) = no λ ()
μ-type _ <:? (_ ⇒[ _ ] _) = no λ ()
μ-type _ <:? (ν-type _ _) = no λ ()
ν-type F π <:? ν-type G π′ = ν-aux (F ≟F G) (π ⊑π? π′)
ν-type _ _ <:? Unit = no λ ()
ν-type _ _ <:? Void = no λ ()
ν-type _ _ <:? Int = no λ ()
ν-type _ _ <:? Float = no λ ()
ν-type _ _ <:? (_ * _) = no λ ()
ν-type _ _ <:? (_ + _) = no λ ()
ν-type _ _ <:? (_ ⇒[ _ ] _) = no λ ()
ν-type _ _ <:? (μ-type _) = no λ ()
-- D243
rigid k i <:? rigid k′ i′ = rigid-aux (rigid k i ≟T rigid k′ i′)
rigid _ _ <:? Void = no λ ()
rigid _ _ <:? Unit = no λ ()
Unit <:? rigid _ _ = no λ ()
rigid _ _ <:? (_ * _) = no λ ()
(_ * _) <:? rigid _ _ = no λ ()
rigid _ _ <:? (_ + _) = no λ ()
(_ + _) <:? rigid _ _ = no λ ()
rigid _ _ <:? (_ ⇒[ _ ] _) = no λ ()
(_ ⇒[ _ ] _) <:? rigid _ _ = no λ ()
rigid _ _ <:? μ-type _ = no λ ()
μ-type _ <:? rigid _ _ = no λ ()
rigid _ _ <:? ν-type _ _ = no λ ()
ν-type _ _ <:? rigid _ _ = no λ ()
rigid _ _ <:? Int = no λ ()
Int <:? rigid _ _ = no λ ()
rigid _ _ <:? Float = no λ ()
Float <:? rigid _ _ = no λ ()
