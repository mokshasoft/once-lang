-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Sub — deciding subtyping.
--
-- The judgment `A <: B` and the effect order `_⊑π_` are the Spec's
-- (`Once.Spec.Type.Sub`). This module decides them.
------------------------------------------------------------------------

module Once.Type.Sub where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff; prod; mk-kind)
open import Once.Spec.Type using (Type; rigid; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Spec.Type.Sub
  using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-prod; ⊑-pp; ⊑-ep; ⊑-g; ⊑-ge; ⊑-gp; _<:_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-prod; sub-sum; sub-μ; sub-ν; sub-rigid)
open import Once.Spec.Type.DecEq using (_≟q_)
open import Once.Spec.Type.DecEq using (_≟F_; _≟T_)

------------------------------------------------------------------------
-- The effect order.
------------------------------------------------------------------------

_⊑π?_ : (π π′ : Purity) → Dec (π ⊑π π′)
pure ⊑π? pure = yes ⊑-pure
pure ⊑π? eff⁺ = no λ ()
pure ⊑π? eff = yes ⊑-pe
pure ⊑π? prod = yes ⊑-pp
eff⁺ ⊑π? pure = no λ ()
eff⁺ ⊑π? eff⁺ = yes ⊑-g
eff⁺ ⊑π? eff = yes ⊑-ge
eff⁺ ⊑π? prod = yes ⊑-gp
eff ⊑π? pure = no λ ()
eff ⊑π? eff⁺ = no λ ()
eff ⊑π? eff = yes ⊑-eff
eff ⊑π? prod = yes ⊑-ep
prod ⊑π? pure = no λ ()
prod ⊑π? eff⁺ = no λ ()
prod ⊑π? eff = no λ ()
prod ⊑π? prod = yes ⊑-prod

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
