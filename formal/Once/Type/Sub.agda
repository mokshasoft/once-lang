-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Sub — deciding subtyping.
--
-- The judgment `A <: B` and the effect order `_⊑π_` are the Spec's
-- (`Once.Internal.Type.Sub`). This module decides them.
------------------------------------------------------------------------

module Once.Type.Sub where

open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Sub using (sub-*; sub-+)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind; fin)
open import Once.Spec.Type using (Ty; Fun; var; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Sub using (_<:_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν)
open import Once.Spec.Sub using (sub-var)
open import Data.Fin using (Fin)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Internal.Type.DecEq using (_≟q_)
open import Once.Internal.Type.DecEq using (_≟F_; _≟T_)

------------------------------------------------------------------------
-- The effect order.
------------------------------------------------------------------------

_⊑π?_ : (π π′ : Purity) → Dec (π ⊑π π′)
pure ⊑π? pure = yes ⊑-pure
pure ⊑π? act = yes ⊑-pa
pure ⊑π? eff = yes ⊑-pe
act ⊑π? pure = no λ ()
act ⊑π? act = yes ⊑-act
act ⊑π? eff = yes ⊑-ae
eff ⊑π? pure = no λ ()
eff ⊑π? act = no λ ()
eff ⊑π? eff = yes ⊑-eff

------------------------------------------------------------------------
-- Decidability. Mismatched heads are refuted clause by clause (no catch-all:
-- a catch-all carries no negative information, so `λ ()` could not fire).
------------------------------------------------------------------------

private
  arr-aux : ∀ {m} {A A′ B B′ : Ty m} {q q′ π π′}
          → Dec (q ≡ q′) → Dec (A′ <: A) → Dec (B <: B′) → Dec (π ⊑π π′)
          → Dec ((A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q′ π′ ] B′))
  arr-aux (yes refl) (yes a) (yes b) (yes g) = yes (sub-arr a b g)
  arr-aux (no ¬q)    _       _       _       = no λ { (sub-arr _ _ _) → ¬q refl }
  arr-aux (yes refl) (no ¬a) _       _       = no λ { (sub-arr a _ _) → ¬a a }
  arr-aux (yes refl) (yes _) (no ¬b) _       = no λ { (sub-arr _ b _) → ¬b b }
  arr-aux (yes refl) (yes _) (yes _) (no ¬g) = no λ { (sub-arr _ _ g) → ¬g g }

  prod-aux : ∀ {m} {A A′ B B′ : Ty m} → Dec (A <: A′) → Dec (B <: B′) → Dec ((A * B) <: (A′ * B′))
  prod-aux (yes a) (yes b) = yes (sub-* a b)
  prod-aux (no ¬a) _       = no λ { (sub-* a _) → ¬a a }
  prod-aux (yes _) (no ¬b) = no λ { (sub-* _ b) → ¬b b }

  sum-aux : ∀ {m} {A A′ B B′ : Ty m} → Dec (A <: A′) → Dec (B <: B′) → Dec ((A + B) <: (A′ + B′))
  sum-aux (yes a) (yes b) = yes (sub-+ a b)
  sum-aux (no ¬a) _       = no λ { (sub-+ a _) → ¬a a }
  sum-aux (yes _) (no ¬b) = no λ { (sub-+ _ b) → ¬b b }

  μ-aux : ∀ {m} {F G : Fun m} → Dec (F ≡ G) → Dec (μ F <: μ G)
  μ-aux (yes refl) = yes sub-μ
  μ-aux (no ¬e)    = no λ { sub-μ → ¬e refl }

  ν-aux : ∀ {m} {F G : Fun m} {φ φ′} → Dec (F ≡ G) → Dec (fin φ ⊑π fin φ′) → Dec (ν F φ <: ν G φ′)
  ν-aux (yes refl) (yes g) = yes (sub-ν g)
  ν-aux (no ¬e)    _       = no λ { (sub-ν _) → ¬e refl }
  ν-aux (yes refl) (no ¬g) = no λ { (sub-ν g) → ¬g g }
  var-aux : ∀ {m} {i i′ : Fin m} → Dec (var i ≡ var i′) → Dec (var i <: var i′)
  var-aux (yes refl) = yes sub-var
  var-aux (no ¬e)    = no λ { sub-var → ¬e refl }

_<:?_ : ∀ {m} (A B : Ty m) → Dec (A <: B)
Void <:? _ = yes sub-void
Unit <:? Unit = yes sub-unit
Unit <:? Void = no λ ()
Unit <:? Int = no λ ()
Unit <:? Float = no λ ()
Unit <:? (_ * _) = no λ ()
Unit <:? (_ + _) = no λ ()
Unit <:? (_ ⇒[ _ ] _) = no λ ()
Unit <:? (μ _) = no λ ()
Unit <:? (ν _ _) = no λ ()
Int <:? Int = yes sub-int
Int <:? Unit = no λ ()
Int <:? Void = no λ ()
Int <:? Float = no λ ()
Int <:? (_ * _) = no λ ()
Int <:? (_ + _) = no λ ()
Int <:? (_ ⇒[ _ ] _) = no λ ()
Int <:? (μ _) = no λ ()
Int <:? (ν _ _) = no λ ()
Float <:? Float = yes sub-float
Float <:? Unit = no λ ()
Float <:? Void = no λ ()
Float <:? Int = no λ ()
Float <:? (_ * _) = no λ ()
Float <:? (_ + _) = no λ ()
Float <:? (_ ⇒[ _ ] _) = no λ ()
Float <:? (μ _) = no λ ()
Float <:? (ν _ _) = no λ ()
(A ⇒[ mk-kind q π ] B) <:? (A′ ⇒[ mk-kind q′ π′ ] B′) = arr-aux (q ≟q q′) (A′ <:? A) (B <:? B′) (π ⊑π? π′)
(_ ⇒[ _ ] _) <:? Unit = no λ ()
(_ ⇒[ _ ] _) <:? Void = no λ ()
(_ ⇒[ _ ] _) <:? Int = no λ ()
(_ ⇒[ _ ] _) <:? Float = no λ ()
(_ ⇒[ _ ] _) <:? (_ * _) = no λ ()
(_ ⇒[ _ ] _) <:? (_ + _) = no λ ()
(_ ⇒[ _ ] _) <:? (μ _) = no λ ()
(_ ⇒[ _ ] _) <:? (ν _ _) = no λ ()
(A * B) <:? (A′ * B′) = prod-aux (A <:? A′) (B <:? B′)
(_ * _) <:? Unit = no λ ()
(_ * _) <:? Void = no λ ()
(_ * _) <:? Int = no λ ()
(_ * _) <:? Float = no λ ()
(_ * _) <:? (_ + _) = no λ ()
(_ * _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ * _) <:? (μ _) = no λ ()
(_ * _) <:? (ν _ _) = no λ ()
(A + B) <:? (A′ + B′) = sum-aux (A <:? A′) (B <:? B′)
(_ + _) <:? Unit = no λ ()
(_ + _) <:? Void = no λ ()
(_ + _) <:? Int = no λ ()
(_ + _) <:? Float = no λ ()
(_ + _) <:? (_ * _) = no λ ()
(_ + _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ + _) <:? (μ _) = no λ ()
(_ + _) <:? (ν _ _) = no λ ()
μ F <:? μ G = μ-aux (F ≟F G)
μ _ <:? Unit = no λ ()
μ _ <:? Void = no λ ()
μ _ <:? Int = no λ ()
μ _ <:? Float = no λ ()
μ _ <:? (_ * _) = no λ ()
μ _ <:? (_ + _) = no λ ()
μ _ <:? (_ ⇒[ _ ] _) = no λ ()
μ _ <:? (ν _ _) = no λ ()
ν F φ <:? ν G φ′ = ν-aux (F ≟F G) (fin φ ⊑π? fin φ′)
ν _ _ <:? Unit = no λ ()
ν _ _ <:? Void = no λ ()
ν _ _ <:? Int = no λ ()
ν _ _ <:? Float = no λ ()
ν _ _ <:? (_ * _) = no λ ()
ν _ _ <:? (_ + _) = no λ ()
ν _ _ <:? (_ ⇒[ _ ] _) = no λ ()
ν _ _ <:? (μ _) = no λ ()
-- D243
var i <:? var i′ = var-aux (var i ≟T var i′)
var _ <:? Void = no λ ()
var _ <:? Unit = no λ ()
Unit <:? var _ = no λ ()
var _ <:? (_ * _) = no λ ()
(_ * _) <:? var _ = no λ ()
var _ <:? (_ + _) = no λ ()
(_ + _) <:? var _ = no λ ()
var _ <:? (_ ⇒[ _ ] _) = no λ ()
(_ ⇒[ _ ] _) <:? var _ = no λ ()
var _ <:? μ _ = no λ ()
μ _ <:? var _ = no λ ()
var _ <:? ν _ _ = no λ ()
ν _ _ <:? var _ = no λ ()
var _ <:? Int = no λ ()
Int <:? var _ = no λ ()
var _ <:? Float = no λ ()
Float <:? var _ = no λ ()
