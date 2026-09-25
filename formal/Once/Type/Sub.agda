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

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Type using (Type; Functor; Quantity; Purity; pure; eff; mk-kind;
                             Unit; Void; Int; Float; Str; Buffer; _*_; _+_; _⇒[_]_;
                             μ-type; ν-type; _≟q_)
open import Once.Type.DecEq using (_≟F_)

------------------------------------------------------------------------
-- The grade order: pure ⊑ eff.
------------------------------------------------------------------------

infix 4 _⊑π_ _<:_

data _⊑π_ : Purity → Purity → Set where
  ⊑-pure : pure ⊑π pure
  ⊑-eff  : eff  ⊑π eff
  ⊑-pe   : pure ⊑π eff

_⊑π?_ : (π π′ : Purity) → Dec (π ⊑π π′)
pure ⊑π? pure = yes ⊑-pure
pure ⊑π? eff  = yes ⊑-pe
eff  ⊑π? pure = no λ ()
eff  ⊑π? eff  = yes ⊑-eff

⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h
⊑π-unique ⊑-pure ⊑-pure = refl
⊑π-unique ⊑-eff  ⊑-eff  = refl
⊑π-unique ⊑-pe   ⊑-pe   = refl

⊑π-refl : ∀ π → π ⊑π π
⊑π-refl pure = ⊑-pure
⊑π-refl eff  = ⊑-eff

⊑π-trans : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
⊑π-trans ⊑-pure g     = g
⊑π-trans ⊑-eff  ⊑-eff = ⊑-eff
⊑π-trans ⊑-pe   ⊑-eff = ⊑-pe

------------------------------------------------------------------------
-- The judgment. One rule per head of the LEFT type — that disjointness is
-- what makes derivations unique.
------------------------------------------------------------------------

data _<:_ : Type → Type → Set where
  sub-void   : ∀ {B} → Void <: B
  sub-unit   : Unit <: Unit
  sub-int    : Int <: Int
  sub-float  : Float <: Float
  sub-str    : Str <: Str
  sub-buffer : Buffer <: Buffer
  sub-arr    : ∀ {A A′ B B′ q π π′}
             → A′ <: A → B <: B′ → π ⊑π π′
             → (A ⇒[ mk-kind q π ] B) <: (A′ ⇒[ mk-kind q π′ ] B′)
  sub-prod   : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A * B) <: (A′ * B′)
  sub-sum    : ∀ {A A′ B B′} → A <: A′ → B <: B′ → (A + B) <: (A′ + B′)
  sub-μ      : ∀ {F} → μ-type F <: μ-type F
  sub-ν      : ∀ {F} → ν-type F <: ν-type F

------------------------------------------------------------------------
-- Coherence: at most one derivation.
------------------------------------------------------------------------

<:-unique : ∀ {A B} (p q : A <: B) → p ≡ q
<:-unique sub-void   sub-void   = refl
<:-unique sub-unit   sub-unit   = refl
<:-unique sub-int    sub-int    = refl
<:-unique sub-float  sub-float  = refl
<:-unique sub-str    sub-str    = refl
<:-unique sub-buffer sub-buffer = refl
<:-unique (sub-arr a b g) (sub-arr a′ b′ g′)
  rewrite <:-unique a a′ | <:-unique b b′ | ⊑π-unique g g′ = refl
<:-unique (sub-prod a b) (sub-prod a′ b′) = cong₂ sub-prod (<:-unique a a′) (<:-unique b b′)
<:-unique (sub-sum a b)  (sub-sum a′ b′)  = cong₂ sub-sum  (<:-unique a a′) (<:-unique b b′)
<:-unique sub-μ sub-μ = refl
<:-unique sub-ν sub-ν = refl

------------------------------------------------------------------------
-- Admissible reflexivity and transitivity.
------------------------------------------------------------------------

<:-refl : ∀ A → A <: A
<:-refl Unit   = sub-unit
<:-refl Void   = sub-void
<:-refl Int    = sub-int
<:-refl Float  = sub-float
<:-refl Str    = sub-str
<:-refl Buffer = sub-buffer
<:-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:-refl A) (<:-refl B) (⊑π-refl π)
<:-refl (A * B) = sub-prod (<:-refl A) (<:-refl B)
<:-refl (A + B) = sub-sum (<:-refl A) (<:-refl B)
<:-refl (μ-type F) = sub-μ
<:-refl (ν-type F) = sub-ν

<:-trans : ∀ {A B C} → A <: B → B <: C → A <: C
<:-trans sub-void   _          = sub-void
<:-trans sub-unit   q          = q
<:-trans sub-int    q          = q
<:-trans sub-float  q          = q
<:-trans sub-str    q          = q
<:-trans sub-buffer q          = q
<:-trans (sub-arr a b g) (sub-arr a′ b′ g′) = sub-arr (<:-trans a′ a) (<:-trans b b′) (⊑π-trans g g′)
<:-trans (sub-prod a b)  (sub-prod a′ b′)   = sub-prod (<:-trans a a′) (<:-trans b b′)
<:-trans (sub-sum a b)   (sub-sum a′ b′)    = sub-sum  (<:-trans a a′) (<:-trans b b′)
<:-trans sub-μ q = q
<:-trans sub-ν q = q

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

  ν-aux : ∀ {F G} → Dec (F ≡ G) → Dec (ν-type F <: ν-type G)
  ν-aux (yes refl) = yes sub-ν
  ν-aux (no ¬e)    = no λ { sub-ν → ¬e refl }

_<:?_ : (A B : Type) → Dec (A <: B)
Void <:? _ = yes sub-void
Unit <:? Unit = yes sub-unit
Unit <:? Void = no λ ()
Unit <:? Int = no λ ()
Unit <:? Float = no λ ()
Unit <:? Str = no λ ()
Unit <:? Buffer = no λ ()
Unit <:? (_ * _) = no λ ()
Unit <:? (_ + _) = no λ ()
Unit <:? (_ ⇒[ _ ] _) = no λ ()
Unit <:? (μ-type _) = no λ ()
Unit <:? (ν-type _) = no λ ()
Int <:? Int = yes sub-int
Int <:? Unit = no λ ()
Int <:? Void = no λ ()
Int <:? Float = no λ ()
Int <:? Str = no λ ()
Int <:? Buffer = no λ ()
Int <:? (_ * _) = no λ ()
Int <:? (_ + _) = no λ ()
Int <:? (_ ⇒[ _ ] _) = no λ ()
Int <:? (μ-type _) = no λ ()
Int <:? (ν-type _) = no λ ()
Float <:? Float = yes sub-float
Float <:? Unit = no λ ()
Float <:? Void = no λ ()
Float <:? Int = no λ ()
Float <:? Str = no λ ()
Float <:? Buffer = no λ ()
Float <:? (_ * _) = no λ ()
Float <:? (_ + _) = no λ ()
Float <:? (_ ⇒[ _ ] _) = no λ ()
Float <:? (μ-type _) = no λ ()
Float <:? (ν-type _) = no λ ()
Str <:? Str = yes sub-str
Str <:? Unit = no λ ()
Str <:? Void = no λ ()
Str <:? Int = no λ ()
Str <:? Float = no λ ()
Str <:? Buffer = no λ ()
Str <:? (_ * _) = no λ ()
Str <:? (_ + _) = no λ ()
Str <:? (_ ⇒[ _ ] _) = no λ ()
Str <:? (μ-type _) = no λ ()
Str <:? (ν-type _) = no λ ()
Buffer <:? Buffer = yes sub-buffer
Buffer <:? Unit = no λ ()
Buffer <:? Void = no λ ()
Buffer <:? Int = no λ ()
Buffer <:? Float = no λ ()
Buffer <:? Str = no λ ()
Buffer <:? (_ * _) = no λ ()
Buffer <:? (_ + _) = no λ ()
Buffer <:? (_ ⇒[ _ ] _) = no λ ()
Buffer <:? (μ-type _) = no λ ()
Buffer <:? (ν-type _) = no λ ()
(A ⇒[ mk-kind q π ] B) <:? (A′ ⇒[ mk-kind q′ π′ ] B′) = arr-aux (q ≟q q′) (A′ <:? A) (B <:? B′) (π ⊑π? π′)
(_ ⇒[ _ ] _) <:? Unit = no λ ()
(_ ⇒[ _ ] _) <:? Void = no λ ()
(_ ⇒[ _ ] _) <:? Int = no λ ()
(_ ⇒[ _ ] _) <:? Float = no λ ()
(_ ⇒[ _ ] _) <:? Str = no λ ()
(_ ⇒[ _ ] _) <:? Buffer = no λ ()
(_ ⇒[ _ ] _) <:? (_ * _) = no λ ()
(_ ⇒[ _ ] _) <:? (_ + _) = no λ ()
(_ ⇒[ _ ] _) <:? (μ-type _) = no λ ()
(_ ⇒[ _ ] _) <:? (ν-type _) = no λ ()
(A * B) <:? (A′ * B′) = prod-aux (A <:? A′) (B <:? B′)
(_ * _) <:? Unit = no λ ()
(_ * _) <:? Void = no λ ()
(_ * _) <:? Int = no λ ()
(_ * _) <:? Float = no λ ()
(_ * _) <:? Str = no λ ()
(_ * _) <:? Buffer = no λ ()
(_ * _) <:? (_ + _) = no λ ()
(_ * _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ * _) <:? (μ-type _) = no λ ()
(_ * _) <:? (ν-type _) = no λ ()
(A + B) <:? (A′ + B′) = sum-aux (A <:? A′) (B <:? B′)
(_ + _) <:? Unit = no λ ()
(_ + _) <:? Void = no λ ()
(_ + _) <:? Int = no λ ()
(_ + _) <:? Float = no λ ()
(_ + _) <:? Str = no λ ()
(_ + _) <:? Buffer = no λ ()
(_ + _) <:? (_ * _) = no λ ()
(_ + _) <:? (_ ⇒[ _ ] _) = no λ ()
(_ + _) <:? (μ-type _) = no λ ()
(_ + _) <:? (ν-type _) = no λ ()
μ-type F <:? μ-type G = μ-aux (F ≟F G)
μ-type _ <:? Unit = no λ ()
μ-type _ <:? Void = no λ ()
μ-type _ <:? Int = no λ ()
μ-type _ <:? Float = no λ ()
μ-type _ <:? Str = no λ ()
μ-type _ <:? Buffer = no λ ()
μ-type _ <:? (_ * _) = no λ ()
μ-type _ <:? (_ + _) = no λ ()
μ-type _ <:? (_ ⇒[ _ ] _) = no λ ()
μ-type _ <:? (ν-type _) = no λ ()
ν-type F <:? ν-type G = ν-aux (F ≟F G)
ν-type _ <:? Unit = no λ ()
ν-type _ <:? Void = no λ ()
ν-type _ <:? Int = no λ ()
ν-type _ <:? Float = no λ ()
ν-type _ <:? Str = no λ ()
ν-type _ <:? Buffer = no λ ()
ν-type _ <:? (_ * _) = no λ ()
ν-type _ <:? (_ + _) = no λ ()
ν-type _ <:? (_ ⇒[ _ ] _) = no λ ()
ν-type _ <:? (μ-type _) = no λ ()
