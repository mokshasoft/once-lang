{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Type.Sub — subtyping `A <: B`.
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
-- of one `case` meet there. `Once.Internal.Type.Join` decides it.
--
-- The relations are the Spec's (`Once.Spec.Sub`); this module keeps the
-- compiler's older constructor names while plan 0.122 renames their users, and
-- proves reflexivity and that keeping the domains is a special case.
------------------------------------------------------------------------

module Once.Internal.Type.Sub where

open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind; _·p_; fin; _⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Spec.Type using (Ty; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Sub

pattern sub-prod a b = sub-* a b
pattern sub-sum a b = sub-+ a b
pattern sub-rigid = sub-var
pattern subᶜ-prod a b = subᶜ-* a b
pattern subᶜ-sum a b = subᶜ-+ a b
pattern subᶜ-rigid = subᶜ-var

-- Running a grade twice stays within it (the product is idempotent). What a rule with one grade for two sequenced parts
-- reads its product as.
·p-diag : ∀ π → (π ·p π) ⊑π π
·p-diag pure = ⊑-pure
·p-diag act  = ⊑-act
·p-diag eff  = ⊑-eff

-- The identities of the order and of the thin category of types.
⊑π-refl : ∀ π → π ⊑π π
⊑π-refl pure = ⊑-pure
⊑π-refl act = ⊑-act
⊑π-refl eff = ⊑-eff

<:-refl : ∀ {m} (A : Ty m) → A <: A
<:-refl (var _) = sub-var
<:-refl Unit   = sub-unit
<:-refl Void   = sub-void
<:-refl Int    = sub-int
<:-refl Float  = sub-float
<:-refl (A ⇒[ mk-kind q π ] B) = sub-arr (<:-refl A) (<:-refl B) (⊑π-refl π)
<:-refl (A * B) = sub-* (<:-refl A) (<:-refl B)
<:-refl (A + B) = sub-+ (<:-refl A) (<:-refl B)
<:-refl (μ F) = sub-μ
<:-refl (ν F φ) = sub-ν (⊑π-refl (fin φ))

-- Keeping the domains is a special case of converting.
<:ᶜ⇒<: : ∀ {m} {A B : Ty m} → A <:ᶜ B → A <: B
<:ᶜ⇒<: subᶜ-void        = sub-void
<:ᶜ⇒<: subᶜ-var         = sub-var
<:ᶜ⇒<: subᶜ-unit        = sub-unit
<:ᶜ⇒<: subᶜ-int         = sub-int
<:ᶜ⇒<: subᶜ-float       = sub-float
<:ᶜ⇒<: (subᶜ-arr {A = A} b g) = sub-arr (<:-refl A) (<:ᶜ⇒<: b) g
<:ᶜ⇒<: (subᶜ-* a b)     = sub-* (<:ᶜ⇒<: a) (<:ᶜ⇒<: b)
<:ᶜ⇒<: (subᶜ-+ a b)     = sub-+ (<:ᶜ⇒<: a) (<:ᶜ⇒<: b)
<:ᶜ⇒<: subᶜ-μ           = sub-μ
<:ᶜ⇒<: (subᶜ-ν g)       = sub-ν g

<:ᶜ-refl : ∀ {m} (A : Ty m) → A <:ᶜ A
<:ᶜ-refl (var _) = subᶜ-var
<:ᶜ-refl Unit   = subᶜ-unit
<:ᶜ-refl Void   = subᶜ-void
<:ᶜ-refl Int    = subᶜ-int
<:ᶜ-refl Float  = subᶜ-float
<:ᶜ-refl (A ⇒[ mk-kind q π ] B) = subᶜ-arr (<:ᶜ-refl B) (⊑π-refl π)
<:ᶜ-refl (A * B) = subᶜ-* (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (A + B) = subᶜ-+ (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (μ F) = subᶜ-μ
<:ᶜ-refl (ν F φ) = subᶜ-ν (⊑π-refl (fin φ))
