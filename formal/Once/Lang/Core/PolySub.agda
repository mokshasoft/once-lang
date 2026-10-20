-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Core.PolySub — subtyping over open types (D226's judgment; a
-- variable is only below itself — no bounded quantification). It concerns
-- types alone, so it is stated once for every signature (the core judgment's
-- coercion, `PolyTyping.⊢coerce`, and a program's entry, `Telescope.entry`,
-- read the same relation).
------------------------------------------------------------------------

module Once.Lang.Core.PolySub where

open import Once.Lang.Type.Grade using (mk-kind; fin)
open import Once.Lang.Type.Sub using (_⊑π_; _<:_; <:-refl; sub-void; sub-unit; sub-int; sub-float; sub-rigid; sub-arr; sub-prod; sub-sum; sub-μ; sub-ν)
open import Once.Lang.Core.PolyTy using (Ty; var; Unit; Void; Int; Float; rigid; _⇒[_]_; _*_; _+_; μ-type; ν-type; GSub; _⟪_⟫)

infix 4 _<:ₚ_

data _<:ₚ_ {m} : Ty m → Ty m → Set where
  sub-var    : ∀ {i} → var i <:ₚ var i
  sub-void   : ∀ {B} → Void <:ₚ B
  sub-unit   : Unit <:ₚ Unit
  sub-int    : Int <:ₚ Int
  sub-float  : Float <:ₚ Float
  sub-rigid  : ∀ {k i} → rigid k i <:ₚ rigid k i
  sub-arr    : ∀ {A A′ B B′ q π π′}
             → A′ <:ₚ A → B <:ₚ B′ → π ⊑π π′
             → (A ⇒[ mk-kind q π ] B) <:ₚ (A′ ⇒[ mk-kind q π′ ] B′)
  sub-prod   : ∀ {A A′ B B′} → A <:ₚ A′ → B <:ₚ B′ → (A * B) <:ₚ (A′ * B′)
  sub-sum    : ∀ {A A′ B B′} → A <:ₚ A′ → B <:ₚ B′ → (A + B) <:ₚ (A′ + B′)
  sub-μ      : ∀ {F} → μ-type F <:ₚ μ-type F
  sub-ν      : ∀ {F φ φ′} → fin φ ⊑π fin φ′ → ν-type F φ <:ₚ ν-type F φ′

<:ₚ-⟪⟫ : ∀ {m} {A B : Ty m} (σ : GSub m) → A <:ₚ B → A ⟪ σ ⟫ <: B ⟪ σ ⟫
<:ₚ-⟪⟫ {A = var i} σ sub-var = <:-refl (σ i)
<:ₚ-⟪⟫ σ sub-void   = sub-void
<:ₚ-⟪⟫ σ sub-unit   = sub-unit
<:ₚ-⟪⟫ σ sub-int    = sub-int
<:ₚ-⟪⟫ σ sub-float  = sub-float
<:ₚ-⟪⟫ σ sub-rigid  = sub-rigid
<:ₚ-⟪⟫ σ (sub-arr a b g) = sub-arr (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b) g
<:ₚ-⟪⟫ σ (sub-prod a b)  = sub-prod (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b)
<:ₚ-⟪⟫ σ (sub-sum a b)   = sub-sum (<:ₚ-⟪⟫ σ a) (<:ₚ-⟪⟫ σ b)
<:ₚ-⟪⟫ σ sub-μ           = sub-μ
<:ₚ-⟪⟫ σ (sub-ν g)       = sub-ν g
