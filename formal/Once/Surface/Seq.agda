-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Seq
--
-- Plan 0.94 §13: "evaluate `a`, discard its value, continue with `b`" — needed
-- where a subterm is REACHED by evaluation but its value is not used (the left
-- operand of `e + v` with `v ∶ Void`; the arms of `case f g` given `Void`,
-- which are built before any input). No new term former: it is
-- `snd' (pair a b)` — the pair evaluates `a` then `b`, the projection keeps
-- `b`'s value — and it uses exactly `Ψa +ᵘ Ψb`.
------------------------------------------------------------------------
module Once.Surface.Seq where

open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans; cong)
open import Once.Type
open import Once.IR as IR using ()
open import Once.Surface.Syntax
open import Once.Surface.Properties using (+ᵘ-identityʳ; +ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Once.Surface.Elaborate using (elaborate)

seq : ∀ {n} {Γ : Ctx n} {Ψa Ψb : Usage n} {A B : Type}
    → Expr Γ Ψa A → Expr Γ Ψb B → Expr Γ (Ψa +ᵘ Ψb) B
seq a b = snd' (pair a b)

-- Continue with a closed term.
seq0 : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Type}
     → Expr Γ Ψ A → Expr Γ zeroUsage B → Expr Γ Ψ B
seq0 {Γ = Γ} {Ψ} {B = B} a b = subst (λ Ψ′ → Expr Γ Ψ′ B) (+ᵘ-identityʳ Ψ) (seq a b)

-- A CLOSED term, evaluated in any context — the way `realize` embeds a
-- top-level definition's body: elaborate it to a morphism from `Unit` and apply
-- it to `unit`. (Used for a `cata` algebra, which is typed without locals.)
closed-usage-eq : ∀ {n} → (zeroUsage {n}) +ᵘ (Many *ᵘ zeroUsage) ≡ zeroUsage
closed-usage-eq = trans (cong (zeroUsage +ᵘ_) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)

-- Plan 0.103 phase 1c: the surface `closed` former, not an embedding through
-- the IR (which would lower the term's definition references to internal
-- calls instead of reading them from the definitions environment).
embedClosed : ∀ {n} {Γ : Ctx n} {A : Type} → Expr ∅ [] A → Expr Γ zeroUsage A
embedClosed e = closed e
