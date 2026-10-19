-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Principal — A DEFINITION'S TYPE IS ITS PRINCIPAL TYPE
-- (D314, refined by D321; plan 0.119 D6).
--
-- The Spec (`Spec.Surface.Program.Principal`): a body's schema is least among
-- the types it checks at that keep the schema's DOMAINS (`Spec.Sub._<:ᶜ_`).
-- The compiler decides it through the type's LOWERINGS: every type strictly
-- below `T` over its domains is below one of `lowerings T` — a covariant
-- position replaced by `Void`, an arrow's grade or a stream's grade lowered —
-- so, checking being closed upward, `T` is principal exactly when the body
-- checks at none of them. Finitely many: the decision is the checker run on
-- each.
------------------------------------------------------------------------

module Once.Lang.Principal where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
open import Once.Lang.Type.Grade using (Purity; pure; act; eff; Finite; mk-kind)
import Once.Lang.Type.Grade as G
open import Once.Lang.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Int; Float; rigid)
open import Once.Lang.Syntax using (RawExpr)
open import Once.Lang.Typing.Scope using (NamedCtx)
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_)
open import Once.Lang.Context using (Usage)

-- the grades strictly below a grade, on the chain `pure ≤ act ≤ eff`
gradesBelow : Purity → List Purity
gradesBelow pure = []
gradesBelow act  = pure ∷ []
gradesBelow eff  = pure ∷ act ∷ []

finBelow : Finite → List Finite
finBelow G.pure = []
finBelow G.act  = G.pure ∷ []

lowerings : Type → List Type
lowerings Void        = []
lowerings Unit        = Void ∷ []
lowerings Int         = Void ∷ []
lowerings Float       = Void ∷ []
lowerings (rigid k i) = Void ∷ []
lowerings (μ-type F)  = Void ∷ []
lowerings (ν-type F φ) = Void ∷ map (ν-type F) (finBelow φ)
lowerings (A * B)     = Void ∷ (map (_* B) (lowerings A) ++ map (A *_) (lowerings B))
lowerings (A + B)     = Void ∷ (map (_+ B) (lowerings A) ++ map (A +_) (lowerings B))
lowerings (A ⇒[ mk-kind q π ] B) =
  Void ∷ (map (A ⇒[ mk-kind q π ]_) (lowerings B) ++ map (λ π′ → A ⇒[ mk-kind q π′ ] B) (gradesBelow π))

-- The body checks at none of its type's lowerings.
PrincipalAt : (ctx : NamedCtx) → RawExpr → Type → Set
PrincipalAt ctx e T = ∀ {X} → X ∈ lowerings T → ∀ {Ψ : Usage (NamedCtx.size ctx)} → ¬ (ctx ⊢ᶜ e ∶ X ⨾ Ψ)
