-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Instance — a telescope entry's body at an instance.
--
-- D243/D252: a body typed ONCE, at its schema with rigid parameters, types at
-- every kinded instance of the schema, with the same raw body: the surface
-- rigid substitution (`RigidSubst`) is a structural map over the judgment
-- (Void-insensitive by D251, annotations fixed by D252, imports ground).
------------------------------------------------------------------------

module Once.TypeCheck.Instance where

import Once.Lang.Type.WellFormed
open import Data.Product using (_×_; proj₁; proj₂)
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.Lang.Type.Poly using (PolyType)
open import Once.Lang.Type.Instance using (KindedInstance; rigidOf)
import Once.Lang.Context as C
open import Once.Lang.Core.Schema using (kindsOf; kinded-instance)
open import Once.Lang.Typing.Scope using (PolyCtx)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys; TopCtx)
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_)
import Once.TypeCheck.RigidSubst as RS

inst-at : ∀ {tc : TopCtx} {polys : PolyCtx} {body : _} (sc : PolyType)
        → (∀ {x T} → Once.Lang.Typing.Scope.lookupImport (TopCtx.tdefs tc) x ≡ Data.Maybe.just T → Once.Lang.Type.WellFormed.RigidFree T)
        × (∀ {x T} → Once.Lang.Typing.Scope.lookupImport (TopCtx.tsig tc) x ≡ Data.Maybe.just T → Once.Lang.Type.WellFormed.RigidFree T)
        → ctxWithImportsAndPolys tc polys ⊢ᶜ body ∶ rigidOf sc ⨾ C.Usage.[] → ∀ {U} → KindedInstance sc U
        → ctxWithImportsAndPolys tc polys ⊢ᶜ body ∶ U ⨾ C.Usage.[]
inst-at sc irf D ki =
  subst (λ X → _ ⊢ᶜ _ ∶ X ⨾ C.Usage.[]) (proj₂ (proj₂ (kinded-instance sc ki)))
        (RS.subst-c (kindsOf sc) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))) irf D)
