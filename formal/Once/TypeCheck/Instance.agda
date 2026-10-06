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

open import Data.Product using (_×_; proj₁; proj₂)
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.Type using (PolyType)
open import Once.Type.Rigid using (KindedInstance; rigidOf)
import Once.Surface.Context as C
open import Once.Spec.Core.Schema using (kindsOf; kinded-instance)
open import Once.TypeCheck.Classify using (Imports; PolyCtx; ctxWithImportsAndPolys; TopCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.TypeCheck.RigidSubst as RS

inst-at : ∀ {tc : TopCtx} {polys : PolyCtx} {body : _} (sc : PolyType)
        → (∀ {x T} → Once.TypeCheck.Classify.lookupImport (TopCtx.tdefs tc) x ≡ Data.Maybe.just T → Once.Type.Rigid.RigidFree T)
        × (∀ {x T} → Once.TypeCheck.Classify.lookupImport (TopCtx.tsig tc) x ≡ Data.Maybe.just T → Once.Type.Rigid.RigidFree T)
        → ctxWithImportsAndPolys tc polys ⊢ᶜ body ∶ rigidOf sc ⨾ C.Usage.[] → ∀ {U} → KindedInstance sc U
        → ctxWithImportsAndPolys tc polys ⊢ᶜ body ∶ U ⨾ C.Usage.[]
inst-at sc irf D ki =
  subst (λ X → _ ⊢ᶜ _ ∶ X ⨾ C.Usage.[]) (proj₂ (proj₂ (kinded-instance sc ki)))
        (RS.subst-c (kindsOf sc) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))) irf D)
