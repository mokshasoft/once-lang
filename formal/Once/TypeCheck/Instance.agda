-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Instance — a telescope entry's body at an instance.
--
-- D243/D252: a body typed ONCE, over its parameters, types at every kinded
-- ground instance of its type, with the same raw body: substituting types for
-- the parameters (`TySubst`) is a structural map over the judgment
-- (Void-insensitive by D251, annotations and what the scope declares ground).
------------------------------------------------------------------------

module Once.TypeCheck.Instance where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.Spec.Type using (Type; ∅ₖ)
open import Once.Spec.Context using ([])
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Internal.Type.Instance using (KindedInstance; rigidOf; kindsOf)
open import Once.Internal.Type.Schema using (kinded-instance)
open import Once.Internal.Typing.Scope using (PolyCtx)
open import Once.TypeCheck.Classify using (ctxAt; ctxWithImportsAndPolys; TopCtx)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_)
import Once.TypeCheck.TySubst as TS

inst-at : ∀ {tc : TopCtx} {polys : PolyCtx} {body} (sc : PolyType)
        → ctxAt (kindsOf sc) tc polys ⊢ᶜ body ∶ rigidOf sc ⨾ [] → ∀ {U : Type} → KindedInstance ∅ₖ sc U
        → ctxWithImportsAndPolys tc polys ⊢ᶜ body ∶ U ⨾ []
inst-at {tc} {polys} sc D ki with kinded-instance sc ki
... | τ , r , e = subst (λ X → _ ⊢ᶜ _ ∶ X ⨾ []) e (TS.subst-c (kindsOf sc) ∅ₖ τ r {ctx = ctxAt (kindsOf sc) tc polys} D)
