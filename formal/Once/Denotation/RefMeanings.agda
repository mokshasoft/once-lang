-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.RefMeanings — what a scope's references mean: a value for
-- each telescope definition at each kinded instance of its schema, for each
-- import, and for each generator of the signature in scope (D274), all in
-- the Spec's domain read at an instance `σ` of no type variables.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (TySub)

module Once.Denotation.RefMeanings (Σ : Signature) (σ : TySub 0 0) where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type using (Type; KCtx)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Typing.Scope using (NamedCtx; PolyCtx; Imports; lookupImport)
open import Once.Denotation.DefEnv using (DefEnvOf; ImpEnvOf)
open import Once.Denotation.SpecDomain Σ σ using (⟦_⟧ᵛ)

DefFamily : PolyType → Set
DefFamily s = ∀ {Δ : KCtx 0} (U : Type) → KindedInstance Δ s U → ⟦ U ⟧ᵛ

DefMeanings : PolyCtx → Set
DefMeanings = DefEnvOf DefFamily

ImpMeanings : Imports → Set
ImpMeanings = ImpEnvOf (λ U → ⟦ U ⟧ᵛ)

record Meanings (polys : PolyCtx) (imps : Imports) (sg : Imports) : Set where
  constructor meanings
  field
    defs    : DefMeanings polys
    entries : ImpMeanings imps
    -- …and of every generator of the signature in scope (D274): what a
    -- resolved reference names, a declaration of Σ (plan 0.122: read in the
    -- world's model, or the Spec's call of the operation).
    sigs    : ∀ {cn T} → WordName cn → lookupImport sg (showCanonical cn) ≡ just T → IsConcrete T → ⟦ T ⟧ᵛ

MeaningsOf : ∀ {m} → NamedCtx m → Set
MeaningsOf ctx = Meanings (NamedCtx.polys ctx) (NamedCtx.imports ctx) (NamedCtx.sig ctx)
