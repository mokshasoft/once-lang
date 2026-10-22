-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Scope — what a Spec definition is in the
-- compiler's scope (plan 0.121 §3.6, F5).
--
-- A polymorphic definition of the Spec's telescope is an entry of the
-- compiler's telescope table, found under its name; its schema says when it
-- has no type variables (ground), which instances of it there are (a kinded
-- instance), and whether it is an arrow whose codomain's variables occur in
-- its domain.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Signature using (Signature)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Internal.Type.Poly as TP
import Once.Internal.Type.Instance as LI
import Once.Spec.Type as ST
import Once.Spec.Grade as SG
import Once.Spec.Core.Syntax as SC
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecGrammar.Conv using (πS)

module Once.Adequacy.SpecFront.Scope
  {s : ℕ} (S′ : SC.Defs s) (imps : Imports) (polys : PolyCtx) {m : ℕ} (Δ : ST.KCtx m) where

open SC.Schema using (arity; kinds; type)

record PolyAt (d : Fin s) (x : String) : Set where
  field
    {sc}  : TP.PolyType
    {b}   : _
    {p}   : PolyCtx
    lki   : lookupImport imps x ≡ nothing
    lp    : lookupPolyPrefix polys x ≡ just (sc , b , p)
    -- no type variables: a ground schema, at its one type
    ground : arity (S′ SC.!! d) ≡ 0
           → Σ[ g ∈ TP.Ground sc ] (∀ τ → TyR Δ (TP.extractGround sc g) (type (S′ SC.!! d) ST.⟨ τ ⟩))
    open′  : 0 < arity (S′ SC.!! d) → ¬ TP.Ground sc
    -- a kinded instance, at its type
    inst   : ∀ (τ : ST.TySub (arity (S′ SC.!! d)) m) → ST.Respects (kinds (S′ SC.!! d)) Δ τ
           → ∀ {T} → TyR Δ T (type (S′ SC.!! d) ST.⟨ τ ⟩) → LI.KindedInstance sc T
    -- an arrow whose codomain's variables occur in its domain
    arrow  : ∀ {sd sco π′} → type (S′ SC.!! d) ≡ sd ST.⇒[ SG.mk-kind SG.Many π′ ] sco
           → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
           → ∀ π → πS π ≡ π′ → Σ[ sd₀ ∈ TP.PolyType ] Σ[ sc₀ ∈ TP.PolyType ] TP.ArrowSchema sc sd₀ sc₀ π × TP.CodVarsInDom sd₀ sc₀
