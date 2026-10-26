-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Scope — where a Spec definition is in the
-- compiler's scope (plan 0.121 §3.6, F5).
--
-- A polymorphic definition of the Spec's telescope is an entry of the
-- compiler's telescope table, found under its name (and no monomorphic
-- definition's) — the lookups the checker makes for it (`View.InView`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Once.Spec.Surface.Syntax as TP
import Once.Spec.Core.Syntax as SC
open import Once.TypeCheck.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)

module Once.Adequacy.SpecFront.Scope
  {s : ℕ} (S′ : SC.Defs s) (imps : Imports) (polys : PolyCtx) where

record PolyAt (d : Fin s) (x : String) : Set where
  field
    {sc}  : TP.PolyType
    {b}   : _
    {p}   : PolyCtx
    lki   : lookupImport imps x ≡ nothing
    lp    : lookupPolyPrefix polys x ≡ just (sc , b , p)
