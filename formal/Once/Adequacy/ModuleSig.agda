-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ModuleSig — a module's FFI declarations, as a Spec signature
-- (plan 0.122 §5.6, stage f).
--
-- The compiler keeps an FFI declaration under its rendered name, the Spec
-- under its canonical name. A rendering reads back to the word name it
-- renders (`Render.parse-render`), so the module's declarations, each under
-- the name its rendering reads back to, are a signature that declares every
-- one under each word name rendering it (`SigIn`) — the signature a typed
-- telescope's checker scope is read against (`TypeCheck.SpecWitness.Pack`).
------------------------------------------------------------------------

module Once.Adequacy.ModuleSig where

open import Data.List using (map)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Contract using (ISig)
open import Once.Core.Decl using (declS)
open import Once.Module using (ModTele; teleSig)
open import Once.Adequacy.SpecFront.Render using (parseC; parse-render)
import Once.Core.Translate as TR

-- The declarations, each under the name its rendering reads back to.
sigOf : ISig → Signature
sigOf = map (λ { (x , T) → parseC x ∶ declS T })

-- Every declaration of a typed telescope is the signature's, under each word
-- name rendering it.
sig-in : ∀ {sc es} (mt : ModTele sc es) → TR.SigIn (sigOf (teleSig mt)) mt
sig-in mt {x} {T} m {c} wc e =
  subst (λ c′ → (c′ ∶ declS T) ∈ sigOf (teleSig mt))
        (trans (cong parseC (sym e)) (parse-render c wc))
        (∈-map⁺ (λ { (x , T) → parseC x ∶ declS T }) m)
  where open import Data.List.Membership.Propositional using (_∈_)
