-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ModuleLaws — the lemmas about `Once.Module`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Adequacy.ModuleLaws where

open import Data.Product using (_,_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Once.Compile as C
import Once.Parser as Parser
import Once.Parser.Module.Core as P
open import Once.Module
open Parser.FunInfo using (funName)

teleSig≡entrySig : ∀ {sc es} (mt : ModTele sc es) → teleSig mt ≡ entrySig es

teleSig≡entrySig []                                       = refl

teleSig≡entrySig (ffi {fi = fi} {ty = ty} ep et _ _ rest) rewrite ep | et = cong ((funName fi , ty) ∷_) (teleSig≡entrySig rest)

teleSig≡entrySig (mono {fi = fi} ep _ _ _ rest)          rewrite ep = teleSig≡entrySig rest

teleSig≡entrySig (poly _ _ rest)                          = teleSig≡entrySig rest
