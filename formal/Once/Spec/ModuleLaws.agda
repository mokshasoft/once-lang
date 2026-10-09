-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.ModuleLaws — the lemmas about `Once.Spec.Module`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Spec.ModuleLaws where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Contract using (ISig)
open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.Type.Rigid using (rigidOf; RigidFree)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Type.Honest using (HonestFFI)
import Once.Compile as C
import Once.Parser as Parser
import Once.Parser.Module.Core as P
open import Once.TypeCheck.Classify using (NamedCtx; ctxWithImportsAndPolys; topCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Spec.Module
open Parser.FunInfo using (funName; funBody; funType; funIsPrimitive)
open Parser.PolyFunInfo using (pfunType; pfunBody)

teleSig≡entrySig : ∀ {sc es} (mt : ModTele sc es) → teleSig mt ≡ entrySig es

teleSig≡entrySig []                                       = refl

teleSig≡entrySig (ffi {fi = fi} {ty = ty} ep et _ _ _ rest) rewrite ep | et = cong ((funName fi , ty) ∷_) (teleSig≡entrySig rest)

teleSig≡entrySig (mono {fi = fi} ep _ _ _ rest)            rewrite ep = teleSig≡entrySig rest

teleSig≡entrySig (poly _ rest)                            = teleSig≡entrySig rest
