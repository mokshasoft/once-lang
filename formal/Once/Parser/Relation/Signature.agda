-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Relation.Signature — the RELATION for the `signature` declaration
-- `name : polytype [! shape]`, and nothing else (Plan 0.84).
--
-- A waypoint of the parser's proof, reached through `ParsesDecl`.
-- `sound-signature`/`complete-signature` — the evidence that
-- `parseSignatureB` meets this — stay in `Once.Grammar.SignatureBridge`.
------------------------------------------------------------------------

module Once.Parser.Relation.Signature where

open import Data.Bool using (true)
open import Data.List using (List; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Spec.Surface.Syntax using (Decl; DSignature)
open import Once.Parser.Module.DeclTail using (colonHead; colDrop1)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)

data ParsesSignature : List Token → Decl → List Token → Set where
  psig-mk : ∀ {name residual ty rest'} →
            colonHead residual ≡ true →
            ParsesPolyType (colDrop1 residual) ty rest' →
            ParsesSignature (TWord name ∷ residual) (DSignature name ty) rest'
