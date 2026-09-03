-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grammar.OpDecl — the RELATIONS for an operator declaration
-- `(op) : polytype` / `(op) param* = expr`, and nothing else (Plan 0.84).
--
-- Reachable from `correct` via `ParsesDecl`, so a spec reviewer must read it.
-- `sound-opDecl`/`complete-opDecl` and the scanner proofs stay in
-- `Once.Grammar.OpDeclBridge`.
------------------------------------------------------------------------

module Once.Spec.Grammar.OpDecl where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; reverse)
open import Data.String using (String) renaming (fromList to strFromList)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DTypeSig)
open import Once.Parser.Module.OpName using (otClose; otChar; opTokClass)
open import Once.Parser.Module.DeclTail using (colonHead; colDrop1)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)
open import Once.Spec.Grammar.FunDef using (ParsesFunDef)

------------------------------------------------------------------------
-- Operator-character scanner `( <opchars> )` (structural on the tail).
------------------------------------------------------------------------

data ParsesOpChars : List Token → List Char → String → List Token → Set where
  poc-close : ∀ {tok rest c cs} → opTokClass tok ≡ otClose →
              ParsesOpChars (tok ∷ rest) (c ∷ cs) (strFromList (reverse (c ∷ cs))) rest
  poc-char  : ∀ {tok rest cs ch s rest'} → opTokClass tok ≡ otChar ch →
              ParsesOpChars rest (ch ∷ cs) s rest' →
              ParsesOpChars (tok ∷ rest) cs s rest'

------------------------------------------------------------------------
-- What follows the operator name: a signature, or a definition.
------------------------------------------------------------------------

data ParsesOpAfter (name : String) : List Token → Decl → List Token → Set where
  poa-sig : ∀ {toks ty rest'} → colonHead toks ≡ true →
            ParsesPolyType (colDrop1 toks) ty rest' →
            ParsesOpAfter name toks (DTypeSig name ty) rest'
  poa-fun : ∀ {toks d rest'} → colonHead toks ≡ false →
            ParsesFunDef name toks d rest' →
            ParsesOpAfter name toks d rest'

------------------------------------------------------------------------
-- `(op)` declaration.
------------------------------------------------------------------------

data ParsesOpDecl : List Token → Decl → List Token → Set where
  pod-mk : ∀ {rest name rest1 d rest'} →
           ParsesOpChars rest [] name rest1 →
           ParsesOpAfter name rest1 d rest' →
           ParsesOpDecl (TLParen ∷ rest) d rest'
