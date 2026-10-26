-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Relation.TypeAlias — the RELATION for `type Name param* = Type`,
-- and nothing else (Plan 0.84).
--
-- A waypoint of the parser's proof, reached through `ParsesDecl`.
-- `sound-typealias`/`complete-typealias` and the WF scanner proofs stay in
-- `Once.Grammar.TypeAliasBridge`.
--
-- `ParsesType` is NOT moved: `Once.Parser.TypeRelation` is already proof-free
-- and deliberately lives in the parser hierarchy so the parser's return type
-- can mention it (plan 0.84 §3a).
------------------------------------------------------------------------

module Once.Parser.Relation.TypeAlias where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; reverse)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (wordHead)
open import Once.Spec.Surface.Syntax using (Decl; DTypeAlias)
open import Once.Parser.Module.DeclTail using (taEqHead; taDrop1)
open import Once.Parser.TypeRelation using (ParsesType)
open import Once.Type.Poly using (polyOf)

------------------------------------------------------------------------
-- Param scanner `param* = Type` (params accumulator). Bottoms at `ParsesType`.
------------------------------------------------------------------------

data ParsesTypeAlias (name : String) : List String → List Token → Decl → List Token → Set where
  gta-eq-r   : ∀ {params toks ty rest''} → wordHead toks ≡ false → taEqHead toks ≡ true →
               ParsesType (taDrop1 toks) ty rest'' →
               ParsesTypeAlias name params toks (DTypeAlias name (reverse params) (polyOf ty)) rest''
  gta-word-r : ∀ {params p rest' d rest''} → ParsesTypeAlias name (p ∷ params) rest' d rest'' →
               ParsesTypeAlias name params (TWord p ∷ rest') d rest''

------------------------------------------------------------------------
-- `type Name param* = Type` (consume the alias name, then the scanner).
------------------------------------------------------------------------

data ParsesTypeAliasDecl : List Token → Decl → List Token → Set where
  pta-mk : ∀ {name rest d rest'} → ParsesTypeAlias name [] rest d rest' →
           ParsesTypeAliasDecl (TWord name ∷ rest) d rest'
