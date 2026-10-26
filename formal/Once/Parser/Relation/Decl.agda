-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Relation.Decl — the RELATION for one declaration, and nothing
-- else (Plan 0.84). This is the join point of the five decl forms.
--
-- A waypoint of the parser's proof (`Once.Parser.Relation.Parsing`).
-- `sound-decl`/`complete-decl` are in `Once.Grammar.DeclBridge`.
------------------------------------------------------------------------

module Once.Parser.Relation.Decl where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig)
import Once.Parser.Module
open import Once.Parser.Module.FunDef.Body using (eqHead)
open import Once.Parser.Module.DeclTail using (colDrop1; colonHead)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)

open import Once.Parser.Relation.Import using (ParsesImport)
open import Once.Parser.Relation.TypeAlias using (ParsesTypeAliasDecl)
open import Once.Parser.Relation.Signature using (ParsesSignature)
open import Once.Parser.Relation.FunDef using (ParsesFunDef)
open import Once.Parser.Relation.OpDecl using (ParsesOpDecl)

data ParsesDecl : List Token → Decl → List Token → Set where
  pd-import    : ∀ {rest d rest'} → ParsesImport rest d rest' →
                 ParsesDecl (TWord "import" ∷ rest) d rest'
  pd-typealias : ∀ {rest d rest'} → ParsesTypeAliasDecl rest d rest' →
                 ParsesDecl (TWord "type" ∷ rest) d rest'
  pd-signature : ∀ {rest d rest'} → ParsesSignature rest d rest' →
                 ParsesDecl (TWord "signature" ∷ rest) d rest'
  pd-typesig   : ∀ {w rest ty rest'} → ¬ (w ≡ "import") → ¬ (w ≡ "type") → ¬ (w ≡ "signature") →
                 colonHead rest ≡ true → ParsesPolyType (colDrop1 rest) ty rest' → eqHead rest' ≡ false →
                 ParsesDecl (TWord w ∷ rest) (DTypeSig w ty) rest'
  pd-fundef    : ∀ {w rest d rest'} → ¬ (w ≡ "import") → ¬ (w ≡ "type") → ¬ (w ≡ "signature") →
                 colonHead rest ≡ false → ParsesFunDef w rest d rest' →
                 ParsesDecl (TWord w ∷ rest) d rest'
  pd-opdecl    : ∀ {rest d rest'} → ParsesOpDecl (TLParen ∷ rest) d rest' →
                 ParsesDecl (TLParen ∷ rest) d rest'
