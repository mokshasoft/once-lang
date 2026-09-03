-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grammar.Decl — the RELATION for one declaration, and nothing
-- else (Plan 0.84). This is the join point of the five decl forms.
--
-- It is the module a spec reviewer reaches from `ParsesText`; the five
-- sub-relations it names are re-exported so that reading this one module
-- gives the whole declaration grammar. `sound-decl`/`complete-decl` stay in
-- `Once.Grammar.DeclBridge`.
------------------------------------------------------------------------

module Once.Spec.Grammar.Decl where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DTypeSig)
open import Once.Parser.Module using (colonHead; colDrop1; eqHead)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)

open import Once.Spec.Grammar.Import    public using (ParsesImport)
open import Once.Spec.Grammar.TypeAlias public using (ParsesTypeAliasDecl)
open import Once.Spec.Grammar.Signature public using (ParsesSignature)
open import Once.Spec.Grammar.FunDef    public using (ParsesFunDef)
open import Once.Spec.Grammar.OpDecl    public using (ParsesOpDecl)

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
