-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grammar.Signature — the RELATION for the `signature` declaration
-- `name : polytype [! shape]`, and nothing else (Plan 0.84).
--
-- Reachable from `correct` via `ParsesDecl`, so a spec reviewer must read it.
-- `sound-signature`/`complete-signature` — the evidence that
-- `parseSignatureB` meets this — stay in `Once.Grammar.SignatureBridge`.
------------------------------------------------------------------------

module Once.Spec.Grammar.Signature where

open import Data.Bool using (true)
open import Data.List using (List; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.SigEffect using (SigEffect)
open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DSignature)
open import Once.Parser.Module.DeclTail using (colonHead; colDrop1; effAnnotShape; eaDrop2)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)

------------------------------------------------------------------------
-- Optional effect annotation `! halts` / `! emits`.
------------------------------------------------------------------------

data ParsesEffAnnot : List Token → Maybe SigEffect → List Token → Set where
  pea-some : ∀ {toks se} → effAnnotShape toks ≡ just se → ParsesEffAnnot toks (just se) (eaDrop2 toks)
  pea-none : ∀ {toks}    → effAnnotShape toks ≡ nothing → ParsesEffAnnot toks nothing toks

------------------------------------------------------------------------
-- `name : polytype [! shape]`.
------------------------------------------------------------------------

data ParsesSignature : List Token → Decl → List Token → Set where
  psig-mk : ∀ {name residual ty rest' meff rest''} →
            colonHead residual ≡ true →
            ParsesPolyType (colDrop1 residual) ty rest' →
            ParsesEffAnnot rest' meff rest'' →
            ParsesSignature (TWord name ∷ residual) (DSignature name nothing ty meff) rest''
