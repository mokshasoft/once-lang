-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.SignatureBridge — independent relational spec + bridge for the
-- `signature` declaration `name : polytype [! shape]` (`parseSignatureB`).
-- Bottoms at the `ParsesPolyType` island + a small `ParsesEffAnnot` relation for
-- the optional `! halts`/`! emits` annotation.
------------------------------------------------------------------------

module Once.Grammar.SignatureBridge where

open import Data.Bool using (true)
open import Data.List using (length)
open import Data.Nat using (_<_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (anyWordB)
open import Once.Parser.Module.DeclTail
  using (parseSignatureB; colonHead; colDrop1)
open import Once.Parser.PolyType using (parsePolyTypeB)
open import Once.Spec.Grammar.Signature
  using (ParsesSignature; psig-mk)
open import Once.Grammar.PolyTypeBridge using (parsePolyTypeB-sound; parsePolyTypeB-complete)
open import Once.Grammar.ImportBridge using (anyWordB-inv)

------------------------------------------------------------------------
-- `name : polytype`.
------------------------------------------------------------------------

-- The relation is in `Once.Spec.Grammar.Signature` (plan 0.84).

sound-signature : ∀ {toks d rest'' bnd} → parseSignatureB toks ≡ just (d , rest'' , bnd) →
  ParsesSignature toks d rest''
sound-signature {toks} h with anyWordB toks in aw
... | just (name , residual , bnd) with anyWordB-inv aw
...   | refl with colonHead residual in ch
...     | true with parsePolyTypeB (colDrop1 residual) in pp
...       | just (ty , rest' , bnd') with refl ← h =
            psig-mk ch (parsePolyTypeB-sound pp)

complete-signature : ∀ {toks d rest''} → ParsesSignature toks d rest'' →
  Σ[ bnd ∈ (length rest'' < length toks) ] parseSignatureB toks ≡ just (d , rest'' , bnd)
complete-signature (psig-mk ch dpt) rewrite ch with parsePolyTypeB-complete dpt
... | (bnd' , ppEq) rewrite ppEq = _ , refl
