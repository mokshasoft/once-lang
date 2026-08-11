-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.SignatureBridge — independent relational spec + bridge for the
-- `signature` declaration `name : polytype [! shape]` (`parseSignatureB`).
-- Bottoms at the `ParsesPolyType` island + a small `ParsesEffAnnot` relation for
-- the optional `! halts`/`! emits` annotation.
------------------------------------------------------------------------

module Once.Grammar.SignatureBridge where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; length)
open import Data.Nat using (_<_; _≤_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Once.Type using (PolyType)
open import Once.SigEffect using (SigEffect)
open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DSignature; ParseAtB; anyWordB)
open import Once.Parser.Module.DeclTail
  using ( parseSignatureB; colonHead; colDrop1; psig-poly; psig-colon
        ; effAnnotShape; eaDrop2; parseEffAnnot; parseEffAnnot-go )
open import Once.Parser.PolyType using (parsePolyTypeB)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)
open import Once.Grammar.PolyTypeBridge using (parsePolyTypeB-sound; parsePolyTypeB-complete)
open import Once.Grammar.ImportBridge using (anyWordB-inv)

------------------------------------------------------------------------
-- Optional effect annotation `! halts` / `! emits`.
------------------------------------------------------------------------

data ParsesEffAnnot : List Token → Maybe SigEffect → List Token → Set where
  pea-some : ∀ {toks se} → effAnnotShape toks ≡ just se → ParsesEffAnnot toks (just se) (eaDrop2 toks)
  pea-none : ∀ {toks}    → effAnnotShape toks ≡ nothing → ParsesEffAnnot toks nothing toks

sound-effAnnot-go : ∀ (toks : List Token) (m : Maybe SigEffect) → effAnnotShape toks ≡ m →
  ParsesEffAnnot toks (proj₁ (parseEffAnnot-go toks m)) (proj₁ (proj₂ (parseEffAnnot-go toks m)))
sound-effAnnot-go toks (just se) eq = pea-some eq
sound-effAnnot-go toks nothing   eq = pea-none eq

sound-effAnnot : ∀ (toks : List Token) →
  ParsesEffAnnot toks (proj₁ (parseEffAnnot toks)) (proj₁ (proj₂ (parseEffAnnot toks)))
sound-effAnnot toks = sound-effAnnot-go toks (effAnnotShape toks) refl

complete-effAnnot-go : ∀ {toks meff rest''} (m : Maybe SigEffect) → effAnnotShape toks ≡ m →
  ParsesEffAnnot toks meff rest'' →
  Σ[ bndE ∈ (length rest'' ≤ length toks) ] parseEffAnnot-go toks m ≡ (meff , rest'' , bndE)
complete-effAnnot-go (just se) pf (pea-some eq) with refl ← just-injective (trans (sym pf) eq) = _ , refl
complete-effAnnot-go (just se) pf (pea-none eq) with trans (sym pf) eq
... | ()
complete-effAnnot-go nothing pf (pea-some eq) with trans (sym pf) eq
... | ()
complete-effAnnot-go nothing pf (pea-none eq) = _ , refl

complete-effAnnot : ∀ {toks meff rest''} → ParsesEffAnnot toks meff rest'' →
  Σ[ bndE ∈ (length rest'' ≤ length toks) ] parseEffAnnot toks ≡ (meff , rest'' , bndE)
complete-effAnnot {toks} dea = complete-effAnnot-go (effAnnotShape toks) refl dea

------------------------------------------------------------------------
-- `name : polytype [! shape]`.
------------------------------------------------------------------------

data ParsesSignature : List Token → Decl → List Token → Set where
  psig-mk : ∀ {name residual ty rest' meff rest''} →
            colonHead residual ≡ true →
            ParsesPolyType (colDrop1 residual) ty rest' →
            ParsesEffAnnot rest' meff rest'' →
            ParsesSignature (TWord name ∷ residual) (DSignature name nothing ty meff) rest''

sound-signature : ∀ {toks d rest'' bnd} → parseSignatureB toks ≡ just (d , rest'' , bnd) →
  ParsesSignature toks d rest''
sound-signature {toks} h with anyWordB toks in aw
... | just (name , residual , bnd) with anyWordB-inv aw
...   | refl with colonHead residual in ch
...     | true with parsePolyTypeB (colDrop1 residual) in pp
...       | just (ty , rest' , bnd') with refl ← h =
            psig-mk ch (parsePolyTypeB-sound pp) (sound-effAnnot rest')

complete-signature : ∀ {toks d rest''} → ParsesSignature toks d rest'' →
  Σ[ bnd ∈ (length rest'' < length toks) ] parseSignatureB toks ≡ just (d , rest'' , bnd)
complete-signature (psig-mk ch dpt dea) rewrite ch with parsePolyTypeB-complete dpt
... | (bnd' , ppEq) rewrite ppEq with complete-effAnnot dea
...   | (bndE , eaEq) rewrite eaEq = _ , refl
