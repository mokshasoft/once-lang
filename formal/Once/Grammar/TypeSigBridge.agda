-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.TypeSigBridge — independent relational spec + bridge for the
-- bare type-signature declaration `name : polytype` (the `pdb-colon` path, taken
-- when keyword checks fail and a `TColon` follows; a trailing `=` is rejected as
-- a type-alias body). Bottoms at the `ParsesPolyType` island. No postulate.
------------------------------------------------------------------------

module Once.Grammar.TypeSigBridge where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; length)
open import Data.Nat using (_<_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (PolyType)
open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DTypeSig; ParseAtB)
open import Once.Parser.Module using (pdb-colon; eqHead)
open import Once.Parser.PolyType using (parsePolyTypeB)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)
open import Once.Grammar.PolyTypeBridge using (parsePolyTypeB-sound; parsePolyTypeB-complete)

data ParsesTypeSig : List Token → Decl → List Token → Set where
  pts-mk : ∀ {w rest ty rest'} → ParsesPolyType rest ty rest' → eqHead rest' ≡ false →
           ParsesTypeSig (TWord w ∷ TColon ∷ rest) (DTypeSig w ty) rest'

sound-typesig : ∀ {w rest d rest'' bnd} →
  pdb-colon w rest (parsePolyTypeB rest) ≡ just (d , rest'' , bnd) →
  ParsesTypeSig (TWord w ∷ TColon ∷ rest) d rest''
sound-typesig {w} {rest} h with parsePolyTypeB rest in eq
... | just (ty , rest' , bnd') with eqHead rest' in eh
...   | false with refl ← h = pts-mk (parsePolyTypeB-sound eq) eh

complete-typesig : ∀ {w rest d rest''} → ParsesTypeSig (TWord w ∷ TColon ∷ rest) d rest'' →
  Σ[ bnd ∈ (length rest'' < length (TWord w ∷ TColon ∷ rest)) ]
    pdb-colon w rest (parsePolyTypeB rest) ≡ just (d , rest'' , bnd)
complete-typesig (pts-mk dpt neh) with parsePolyTypeB-complete dpt
... | (bnd' , eqB) rewrite eqB | neh = _ , refl
