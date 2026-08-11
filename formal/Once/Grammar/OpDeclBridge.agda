-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.OpDeclBridge — independent relational spec + bridge for the
-- operator-form declaration `(op)` followed by a type signature or a function
-- definition (`tryOpDeclB`). The operator-name scanner `parseOpCharsB` is
-- structural (recurses on the tail), so its relation `ParsesOpChars` is too.
-- Bottoms at `ParsesPolyType` + the reused `ParsesFunDef`.
------------------------------------------------------------------------

module Once.Grammar.OpDeclBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.String using (String) renaming (fromList to strFromList)
open import Data.Nat using (_<_; _≤_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (PolyType)
open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DTypeSig; ParseAtB; ParseAtB≤)
open import Once.Parser.Module.OpName
  using (OpTok; otClose; otChar; otNone; opTokClass; parseOpCharsB; pocGo; parseOperatorNameB)
open import Once.Parser.Module.DeclTail using (colonHead; colDrop1)
open import Once.Parser.Module.FunDef.Def using (parseFunDefB)
open import Once.Parser.Module.FunDef.OpDecl using (tryOpDeclB; tryOpDeclAfterB)
open import Once.Parser.PolyType using (parsePolyTypeB)
open import Once.Parser.Generic.PolyInst using (ParsesPolyType)
open import Once.Grammar.PolyTypeBridge using (parsePolyTypeB-sound; parsePolyTypeB-complete)
open import Once.Grammar.FunDefBridge using (ParsesFunDef; sound-fundef; complete-fundef)

------------------------------------------------------------------------
-- Operator-character scanner `( <opchars> )` (structural on the tail).
------------------------------------------------------------------------

data ParsesOpChars : List Token → List Char → String → List Token → Set where
  poc-close : ∀ {tok rest c cs} → opTokClass tok ≡ otClose →
              ParsesOpChars (tok ∷ rest) (c ∷ cs) (strFromList (reverse (c ∷ cs))) rest
  poc-char  : ∀ {tok rest cs ch s rest'} → opTokClass tok ≡ otChar ch →
              ParsesOpChars rest (ch ∷ cs) s rest' →
              ParsesOpChars (tok ∷ rest) cs s rest'

-- `with opTokClass tok` freezes `pocGo`; delegate to a helper that takes the
-- OpTok as a concrete parameter (applied at the stuck `opTokClass tok`).
sound-opChars : ∀ (toks : List Token) (cs : List Char) {s rest bnd} →
  parseOpCharsB toks cs ≡ just (s , rest , bnd) → ParsesOpChars toks cs s rest
sound-pocGo : ∀ (tok : Token) (rest : List Token) (cs : List Char) (ot : OpTok) →
  opTokClass tok ≡ ot → {s : String} {rest' : List Token} {bnd : length rest' < length (tok ∷ rest)} →
  pocGo tok rest cs ot ≡ just (s , rest' , bnd) → ParsesOpChars (tok ∷ rest) cs s rest'

sound-opChars [] cs h with () ← h
sound-opChars (tok ∷ rest) cs h = sound-pocGo tok rest cs (opTokClass tok) refl h

sound-pocGo tok rest []       otClose     eq h with () ← h
sound-pocGo tok rest (c ∷ cs) otClose     eq h with refl ← h = poc-close eq
sound-pocGo tok rest cs       (otChar ch) eq h with parseOpCharsB rest (ch ∷ cs) in pp
... | just (s , rest' , bnd) with refl ← h = poc-char eq (sound-opChars rest (ch ∷ cs) pp)
... | nothing with () ← h
sound-pocGo tok rest cs       otNone      eq h with () ← h

complete-opChars : ∀ {toks cs s rest} → ParsesOpChars toks cs s rest →
  Σ[ bnd ∈ (length rest < length toks) ] parseOpCharsB toks cs ≡ just (s , rest , bnd)
complete-opChars (poc-close eq) rewrite eq = _ , refl
complete-opChars (poc-char eq dsub) rewrite eq with complete-opChars dsub
... | (bnd , sub) rewrite sub = _ , refl

------------------------------------------------------------------------
-- After the operator name: `: polytype` signature, else a function def.
------------------------------------------------------------------------

data ParsesOpAfter (name : String) : List Token → Decl → List Token → Set where
  poa-sig : ∀ {toks ty rest'} → colonHead toks ≡ true →
            ParsesPolyType (colDrop1 toks) ty rest' →
            ParsesOpAfter name toks (DTypeSig name ty) rest'
  poa-fun : ∀ {toks d rest'} → colonHead toks ≡ false →
            ParsesFunDef name toks d rest' →
            ParsesOpAfter name toks d rest'

sound-opAfter : ∀ {name toks d rest' bnd} → tryOpDeclAfterB name toks ≡ just (d , rest' , bnd) →
  ParsesOpAfter name toks d rest'
sound-opAfter {name} {toks} h with colonHead toks in ch
... | true with parsePolyTypeB (colDrop1 toks) in pp
...   | just (ty , rest' , bnd) with refl ← h = poa-sig ch (parsePolyTypeB-sound pp)
sound-opAfter {name} {toks} h | false with parseFunDefB name toks in pf
... | just (d , rest' , bnd) with refl ← h = poa-fun ch (sound-fundef pf)

complete-opAfter : ∀ {name toks d rest'} → ParsesOpAfter name toks d rest' →
  Σ[ bnd ∈ (length rest' ≤ length toks) ] tryOpDeclAfterB name toks ≡ just (d , rest' , bnd)
complete-opAfter (poa-sig ch dpt) rewrite ch with parsePolyTypeB-complete dpt
... | (bnd , pp) rewrite pp = _ , refl
complete-opAfter (poa-fun ch dfd) rewrite ch with complete-fundef dfd
... | (bnd , pf) rewrite pf = _ , refl

------------------------------------------------------------------------
-- `(op)` declaration.
------------------------------------------------------------------------

data ParsesOpDecl : List Token → Decl → List Token → Set where
  pod-mk : ∀ {rest name rest1 d rest'} →
           ParsesOpChars rest [] name rest1 →
           ParsesOpAfter name rest1 d rest' →
           ParsesOpDecl (TLParen ∷ rest) d rest'

sound-opDecl : ∀ {toks d rest'' bnd} → tryOpDeclB toks ≡ just (d , rest'' , bnd) →
  ParsesOpDecl toks d rest''
sound-opDecl {TLParen ∷ rest} h with parseOpCharsB rest [] in pp
... | just (name , rest1 , bnd0) with tryOpDeclAfterB name rest1 in ta
...   | just (d , rest' , bnd') with refl ← h = pod-mk (sound-opChars rest [] pp) (sound-opAfter ta)

complete-opDecl : ∀ {toks d rest'} → ParsesOpDecl toks d rest' →
  Σ[ bnd ∈ (length rest' < length toks) ] tryOpDeclB toks ≡ just (d , rest' , bnd)
complete-opDecl (pod-mk doc doa) with complete-opChars doc
... | (bnd0 , pp) rewrite pp with complete-opAfter doa
...   | (bnd' , ta) rewrite ta = _ , refl
