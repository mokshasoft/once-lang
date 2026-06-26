-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Generic.Parser — the generic WF type-grammar parser, carrying the
-- `Gen` derivation. Classifier-routed (no per-token enumeration). Instantiated
-- for Type and PolyType. Plan 0.7 Phase 2.
------------------------------------------------------------------------

module Once.Parser.Generic.Parser where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; <-≤-trans; n≤1+n)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity; One; Zero; Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation


module Make (alg : TyAlg) where
  open TyAlg alg
  open Gen alg

  ParseAtomGD ParseProdGD ParseSumGD ParseTypeGD : List Token → Set
  ParseAtomGD toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesAtomG toks T rest)
  ParseProdGD toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesProdG toks T rest)
  ParseSumGD  toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesSumG toks T rest)
  ParseTypeGD toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesTypeG toks T rest)
  ParseProdTailGD ParseSumTailGD ParseArrowTailGD : R → List Token → Set
  ParseProdTailGD l toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesProdTailG l toks T rest)
  ParseSumTailGD  l toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesSumTailG l toks T rest)
  ParseArrowTailGD l toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] ParsesArrowTailG l toks T rest)
  ParseFAtomGD ParseFProdGD ParseFSumGD : List Token → Set
  ParseFAtomGD toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] ParsesFuncAtomG toks F rest)
  ParseFProdGD toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] ParsesFuncProdG toks F rest)
  ParseFSumGD  toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] ParsesFuncSumG toks F rest)
  ParseFProdTailGD ParseFSumTailGD : RF → List Token → Set
  ParseFProdTailGD l toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] ParsesFuncProdTailG l toks F rest)
  ParseFSumTailGD  l toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] ParsesFuncSumTailG l toks F rest)

  atomWF      : (toks : List Token) → Acc _<_ (length toks) → ParseAtomGD toks
  prodWF      : (toks : List Token) → Acc _<_ (length toks) → ParseProdGD toks
  prodTailWF  : (l : R) (toks : List Token) → Acc _<_ (length toks) → ParseProdTailGD l toks
  sumWF       : (toks : List Token) → Acc _<_ (length toks) → ParseSumGD toks
  sumTailWF   : (l : R) (toks : List Token) → Acc _<_ (length toks) → ParseSumTailGD l toks
  typeWF      : (toks : List Token) → Acc _<_ (length toks) → ParseTypeGD toks
  arrowTailWF : (l : R) (toks : List Token) → Acc _<_ (length toks) → ParseArrowTailGD l toks
  fAtomWF     : (toks : List Token) → Acc _<_ (length toks) → ParseFAtomGD toks
  fProdWF     : (toks : List Token) → Acc _<_ (length toks) → ParseFProdGD toks
  fProdTailWF : (l : RF) (toks : List Token) → Acc _<_ (length toks) → ParseFProdTailGD l toks
  fSumWF      : (toks : List Token) → Acc _<_ (length toks) → ParseFSumGD toks
  fSumTailWF  : (l : RF) (toks : List Token) → Acc _<_ (length toks) → ParseFSumTailGD l toks
  atomExtra   : (toks : List Token) →
                Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest) → ParseAtomGD toks
  parenFin    : (rest : List Token) → ParseTypeGD rest → ParseAtomGD (TLParen ∷ rest)
  arrowA      : (l : R) (toks : List Token) → arrowDir toks ≡ adA → ParseTypeGD (drop1 toks) → ParseArrowTailGD l toks
  arrowG      : (l : R) (toks : List Token) (q : Quantity) → arrowDir toks ≡ adG q → ParseTypeGD (drop2 toks) → ParseArrowTailGD l toks
  fAtomK      : (rest : List Token) → ParseAtomGD rest → ParseFAtomGD (TWord "K" ∷ rest)

  -- atom
  atomWF (TWord name ∷ rest) (acc rec) with name ≟s "Unit"
  ... | yes refl = just (aUnit , rest , pa-unit rest)
  ... | no _ with name ≟s "Void"
  ...   | yes refl = just (aVoid , rest , pa-void rest)
  ...   | no _ with name ≟s "Int"
  ...     | yes refl = just (aInt , rest , pa-int rest)
  ...     | no _ with name ≟s "Float"
  ...       | yes refl = just (aFloat , rest , pa-float rest)
  ...       | no _ with name ≟s "Buffer"
  ...         | yes refl = just (aBuffer , rest , pa-buffer rest)
  ...         | no _ with name ≟s "String"
  ...           | yes refl = just (aStr , rest , pa-string rest)
  ...           | no _ with name ≟s "Eff"
  ...             | yes refl with atomWF rest (rec (s≤s ≤-refl))
  ...               | nothing = nothing
  ...               | just (A , r1 , dA) with atomWF r1 (rec (<-trans (atomShrink dA) (s≤s ≤-refl)))
  ...                 | nothing = nothing
  ...                 | just (B , r2 , dB) = just (aEff A B , r2 , pa-eff dA dB)
  atomWF (TWord name ∷ rest) (acc rec)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "IO"
  ... | yes refl with atomWF rest (rec (s≤s ≤-refl))
  ...   | nothing = nothing
  ...   | just (A , r1 , dA) = just (aEff aUnit A , r1 , pa-io dA)
  atomWF (TWord name ∷ rest) (acc rec)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Mu"
  ... | yes refl with fSumWF rest (rec (s≤s ≤-refl))
  ...   | nothing = nothing
  ...   | just (F , r1 , dF) = just (aMu F , r1 , pa-mu dF)
  atomWF (TWord name ∷ rest) (acc rec)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ =
      atomExtra (TWord name ∷ rest) (extraP (TWord name ∷ rest))
  atomWF (TLParen ∷ rest) (acc rec) = parenFin rest (typeWF rest (rec (s≤s ≤-refl)))
  atomWF toks (acc rec) = atomExtra toks (extraP toks)

  atomExtra toks (just (a , rest , ex)) = just (a , rest , pa-extra ex)
  atomExtra toks nothing                = nothing

  parenFin rest (just (T , TRParen ∷ rest2 , dT)) = just (T , rest2 , pa-paren dT refl)
  parenFin rest (just (_ , _ , _))                = nothing
  parenFin rest nothing                           = nothing

  fAtomK rest (just (A , r1 , dA)) = just (fK A , r1 , pfa-k dA)
  fAtomK rest nothing              = nothing

  -- prod
  prodWF toks (acc rec) with atomWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , dA) with prodTailWF A r1 (rec (atomShrink dA))
  ...   | nothing = nothing
  ...   | just (T , r2 , dT) = just (T , r2 , pp-mk dA dT)

  prodTailWF l toks (acc rec) with isStar toks in eq
  ... | false = just (l , toks , ppt-done eq)
  ... | true with atomWF (drop1 toks) (rec (isStar-< toks eq))
  ...   | nothing = nothing
  ...   | just (B , r2 , dB) with prodTailWF (aProd l B) r2 (rec (<-≤-trans (atomShrink dB) (drop1-≤ toks)))
  ...     | nothing = nothing
  ...     | just (T , r3 , dT) = just (T , r3 , ppt-star eq dB dT)

  -- sum
  sumWF toks (acc rec) with prodWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , dA) with sumTailWF A r1 (rec (prodShrink dA))
  ...   | nothing = nothing
  ...   | just (T , r2 , dT) = just (T , r2 , ps-mk dA dT)

  sumTailWF l toks (acc rec) with isPlus toks in eq
  ... | false = just (l , toks , pst-done eq)
  ... | true with prodWF (drop1 toks) (rec (isPlus-< toks eq))
  ...   | nothing = nothing
  ...   | just (B , r2 , dB) with sumTailWF (aSum l B) r2 (rec (<-≤-trans (prodShrink dB) (drop1-≤ toks)))
  ...     | nothing = nothing
  ...     | just (T , r3 , dT) = just (T , r3 , pst-plus eq dB dT)

  -- type
  typeWF toks (acc rec) with sumWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , dA) with arrowTailWF A r1 (rec (sumShrink dA))
  ...   | nothing = nothing
  ...   | just (T , r2 , dT) = just (T , r2 , pt-mk dA dT)

  arrowTailWF l toks (acc rec) with arrowDir toks in eq
  ... | adD   = just (l , toks , pat-done eq)
  ... | adR   = nothing
  ... | adA   = arrowA l toks eq (typeWF (drop1 toks) (rec (arrowDir-A-< toks eq)))
  ... | adG q = arrowG l toks q eq (typeWF (drop2 toks) (rec (arrowDir-G-< toks eq)))

  arrowA l toks eq (just (B , r , dT)) = just (aArrow Many l B , r , pat-arrow eq dT)
  arrowA l toks eq nothing             = nothing
  arrowG l toks q eq (just (B , r , dT)) = just (aArrow q l B , r , pat-arrow-g eq dT)
  arrowG l toks q eq nothing             = nothing

  -- functor sub-grammar
  fAtomWF (TWord name ∷ rest) (acc rec) with name ≟s "Id"
  ... | yes refl = just (fId , rest , pfa-id rest)
  ... | no _ with name ≟s "K"
  ...   | yes refl = fAtomK rest (atomWF rest (rec (s≤s ≤-refl)))
  ...   | no _ = nothing
  fAtomWF (TLParen ∷ rest) (acc rec) = fParenFin rest (fSumWF rest (rec (s≤s ≤-refl)))
    where
      fParenFin : (rest' : List Token) → ParseFSumGD rest' → ParseFAtomGD (TLParen ∷ rest')
      fParenFin rest' (just (F , TRParen ∷ rest2 , dF)) = just (F , rest2 , pfa-paren dF refl)
      fParenFin rest' (just (_ , _ , _))                = nothing
      fParenFin rest' nothing                           = nothing
  fAtomWF toks (acc rec) = nothing

  fProdWF toks (acc rec) with fAtomWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , dA) with fProdTailWF A r1 (rec (funcAtomShrink dA))
  ...   | nothing = nothing
  ...   | just (F , r2 , dT) = just (F , r2 , pfp-mk dA dT)

  fProdTailWF l toks (acc rec) with isStar toks in eq
  ... | false = just (l , toks , pfpt-done eq)
  ... | true with fAtomWF (drop1 toks) (rec (isStar-< toks eq))
  ...   | nothing = nothing
  ...   | just (B , r2 , dB) with fProdTailWF (fProd l B) r2 (rec (<-≤-trans (funcAtomShrink dB) (drop1-≤ toks)))
  ...     | nothing = nothing
  ...     | just (F , r3 , dT) = just (F , r3 , pfpt-star eq dB dT)

  fSumWF toks (acc rec) with fProdWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , dA) with fSumTailWF A r1 (rec (funcProdShrink dA))
  ...   | nothing = nothing
  ...   | just (F , r2 , dT) = just (F , r2 , pfs-mk dA dT)

  fSumTailWF l toks (acc rec) with isPlus toks in eq
  ... | false = just (l , toks , pfst-done eq)
  ... | true with fProdWF (drop1 toks) (rec (isPlus-< toks eq))
  ...   | nothing = nothing
  ...   | just (B , r2 , dB) with fSumTailWF (fSum l B) r2 (rec (<-≤-trans (funcProdShrink dB) (drop1-≤ toks)))
  ...     | nothing = nothing
  ...     | just (F , r3 , dT) = just (F , r3 , pfst-plus eq dB dT)

