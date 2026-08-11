-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Parser — generic type-grammar parser, TERMINATING and
-- BOUND-FREE (returns just `T × rest`, like the existing `parsePolyType`). The
-- length bound is recovered separately via the relation's `shrinks`. With no
-- bound in the parser there is no bound-dependency, so `with`/`rewrite` abstract
-- the classifier cleanly — soundness and completeness both reduce. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Parser.Generic.Parser where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Type using (Quantity; One; Zero; Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation

module Make (alg : TyAlg) where
  open TyAlg alg

  {-# TERMINATING #-}
  atomP prodP sumP typeP : List Token → Maybe (R × List Token)
  prodTailP sumTailP arrowTailP : R → List Token → Maybe (R × List Token)
  fAtomP fProdP fSumP : List Token → Maybe (RF × List Token)
  fProdTailP fSumTailP : RF → List Token → Maybe (RF × List Token)
  atomKw : List Token → Maybe (R × List Token)

  atomP toks with extraP toks
  ... | just (a , rest , _) = just (a , rest)
  ... | nothing = atomKw toks
  atomKw (TWord name ∷ rest) with name ≟s "Unit"
  ... | yes refl = just (aUnit , rest)
  ... | no _ with name ≟s "Void"
  ...   | yes refl = just (aVoid , rest)
  ...   | no _ with name ≟s "Int"
  ...     | yes refl = just (aInt , rest)
  ...     | no _ with name ≟s "Float"
  ...       | yes refl = just (aFloat , rest)
  ...       | no _ with name ≟s "Buffer"
  ...         | yes refl = just (aBuffer , rest)
  ...         | no _ with name ≟s "String"
  ...           | yes refl = just (aStr , rest)
  ...           | no _ with name ≟s "Eff"
  ...             | yes refl with atomP rest
  ...               | nothing = nothing
  ...               | just (A , r1) with atomP r1
  ...                 | nothing = nothing
  ...                 | just (B , r2) = just (aEff A B , r2)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "IO"
  ... | yes refl with atomP rest
  ...   | nothing = nothing
  ...   | just (A , r1) = just (aEff aUnit A , r1)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Mu"
  ... | yes refl with fSumP rest
  ...   | nothing = nothing
  ...   | just (F , r1) = just (aMu F , r1)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = nothing
  atomKw (TLParen ∷ rest) with typeP rest
  ... | just (T , TRParen ∷ rest2) = just (T , rest2)
  ... | just (_ , _) = nothing
  ... | nothing = nothing
  atomKw _ = nothing

  prodP toks with atomP toks
  ... | nothing = nothing
  ... | just (A , r1) = prodTailP A r1
  prodTailP l toks = ptGo l toks (isStar toks)
    where
      ptGo : R → List Token → Bool → Maybe (R × List Token)
      ptGo l toks false = just (l , toks)
      ptGo l toks true with atomP (drop1 toks)
      ... | nothing = nothing
      ... | just (B , r2) = prodTailP (aProd l B) r2

  sumP toks with prodP toks
  ... | nothing = nothing
  ... | just (A , r1) = sumTailP A r1
  sumTailP l toks = stGo l toks (isPlus toks)
    where
      stGo : R → List Token → Bool → Maybe (R × List Token)
      stGo l toks false = just (l , toks)
      stGo l toks true with prodP (drop1 toks)
      ... | nothing = nothing
      ... | just (B , r2) = sumTailP (aSum l B) r2

  typeP toks with sumP toks
  ... | nothing = nothing
  ... | just (A , r1) = arrowTailP A r1
  arrowTailP l toks = atGo l toks (arrowDir toks)
    where
      atGo : R → List Token → ArrowDir → Maybe (R × List Token)
      atGo l toks adD = just (l , toks)
      atGo l toks adR = nothing
      atGo l toks adA with typeP (drop1 toks)
      ... | nothing = nothing
      ... | just (B , r) = just (aArrow Many l B , r)
      atGo l toks (adG q) with typeP (drop2 toks)
      ... | nothing = nothing
      ... | just (B , r) = just (aArrow q l B , r)

  fAtomP (TWord name ∷ rest) with name ≟s "Id" | name ≟s "K"
  ... | yes refl | _ = just (fId , rest)
  ... | no _ | yes refl with atomP rest
  ...   | nothing = nothing
  ...   | just (A , r1) = just (fK A , r1)
  fAtomP (TWord name ∷ rest) | no _ | no _ = nothing
  fAtomP (TLParen ∷ rest) with fSumP rest
  ... | just (F , TRParen ∷ rest2) = just (F , rest2)
  ... | just (_ , _) = nothing
  ... | nothing = nothing
  fAtomP _ = nothing

  fProdP toks with fAtomP toks
  ... | nothing = nothing
  ... | just (A , r1) = fProdTailP A r1
  fProdTailP l toks = fptGo l toks (isStar toks)
    where
      fptGo : RF → List Token → Bool → Maybe (RF × List Token)
      fptGo l toks false = just (l , toks)
      fptGo l toks true with fAtomP (drop1 toks)
      ... | nothing = nothing
      ... | just (B , r2) = fProdTailP (fProd l B) r2

  fSumP toks with fProdP toks
  ... | nothing = nothing
  ... | just (A , r1) = fSumTailP A r1
  fSumTailP l toks = fstGo l toks (isPlus toks)
    where
      fstGo : RF → List Token → Bool → Maybe (RF × List Token)
      fstGo l toks false = just (l , toks)
      fstGo l toks true with fProdP (drop1 toks)
      ... | nothing = nothing
      ... | just (B , r2) = fSumTailP (fSum l B) r2
