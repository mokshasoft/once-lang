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
open import Data.List using (List; _∷_)
open import Data.String using () renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation

-- D233: does the token stream start `( Eff`? The equation is what lets the
-- soundness proof recover the shape without enumerating tokens.
effHead? : (rest : List Token) → Maybe (Σ[ r ∈ List Token ] rest ≡ TLParen ∷ TWord "Eff" ∷ r)
effHead? (TLParen ∷ TWord w ∷ r) with w ≟s "Eff"
... | yes refl = just (r , refl)
... | no _     = nothing
{-# CATCHALL #-}
effHead? _ = nothing

module Make (alg : TyAlg) where
  open TyAlg alg

  {-# TERMINATING #-}
  atomP prodP sumP typeP : List Token → Maybe (R × List Token)
  prodTailP sumTailP arrowTailP : R → List Token → Maybe (R × List Token)
  fAtomP fProdP fSumP : List Token → Maybe (RF × List Token)
  fProdTailP fSumTailP : RF → List Token → Maybe (RF × List Token)
  atomKw : List Token → Maybe (R × List Token)
  -- D233: `Nu` — the pure stream first; `( Eff F )` exactly when that fails
  -- (a functor never starts with `( Eff`).
  nuP nuEffP : List Token → Maybe (R × List Token)
  nuTryP : List Token → Maybe (RF × List Token) → Maybe (R × List Token)
  nuCloseP : Maybe (RF × List Token) → Maybe (R × List Token)
  nuEffWith : (rest : List Token) → Maybe (Σ[ r ∈ List Token ] rest ≡ TLParen ∷ TWord "Eff" ∷ r)
            → Maybe (R × List Token)

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
  ...       | no _ with name ≟s "Eff"
  ...         | yes refl with atomP rest
  ...           | nothing = nothing
  ...           | just (A , r1) with atomP r1
  ...             | nothing = nothing
  ...             | just (B , r2) = just (aEff A B , r2)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ with name ≟s "IO"
  ... | yes refl with atomP rest
  ...   | nothing = nothing
  ...   | just (A , r1) = just (aEff aUnit A , r1)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Mu"
  ... | yes refl with fSumP rest
  ...   | nothing = nothing
  ...   | just (F , r1) = just (aMu F , r1)
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Nu"
  ... | yes refl = nuP rest
  atomKw (TWord name ∷ rest)
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = nothing
  atomKw (TLParen ∷ rest) with typeP rest
  ... | just (T , TRParen ∷ rest2) = just (T , rest2)
  {-# CATCHALL #-}
  ... | just (_ , _) = nothing
  ... | nothing = nothing
  {-# CATCHALL #-}
  atomKw _ = nothing

  nuP rest = nuTryP rest (fSumP rest)
  nuTryP rest (just (F , r1)) = just (aNu F , r1)
  nuTryP rest nothing         = nuEffP rest
  nuEffP rest = nuEffWith rest (effHead? rest)
  nuCloseP (just (F , TRParen ∷ r2)) = just (aNuEff F , r2)
  {-# CATCHALL #-}
  nuCloseP (just (F , _))            = nothing
  nuCloseP nothing                   = nothing

  nuEffWith rest nothing = nothing
  nuEffWith .(TLParen ∷ TWord "Eff" ∷ r) (just (r , refl)) = nuCloseP (fSumP r)

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
  {-# CATCHALL #-}
  ... | just (_ , _) = nothing
  ... | nothing = nothing
  {-# CATCHALL #-}
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
