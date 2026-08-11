-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Generic.Sound — generic soundness: whatever the bound-free parser
-- accepts is in the relation. WF on token length; the recursion Accs use the
-- relation's `atomShrink`/classifier strict-bound lemmas applied to the already-
-- returned sub-derivation. Mirrors the parser clause-for-clause. Plan 0.7-2.
------------------------------------------------------------------------

module Once.Parser.Generic.Sound where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl; <-trans; <-≤-trans)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation
import Once.Parser.Generic.Parser as P

module Make (alg : TyAlg) where
  open TyAlg alg
  open Gen alg
  open P.Make alg

  mutual
    {-# TERMINATING #-}
    sound-atom : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      atomP toks ≡ just (T , rest) → ParsesAtomG toks T rest
    sound-atom toks (acc rec) h with extraP toks in eq
    ... | just (a , r , ex) with refl ← just-injective h = pa-extra ex
    ... | nothing = sound-kw toks (acc rec) h

    {-# TERMINATING #-}
    sound-kw : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      atomKw toks ≡ just (T , rest) → ParsesAtomG toks T rest
    sound-kw (TWord name ∷ rest) (acc rec) h with name ≟s "Unit"
    ... | yes refl with refl ← just-injective h = pa-unit rest
    ... | no _ with name ≟s "Void"
    ...   | yes refl with refl ← just-injective h = pa-void rest
    ...   | no _ with name ≟s "Int"
    ...     | yes refl with refl ← just-injective h = pa-int rest
    ...     | no _ with name ≟s "Float"
    ...       | yes refl with refl ← just-injective h = pa-float rest
    ...       | no _ with name ≟s "Buffer"
    ...         | yes refl with refl ← just-injective h = pa-buffer rest
    ...         | no _ with name ≟s "String"
    ...           | yes refl with refl ← just-injective h = pa-string rest
    ...           | no _ with name ≟s "Eff"
    ...             | yes refl with atomP rest in eq1
    ...               | just (A , r1) with sound-atom rest (rec (s≤s ≤-refl)) eq1
    ...                 | dA with atomP r1 in eq2
    ...                   | just (B , r2) with sound-atom r1 (rec (<-trans (atomShrink dA) (s≤s ≤-refl))) eq2
    ...                     | dB with refl ← just-injective h = pa-eff dA dB
    sound-kw (TWord name ∷ rest) (acc rec) h
      | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "IO"
    ... | yes refl with atomP rest in eq1
    ...   | just (A , r1) with sound-atom rest (rec (s≤s ≤-refl)) eq1
    ...     | dA with refl ← just-injective h = pa-io dA
    sound-kw (TWord name ∷ rest) (acc rec) h
      | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Mu"
    ... | yes refl with fSumP rest in eq1
    ...   | just (F , r1) with sound-fSum rest (rec (s≤s ≤-refl)) eq1
    ...     | dF with refl ← just-injective h = pa-mu dF
    sound-kw (TLParen ∷ rest) (acc rec) h with typeP rest in eq1
    ... | just (T , TRParen ∷ rest2) with sound-type rest (rec (s≤s ≤-refl)) eq1
    ...   | dT with refl ← just-injective h = pa-paren dT refl

    {-# TERMINATING #-}
    sound-prod : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      prodP toks ≡ just (T , rest) → ParsesProdG toks T rest
    sound-prod toks (acc rec) h with atomP toks in eq1
    ... | just (A , r1) with sound-atom toks (acc rec) eq1
    ...   | dA = pp-mk dA (sound-prodTail A r1 (rec (atomShrink dA)) h)

    {-# TERMINATING #-}
    sound-prodTail : ∀ (l : R) (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      prodTailP l toks ≡ just (T , rest) → ParsesProdTailG l toks T rest
    sound-prodTail l toks (acc rec) h with isStar toks in eq
    ... | false with refl ← just-injective h = ppt-done eq
    ... | true with atomP (drop1 toks) in eq2
    ...   | just (B , r2) with sound-atom (drop1 toks) (rec (isStar-< toks eq)) eq2
    ...     | dB = ppt-star eq dB
                     (sound-prodTail (aProd l B) r2
                       (rec (<-≤-trans (atomShrink dB) (drop1-≤ toks))) h)

    {-# TERMINATING #-}
    sound-sum : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      sumP toks ≡ just (T , rest) → ParsesSumG toks T rest
    sound-sum toks (acc rec) h with prodP toks in eq1
    ... | just (A , r1) with sound-prod toks (acc rec) eq1
    ...   | dA = ps-mk dA (sound-sumTail A r1 (rec (prodShrink dA)) h)

    {-# TERMINATING #-}
    sound-sumTail : ∀ (l : R) (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      sumTailP l toks ≡ just (T , rest) → ParsesSumTailG l toks T rest
    sound-sumTail l toks (acc rec) h with isPlus toks in eq
    ... | false with refl ← just-injective h = pst-done eq
    ... | true with prodP (drop1 toks) in eq2
    ...   | just (B , r2) with sound-prod (drop1 toks) (rec (isPlus-< toks eq)) eq2
    ...     | dB = pst-plus eq dB
                     (sound-sumTail (aSum l B) r2
                       (rec (<-≤-trans (prodShrink dB) (drop1-≤ toks))) h)

    {-# TERMINATING #-}
    sound-type : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      typeP toks ≡ just (T , rest) → ParsesTypeG toks T rest
    sound-type toks (acc rec) h with sumP toks in eq1
    ... | just (A , r1) with sound-sum toks (acc rec) eq1
    ...   | dA = pt-mk dA (sound-arrowTail A r1 (rec (sumShrink dA)) h)

    {-# TERMINATING #-}
    sound-arrowTail : ∀ (l : R) (toks : List Token) (a : Acc _<_ (length toks)) {T rest} →
      arrowTailP l toks ≡ just (T , rest) → ParsesArrowTailG l toks T rest
    sound-arrowTail l toks (acc rec) h with arrowDir toks in eq
    ... | adD with refl ← just-injective h = pat-done eq
    ... | adR with () ← h
    ... | adA with typeP (drop1 toks) in eq2
    ...   | just (B , r) with sound-type (drop1 toks) (rec (arrowDir-A-< toks eq)) eq2
    ...     | dB with refl ← just-injective h = pat-arrow eq dB
    sound-arrowTail l toks (acc rec) h | adG q with typeP (drop2 toks) in eq2
    ... | just (B , r) with sound-type (drop2 toks) (rec (arrowDir-G-< toks eq)) eq2
    ...   | dB with refl ← just-injective h = pat-arrow-g eq dB

    {-# TERMINATING #-}
    sound-fAtom : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {F rest} →
      fAtomP toks ≡ just (F , rest) → ParsesFuncAtomG toks F rest
    sound-fAtom (TWord name ∷ rest) (acc rec) h with name ≟s "Id" | name ≟s "K"
    ... | yes refl | _ with refl ← just-injective h = pfa-id rest
    ... | no _ | yes refl with atomP rest in eq1
    ...   | just (A , r1) with sound-atom rest (rec (s≤s ≤-refl)) eq1
    ...     | dA with refl ← just-injective h = pfa-k dA
    sound-fAtom (TLParen ∷ rest) (acc rec) h with fSumP rest in eq1
    ... | just (F , TRParen ∷ rest2) with sound-fSum rest (rec (s≤s ≤-refl)) eq1
    ...   | dF with refl ← just-injective h = pfa-paren dF refl

    {-# TERMINATING #-}
    sound-fProd : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {F rest} →
      fProdP toks ≡ just (F , rest) → ParsesFuncProdG toks F rest
    sound-fProd toks (acc rec) h with fAtomP toks in eq1
    ... | just (A , r1) with sound-fAtom toks (acc rec) eq1
    ...   | dA = pfp-mk dA (sound-fProdTail A r1 (rec (funcAtomShrink dA)) h)

    {-# TERMINATING #-}
    sound-fProdTail : ∀ (l : RF) (toks : List Token) (a : Acc _<_ (length toks)) {F rest} →
      fProdTailP l toks ≡ just (F , rest) → ParsesFuncProdTailG l toks F rest
    sound-fProdTail l toks (acc rec) h with isStar toks in eq
    ... | false with refl ← just-injective h = pfpt-done eq
    ... | true with fAtomP (drop1 toks) in eq2
    ...   | just (B , r2) with sound-fAtom (drop1 toks) (rec (isStar-< toks eq)) eq2
    ...     | dB = pfpt-star eq dB
                     (sound-fProdTail (fProd l B) r2
                       (rec (<-≤-trans (funcAtomShrink dB) (drop1-≤ toks))) h)

    {-# TERMINATING #-}
    sound-fSum : ∀ (toks : List Token) (a : Acc _<_ (length toks)) {F rest} →
      fSumP toks ≡ just (F , rest) → ParsesFuncSumG toks F rest
    sound-fSum toks (acc rec) h with fProdP toks in eq1
    ... | just (A , r1) with sound-fProd toks (acc rec) eq1
    ...   | dA = pfs-mk dA (sound-fSumTail A r1 (rec (funcProdShrink dA)) h)

    {-# TERMINATING #-}
    sound-fSumTail : ∀ (l : RF) (toks : List Token) (a : Acc _<_ (length toks)) {F rest} →
      fSumTailP l toks ≡ just (F , rest) → ParsesFuncSumTailG l toks F rest
    sound-fSumTail l toks (acc rec) h with isPlus toks in eq
    ... | false with refl ← just-injective h = pfst-done eq
    ... | true with fProdP (drop1 toks) in eq2
    ...   | just (B , r2) with sound-fProd (drop1 toks) (rec (isPlus-< toks eq)) eq2
    ...     | dB = pfst-plus eq dB
                     (sound-fSumTail (fSum l B) r2
                       (rec (<-≤-trans (funcProdShrink dB) (drop1-≤ toks))) h)
