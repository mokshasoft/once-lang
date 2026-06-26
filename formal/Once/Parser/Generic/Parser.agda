-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Generic.Parser — the generic WF type-grammar parser, EXECUTABLE
-- (returns the length bound). Classifier-routed; the tail helpers take the
-- classifier VALUE + the bound as a FUNCTION of the eq (`λ e → isStar-< toks e`)
-- — never a self-referential `refl` — so soundness (`with classifier in eq`) and
-- completeness (`rewrite premise`) both reduce. Plan 0.7 Phase 2.
------------------------------------------------------------------------

module Once.Parser.Generic.Parser where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-≤-trans; ≤-<-trans; <⇒≤; n≤1+n)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity; One; Zero; Many)
open import Once.Parser.Token
open import Once.Parser.Generic.Relation

module Make (alg : TyAlg) where
  open TyAlg alg

  AtomD : List Token → Set
  AtomD toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] length rest < length toks)
  ProdD SumD TypeD : List Token → Set
  ProdD = AtomD
  SumD  = AtomD
  TypeD = AtomD
  ProdTailD : R → List Token → Set
  ProdTailD  l toks = Maybe (Σ[ T ∈ R ] Σ[ rest ∈ List Token ] length rest ≤ length toks)
  SumTailD ArrowTailD : R → List Token → Set
  SumTailD   = ProdTailD
  ArrowTailD = ProdTailD
  FAtomD : List Token → Set
  FAtomD toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] length rest < length toks)
  FProdD FSumD : List Token → Set
  FProdD = FAtomD
  FSumD  = FAtomD
  FProdTailD : RF → List Token → Set
  FProdTailD l toks = Maybe (Σ[ F ∈ RF ] Σ[ rest ∈ List Token ] length rest ≤ length toks)
  FSumTailD : RF → List Token → Set
  FSumTailD = FProdTailD

  atomWF      : (toks : List Token) → Acc _<_ (length toks) → AtomD toks
  prodWF      : (toks : List Token) → Acc _<_ (length toks) → ProdD toks
  prodTailWF  : (l : R) (toks : List Token) → Acc _<_ (length toks) → ProdTailD l toks
  sumWF       : (toks : List Token) → Acc _<_ (length toks) → SumD toks
  sumTailWF   : (l : R) (toks : List Token) → Acc _<_ (length toks) → SumTailD l toks
  typeWF      : (toks : List Token) → Acc _<_ (length toks) → TypeD toks
  arrowTailWF : (l : R) (toks : List Token) → Acc _<_ (length toks) → ArrowTailD l toks
  fAtomWF     : (toks : List Token) → Acc _<_ (length toks) → FAtomD toks
  fProdWF     : (toks : List Token) → Acc _<_ (length toks) → FProdD toks
  fProdTailWF : (l : RF) (toks : List Token) → Acc _<_ (length toks) → FProdTailD l toks
  fSumWF      : (toks : List Token) → Acc _<_ (length toks) → FSumD toks
  fSumTailWF  : (l : RF) (toks : List Token) → Acc _<_ (length toks) → FSumTailD l toks
  atomGo      : (toks : List Token) → (∀ {y} → y < length toks → Acc _<_ y) →
                Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest) → AtomD toks
  atomKw      : (toks : List Token) → (∀ {y} → y < length toks → Acc _<_ y) → AtomD toks
  parenFin    : (rest : List Token) → TypeD rest → AtomD (TLParen ∷ rest)
  arrowA      : (l : R) (toks : List Token) → TypeD (drop1 toks) → ArrowTailD l toks
  arrowG      : (l : R) (toks : List Token) (q : Quantity) → TypeD (drop2 toks) → ArrowTailD l toks
  fAtomK      : (rest : List Token) → AtomD rest → FAtomD (TWord "K" ∷ rest)
  ptGo  : (l : R) (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → ProdTailD l toks
  stGo  : (l : R) (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → SumTailD l toks
  atGo  : (l : R) (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (d : ArrowDir) → (d ≡ adA → length (drop1 toks) < length toks)
          → (∀ {q} → d ≡ adG q → length (drop2 toks) < length toks) → ArrowTailD l toks
  fptGo : (l : RF) (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → FProdTailD l toks
  fstGo : (l : RF) (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
          (b : Bool) → (b ≡ true → length (drop1 toks) < length toks) → FSumTailD l toks

  atomWF toks (acc rec) = atomGo toks rec (extraP toks)
  atomGo toks rec (just (a , rest , ex)) = just (a , rest , extraShrink ex)
  atomGo toks rec nothing                = atomKw toks rec

  atomKw (TWord name ∷ rest) rec with name ≟s "Unit"
  ... | yes refl = just (aUnit , rest , s≤s ≤-refl)
  ... | no _ with name ≟s "Void"
  ...   | yes refl = just (aVoid , rest , s≤s ≤-refl)
  ...   | no _ with name ≟s "Int"
  ...     | yes refl = just (aInt , rest , s≤s ≤-refl)
  ...     | no _ with name ≟s "Float"
  ...       | yes refl = just (aFloat , rest , s≤s ≤-refl)
  ...       | no _ with name ≟s "Buffer"
  ...         | yes refl = just (aBuffer , rest , s≤s ≤-refl)
  ...         | no _ with name ≟s "String"
  ...           | yes refl = just (aStr , rest , s≤s ≤-refl)
  ...           | no _ with name ≟s "Eff"
  ...             | yes refl with atomWF rest (rec (s≤s ≤-refl))
  ...               | nothing = nothing
  ...               | just (A , r1 , bA) with atomWF r1 (rec (<-trans bA (s≤s ≤-refl)))
  ...                 | nothing = nothing
  ...                 | just (B , r2 , bB) = just (aEff A B , r2 , <-trans bB (<-trans bA (s≤s ≤-refl)))
  atomKw (TWord name ∷ rest) rec
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "IO"
  ... | yes refl with atomWF rest (rec (s≤s ≤-refl))
  ...   | nothing = nothing
  ...   | just (A , r1 , bA) = just (aEff aUnit A , r1 , <-trans bA (s≤s ≤-refl))
  atomKw (TWord name ∷ rest) rec
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟s "Mu"
  ... | yes refl with fSumWF rest (rec (s≤s ≤-refl))
  ...   | nothing = nothing
  ...   | just (F , r1 , bF) = just (aMu F , r1 , <-trans bF (s≤s ≤-refl))
  atomKw (TWord name ∷ rest) rec
    | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = nothing
  atomKw (TLParen ∷ rest) rec = parenFin rest (typeWF rest (rec (s≤s ≤-refl)))
  atomKw toks rec = nothing

  parenFin rest (just (T , TRParen ∷ rest2 , bT)) =
    just (T , rest2 , <-trans (s≤s ≤-refl) (<-trans bT (s≤s ≤-refl)))
  parenFin rest (just (_ , _ , _))                = nothing
  parenFin rest nothing                           = nothing

  fAtomK rest (just (A , r1 , bA)) = just (fK A , r1 , <-trans bA (s≤s ≤-refl))
  fAtomK rest nothing              = nothing

  prodWF toks (acc rec) with atomWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , bA) with prodTailWF A r1 (rec bA)
  ...   | nothing = nothing
  ...   | just (T , r2 , bT) = just (T , r2 , ≤-<-trans bT bA)

  prodTailWF l toks (acc rec) = ptGo l toks rec (isStar toks) (isStar-< toks)
  ptGo l toks rec false bnd = just (l , toks , ≤-refl)
  ptGo l toks rec true bnd with atomWF (drop1 toks) (rec (bnd refl))
  ... | nothing = nothing
  ... | just (B , r2 , bB) with prodTailWF (aProd l B) r2 (rec (<-≤-trans bB (drop1-≤ toks)))
  ...   | nothing = nothing
  ...   | just (T , r3 , bT) = just (T , r3 , ≤-trans bT (≤-trans (<⇒≤ bB) (drop1-≤ toks)))

  sumWF toks (acc rec) with prodWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , bA) with sumTailWF A r1 (rec bA)
  ...   | nothing = nothing
  ...   | just (T , r2 , bT) = just (T , r2 , ≤-<-trans bT bA)

  sumTailWF l toks (acc rec) = stGo l toks rec (isPlus toks) (isPlus-< toks)
  stGo l toks rec false bnd = just (l , toks , ≤-refl)
  stGo l toks rec true bnd with prodWF (drop1 toks) (rec (bnd refl))
  ... | nothing = nothing
  ... | just (B , r2 , bB) with sumTailWF (aSum l B) r2 (rec (<-≤-trans bB (drop1-≤ toks)))
  ...   | nothing = nothing
  ...   | just (T , r3 , bT) = just (T , r3 , ≤-trans bT (≤-trans (<⇒≤ bB) (drop1-≤ toks)))

  typeWF toks (acc rec) with sumWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , bA) with arrowTailWF A r1 (rec bA)
  ...   | nothing = nothing
  ...   | just (T , r2 , bT) = just (T , r2 , ≤-<-trans bT bA)

  arrowTailWF l toks (acc rec) = atGo l toks rec (arrowDir toks) (arrowDir-A-< toks) (arrowDir-G-< toks)
  atGo l toks rec adD     bndA bndG = just (l , toks , ≤-refl)
  atGo l toks rec adR     bndA bndG = nothing
  atGo l toks rec adA     bndA bndG = arrowA l toks (typeWF (drop1 toks) (rec (bndA refl)))
  atGo l toks rec (adG q) bndA bndG = arrowG l toks q (typeWF (drop2 toks) (rec (bndG refl)))

  arrowA l toks (just (B , r , bT)) = just (aArrow Many l B , r , <⇒≤ (<-≤-trans bT (drop1-≤ toks)))
  arrowA l toks nothing             = nothing
  arrowG l toks q (just (B , r , bT)) = just (aArrow q l B , r , <⇒≤ (<-≤-trans bT (drop2-≤ toks)))
  arrowG l toks q nothing             = nothing

  fAtomWF (TWord name ∷ rest) (acc rec) with name ≟s "Id"
  ... | yes refl = just (fId , rest , s≤s ≤-refl)
  ... | no _ with name ≟s "K"
  ...   | yes refl = fAtomK rest (atomWF rest (rec (s≤s ≤-refl)))
  ...   | no _ = nothing
  fAtomWF (TLParen ∷ rest) (acc rec) = fParenFin rest (fSumWF rest (rec (s≤s ≤-refl)))
    where
      fParenFin : (rest' : List Token) → FSumD rest' → FAtomD (TLParen ∷ rest')
      fParenFin rest' (just (F , TRParen ∷ rest2 , bF)) =
        just (F , rest2 , <-trans (s≤s ≤-refl) (<-trans bF (s≤s ≤-refl)))
      fParenFin rest' (just (_ , _ , _))                = nothing
      fParenFin rest' nothing                           = nothing
  fAtomWF toks (acc rec) = nothing

  fProdWF toks (acc rec) with fAtomWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , bA) with fProdTailWF A r1 (rec bA)
  ...   | nothing = nothing
  ...   | just (F , r2 , bT) = just (F , r2 , ≤-<-trans bT bA)

  fProdTailWF l toks (acc rec) = fptGo l toks rec (isStar toks) (isStar-< toks)
  fptGo l toks rec false bnd = just (l , toks , ≤-refl)
  fptGo l toks rec true bnd with fAtomWF (drop1 toks) (rec (bnd refl))
  ... | nothing = nothing
  ... | just (B , r2 , bB) with fProdTailWF (fProd l B) r2 (rec (<-≤-trans bB (drop1-≤ toks)))
  ...   | nothing = nothing
  ...   | just (F , r3 , bT) = just (F , r3 , ≤-trans bT (≤-trans (<⇒≤ bB) (drop1-≤ toks)))

  fSumWF toks (acc rec) with fProdWF toks (acc rec)
  ... | nothing = nothing
  ... | just (A , r1 , bA) with fSumTailWF A r1 (rec bA)
  ...   | nothing = nothing
  ...   | just (F , r2 , bT) = just (F , r2 , ≤-<-trans bT bA)

  fSumTailWF l toks (acc rec) = fstGo l toks rec (isPlus toks) (isPlus-< toks)
  fstGo l toks rec false bnd = just (l , toks , ≤-refl)
  fstGo l toks rec true bnd with fProdWF (drop1 toks) (rec (bnd refl))
  ... | nothing = nothing
  ... | just (B , r2 , bB) with fSumTailWF (fSum l B) r2 (rec (<-≤-trans bB (drop1-≤ toks)))
  ...   | nothing = nothing
  ...   | just (F , r3 , bT) = just (F , r3 , ≤-trans bT (≤-trans (<⇒≤ bB) (drop1-≤ toks)))
