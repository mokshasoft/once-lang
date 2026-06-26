-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Generic.Relation
--
-- The type-grammar parsing relation, parameterised over a `TyAlg` (the AST
-- builders) + an extra-atom hook. One generic structure, instantiated for both
-- ground `Type` (extra = none) and `PolyType` (extra = lowercase TVar). Mirrors
-- the precedence levels of `Once.Parser.Type` (atom → prod → sum → type + tails
-- + functor sub-grammar). `Mu` reads a functor SUM (the principled denotation:
-- the fixpoint of a polynomial functor, a sum-of-products).
------------------------------------------------------------------------

module Once.Parser.Generic.Relation where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity; Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.TypeRelation using (NotStar; NotStarPlus; NotArrowOrGrade; quantityTokenOf)

------------------------------------------------------------------------
-- The algebra: result sorts `R` (types) and `RF` (functors) + builders +
-- the extra-atom hook (`Extra` relation + its shrink).
------------------------------------------------------------------------

record TyAlg : Set₁ where
  field
    R RF : Set
    aUnit aVoid aInt aFloat aBuffer aStr : R
    aProd aSum aEff : R → R → R
    aArrow : Quantity → R → R → R
    aMu : RF → R
    fK : R → RF
    fId : RF
    fSum fProd : RF → RF → RF
    Extra : List Token → R → List Token → Set
    extraShrink : ∀ {toks a rest} → Extra toks a rest → length rest < length toks

module Gen (alg : TyAlg) where
  open TyAlg alg

  mutual
    data ParsesAtomG : List Token → R → List Token → Set where
      pa-unit   : ∀ rest → ParsesAtomG (TWord "Unit"   ∷ rest) aUnit   rest
      pa-void   : ∀ rest → ParsesAtomG (TWord "Void"   ∷ rest) aVoid   rest
      pa-int    : ∀ rest → ParsesAtomG (TWord "Int"    ∷ rest) aInt    rest
      pa-float  : ∀ rest → ParsesAtomG (TWord "Float"  ∷ rest) aFloat  rest
      pa-buffer : ∀ rest → ParsesAtomG (TWord "Buffer" ∷ rest) aBuffer rest
      pa-string : ∀ rest → ParsesAtomG (TWord "String" ∷ rest) aStr    rest
      pa-eff : ∀ {toks1 toks2 rest} {A B : R}
             → ParsesAtomG toks1 A toks2 → ParsesAtomG toks2 B rest
             → ParsesAtomG (TWord "Eff" ∷ toks1) (aEff A B) rest
      pa-io : ∀ {toks1 rest} {A : R}
            → ParsesAtomG toks1 A rest → ParsesAtomG (TWord "IO" ∷ toks1) (aEff aUnit A) rest
      pa-mu : ∀ {toks rest} {F : RF}
            → ParsesFuncSumG toks F rest → ParsesAtomG (TWord "Mu" ∷ toks) (aMu F) rest
      pa-extra : ∀ {toks a rest} → Extra toks a rest → ParsesAtomG toks a rest
      pa-paren : ∀ {toks rest1 rest2} {T : R}
               → ParsesTypeG toks T rest1 → rest1 ≡ TRParen ∷ rest2
               → ParsesAtomG (TLParen ∷ toks) T rest2

    data ParsesProdG : List Token → R → List Token → Set where
      pp-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesAtomG toks A toks1 → ParsesProdTailG A toks1 T rest → ParsesProdG toks T rest

    data ParsesProdTailG : R → List Token → R → List Token → Set where
      ppt-done : ∀ {l toks} → NotStar toks → ParsesProdTailG l toks l toks
      ppt-star : ∀ {l toks1 toks2 rest} {B T : R}
               → ParsesAtomG toks1 B toks2 → ParsesProdTailG (aProd l B) toks2 T rest
               → ParsesProdTailG l (TStar ∷ toks1) T rest

    data ParsesSumG : List Token → R → List Token → Set where
      ps-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesProdG toks A toks1 → ParsesSumTailG A toks1 T rest → ParsesSumG toks T rest

    data ParsesSumTailG : R → List Token → R → List Token → Set where
      pst-done : ∀ {l toks} → NotStarPlus toks → ParsesSumTailG l toks l toks
      pst-plus : ∀ {l toks1 toks2 rest} {B T : R}
               → ParsesProdG toks1 B toks2 → ParsesSumTailG (aSum l B) toks2 T rest
               → ParsesSumTailG l (TPlus ∷ toks1) T rest

    data ParsesTypeG : List Token → R → List Token → Set where
      pt-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesSumG toks A toks1 → ParsesArrowTailG A toks1 T rest → ParsesTypeG toks T rest

    data ParsesArrowTailG : R → List Token → R → List Token → Set where
      pat-done : ∀ {l toks} → NotArrowOrGrade toks → ParsesArrowTailG l toks l toks
      pat-arrow-g : ∀ {l toks rest} {B : R} {q : Quantity}
                  → ParsesTypeG toks B rest
                  → ParsesArrowTailG l (quantityTokenOf q ∷ TArrow ∷ toks) (aArrow q l B) rest
      pat-arrow : ∀ {l toks rest} {B : R}
                → ParsesTypeG toks B rest → ParsesArrowTailG l (TArrow ∷ toks) (aArrow Many l B) rest

    data ParsesFuncAtomG : List Token → RF → List Token → Set where
      pfa-id : ∀ rest → ParsesFuncAtomG (TWord "Id" ∷ rest) fId rest
      pfa-k  : ∀ {toks rest} {A : R}
             → ParsesAtomG toks A rest → ParsesFuncAtomG (TWord "K" ∷ toks) (fK A) rest
      pfa-paren : ∀ {toks rest1 rest2} {F : RF}
                → ParsesFuncSumG toks F rest1 → rest1 ≡ TRParen ∷ rest2
                → ParsesFuncAtomG (TLParen ∷ toks) F rest2

    data ParsesFuncProdG : List Token → RF → List Token → Set where
      pfp-mk : ∀ {toks toks1 rest} {A F : RF}
             → ParsesFuncAtomG toks A toks1 → ParsesFuncProdTailG A toks1 F rest → ParsesFuncProdG toks F rest

    data ParsesFuncProdTailG : RF → List Token → RF → List Token → Set where
      pfpt-done : ∀ {l toks} → NotStar toks → ParsesFuncProdTailG l toks l toks
      pfpt-star : ∀ {l toks1 toks2 rest} {B F : RF}
                → ParsesFuncAtomG toks1 B toks2 → ParsesFuncProdTailG (fProd l B) toks2 F rest
                → ParsesFuncProdTailG l (TStar ∷ toks1) F rest

    data ParsesFuncSumG : List Token → RF → List Token → Set where
      pfs-mk : ∀ {toks toks1 rest} {A F : RF}
             → ParsesFuncProdG toks A toks1 → ParsesFuncSumTailG A toks1 F rest → ParsesFuncSumG toks F rest

    data ParsesFuncSumTailG : RF → List Token → RF → List Token → Set where
      pfst-done : ∀ {l toks} → NotStarPlus toks → ParsesFuncSumTailG l toks l toks
      pfst-plus : ∀ {l toks1 toks2 rest} {B F : RF}
                → ParsesFuncProdG toks1 B toks2 → ParsesFuncSumTailG (fSum l B) toks2 F rest
                → ParsesFuncSumTailG l (TPlus ∷ toks1) F rest

  ------------------------------------------------------------------------
  -- Shrinks.
  ------------------------------------------------------------------------
  mutual
    atomShrink : ∀ {toks T rest} → ParsesAtomG toks T rest → length rest < length toks
    atomShrink (pa-unit rest)   = s≤s ≤-refl
    atomShrink (pa-void rest)   = s≤s ≤-refl
    atomShrink (pa-int rest)    = s≤s ≤-refl
    atomShrink (pa-float rest)  = s≤s ≤-refl
    atomShrink (pa-buffer rest) = s≤s ≤-refl
    atomShrink (pa-string rest) = s≤s ≤-refl
    atomShrink (pa-eff dA dB) = <-trans (atomShrink dB) (<-trans (atomShrink dA) (s≤s ≤-refl))
    atomShrink (pa-io dA) = <-trans (atomShrink dA) (s≤s ≤-refl)
    atomShrink (pa-mu dF) = <-trans (funcSumShrink dF) (s≤s ≤-refl)
    atomShrink (pa-extra ex) = extraShrink ex
    atomShrink (pa-paren dT refl) = <-trans (s≤s ≤-refl) (<-trans (typeShrink dT) (s≤s ≤-refl))

    prodShrink : ∀ {toks T rest} → ParsesProdG toks T rest → length rest < length toks
    prodShrink (pp-mk dA dT) = ≤-<-trans (prodTailShrink dT) (atomShrink dA)

    prodTailShrink : ∀ {l toks T rest} → ParsesProdTailG l toks T rest → length rest ≤ length toks
    prodTailShrink (ppt-done _) = ≤-refl
    prodTailShrink (ppt-star dB dT) =
      <⇒≤ (≤-<-trans (prodTailShrink dT) (<-trans (atomShrink dB) (s≤s ≤-refl)))

    sumShrink : ∀ {toks T rest} → ParsesSumG toks T rest → length rest < length toks
    sumShrink (ps-mk dA dT) = ≤-<-trans (sumTailShrink dT) (prodShrink dA)

    sumTailShrink : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → length rest ≤ length toks
    sumTailShrink (pst-done _) = ≤-refl
    sumTailShrink (pst-plus dB dT) =
      <⇒≤ (≤-<-trans (sumTailShrink dT) (<-trans (prodShrink dB) (s≤s ≤-refl)))

    arrowTailShrink : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → length rest ≤ length toks
    arrowTailShrink (pat-done _) = ≤-refl
    arrowTailShrink (pat-arrow-g {q = Zero} dT) = <⇒≤ (<-trans (typeShrink dT) (s≤s (n≤1+n _)))
    arrowTailShrink (pat-arrow-g {q = One}  dT) = <⇒≤ (<-trans (typeShrink dT) (s≤s (n≤1+n _)))
    arrowTailShrink (pat-arrow-g {q = Many} dT) = <⇒≤ (<-trans (typeShrink dT) (s≤s (n≤1+n _)))
    arrowTailShrink (pat-arrow dT) = <⇒≤ (<-trans (typeShrink dT) (s≤s ≤-refl))

    typeShrink : ∀ {toks T rest} → ParsesTypeG toks T rest → length rest < length toks
    typeShrink (pt-mk dS dA) = ≤-<-trans (arrowTailShrink dA) (sumShrink dS)

    funcAtomShrink : ∀ {toks F rest} → ParsesFuncAtomG toks F rest → length rest < length toks
    funcAtomShrink (pfa-id rest) = s≤s ≤-refl
    funcAtomShrink (pfa-k dA) = <-trans (atomShrink dA) (s≤s ≤-refl)
    funcAtomShrink (pfa-paren dF refl) = <-trans (s≤s ≤-refl) (<-trans (funcSumShrink dF) (s≤s ≤-refl))

    funcProdShrink : ∀ {toks F rest} → ParsesFuncProdG toks F rest → length rest < length toks
    funcProdShrink (pfp-mk dA dT) = ≤-<-trans (funcProdTailShrink dT) (funcAtomShrink dA)

    funcProdTailShrink : ∀ {l toks F rest} → ParsesFuncProdTailG l toks F rest → length rest ≤ length toks
    funcProdTailShrink (pfpt-done _) = ≤-refl
    funcProdTailShrink (pfpt-star dB dT) =
      <⇒≤ (≤-<-trans (funcProdTailShrink dT) (<-trans (funcAtomShrink dB) (s≤s ≤-refl)))

    funcSumShrink : ∀ {toks F rest} → ParsesFuncSumG toks F rest → length rest < length toks
    funcSumShrink (pfs-mk dA dT) = ≤-<-trans (funcSumTailShrink dT) (funcProdShrink dA)

    funcSumTailShrink : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → length rest ≤ length toks
    funcSumTailShrink (pfst-done _) = ≤-refl
    funcSumTailShrink (pfst-plus dB dT) =
      <⇒≤ (≤-<-trans (funcSumTailShrink dT) (<-trans (funcProdShrink dB) (s≤s ≤-refl)))
