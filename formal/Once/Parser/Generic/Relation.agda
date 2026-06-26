-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Generic.Relation
--
-- The type-grammar parsing relation, parameterised over a `TyAlg` (AST builders)
-- + an extra-atom hook. One structure for both ground `Type` (extra = none) and
-- `PolyType` (extra = lowercase TVar). Tails use Bool/enum CLASSIFIER premises
-- (`isStar`/`isPlus`/`arrowDir`) + `drop1`/`drop2` bodies, so the parser routes
-- (no per-token enumeration) and the bridge proofs reduce. `Mu` reads a functor
-- SUM (the polynomial-functor fixpoint denotation; see Plan 0.7 Phase 2).
------------------------------------------------------------------------

module Once.Parser.Generic.Relation where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; m≤n⇒m≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Quantity; Zero; One; Many)
open import Once.Parser.Token

------------------------------------------------------------------------
-- Head classifiers + drops.
------------------------------------------------------------------------

isStar : List Token → Bool
isStar (TStar ∷ _) = true
isStar _           = false

isPlus : List Token → Bool
isPlus (TPlus ∷ _) = true
isPlus _           = false

data ArrowDir : Set where
  adG : Quantity → ArrowDir   -- grade + arrow (consume 2)
  adA : ArrowDir              -- plain arrow (consume 1)
  adR : ArrowDir              -- grade without arrow: reject
  adD : ArrowDir              -- done (no arrow tail)

arrowDir : List Token → ArrowDir
arrowDir (TCaret1 ∷ TArrow ∷ _) = adG One
arrowDir (TCaret0 ∷ TArrow ∷ _) = adG Zero
arrowDir (TCaretW ∷ TArrow ∷ _) = adG Many
arrowDir (TArrow ∷ _)           = adA
arrowDir (TCaret1 ∷ _)          = adR
arrowDir (TCaret0 ∷ _)          = adR
arrowDir (TCaretW ∷ _)          = adR
arrowDir _                      = adD

drop1 : List Token → List Token
drop1 []       = []
drop1 (_ ∷ xs) = xs

drop1-≤ : (xs : List Token) → length (drop1 xs) ≤ length xs
drop1-≤ []       = ≤-refl
drop1-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl

drop2 : List Token → List Token
drop2 (_ ∷ _ ∷ xs) = xs
drop2 xs           = xs

drop2-≤ : (xs : List Token) → length (drop2 xs) ≤ length xs
drop2-≤ (_ ∷ _ ∷ xs) = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
drop2-≤ []           = ≤-refl
drop2-≤ (_ ∷ [])     = ≤-refl

------------------------------------------------------------------------
-- The algebra.
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
    -- executable extra-atom parser (only fires when the keyword chain fails)
    extraP : (toks : List Token) → Maybe (Σ[ a ∈ R ] Σ[ rest ∈ List Token ] Extra toks a rest)

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
      ppt-done : ∀ {l toks} → isStar toks ≡ false → ParsesProdTailG l toks l toks
      ppt-star : ∀ {l toks toks2 rest} {B T : R} → isStar toks ≡ true
               → ParsesAtomG (drop1 toks) B toks2 → ParsesProdTailG (aProd l B) toks2 T rest
               → ParsesProdTailG l toks T rest

    data ParsesSumG : List Token → R → List Token → Set where
      ps-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesProdG toks A toks1 → ParsesSumTailG A toks1 T rest → ParsesSumG toks T rest

    data ParsesSumTailG : R → List Token → R → List Token → Set where
      pst-done : ∀ {l toks} → isPlus toks ≡ false → ParsesSumTailG l toks l toks
      pst-plus : ∀ {l toks toks2 rest} {B T : R} → isPlus toks ≡ true
               → ParsesProdG (drop1 toks) B toks2 → ParsesSumTailG (aSum l B) toks2 T rest
               → ParsesSumTailG l toks T rest

    data ParsesTypeG : List Token → R → List Token → Set where
      pt-mk : ∀ {toks toks1 rest} {A T : R}
            → ParsesSumG toks A toks1 → ParsesArrowTailG A toks1 T rest → ParsesTypeG toks T rest

    data ParsesArrowTailG : R → List Token → R → List Token → Set where
      pat-done : ∀ {l toks} → arrowDir toks ≡ adD → ParsesArrowTailG l toks l toks
      pat-arrow-g : ∀ {l toks rest} {B : R} {q : Quantity} → arrowDir toks ≡ adG q
                  → ParsesTypeG (drop2 toks) B rest → ParsesArrowTailG l toks (aArrow q l B) rest
      pat-arrow : ∀ {l toks rest} {B : R} → arrowDir toks ≡ adA
                → ParsesTypeG (drop1 toks) B rest → ParsesArrowTailG l toks (aArrow Many l B) rest

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
      pfpt-done : ∀ {l toks} → isStar toks ≡ false → ParsesFuncProdTailG l toks l toks
      pfpt-star : ∀ {l toks toks2 rest} {B F : RF} → isStar toks ≡ true
                → ParsesFuncAtomG (drop1 toks) B toks2 → ParsesFuncProdTailG (fProd l B) toks2 F rest
                → ParsesFuncProdTailG l toks F rest

    data ParsesFuncSumG : List Token → RF → List Token → Set where
      pfs-mk : ∀ {toks toks1 rest} {A F : RF}
             → ParsesFuncProdG toks A toks1 → ParsesFuncSumTailG A toks1 F rest → ParsesFuncSumG toks F rest

    data ParsesFuncSumTailG : RF → List Token → RF → List Token → Set where
      pfst-done : ∀ {l toks} → isPlus toks ≡ false → ParsesFuncSumTailG l toks l toks
      pfst-plus : ∀ {l toks toks2 rest} {B F : RF} → isPlus toks ≡ true
                → ParsesFuncProdG (drop1 toks) B toks2 → ParsesFuncSumTailG (fSum l B) toks2 F rest
                → ParsesFuncSumTailG l toks F rest

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
    prodTailShrink {toks = toks} (ppt-star _ dB dT) =
      <⇒≤ (≤-<-trans (prodTailShrink dT) (<-≤-trans (atomShrink dB) (drop1-≤ toks)))

    sumShrink : ∀ {toks T rest} → ParsesSumG toks T rest → length rest < length toks
    sumShrink (ps-mk dA dT) = ≤-<-trans (sumTailShrink dT) (prodShrink dA)

    sumTailShrink : ∀ {l toks T rest} → ParsesSumTailG l toks T rest → length rest ≤ length toks
    sumTailShrink (pst-done _) = ≤-refl
    sumTailShrink {toks = toks} (pst-plus _ dB dT) =
      <⇒≤ (≤-<-trans (sumTailShrink dT) (<-≤-trans (prodShrink dB) (drop1-≤ toks)))

    arrowTailShrink : ∀ {l toks T rest} → ParsesArrowTailG l toks T rest → length rest ≤ length toks
    arrowTailShrink (pat-done _) = ≤-refl
    arrowTailShrink {toks = toks} (pat-arrow-g _ dT) = <⇒≤ (<-≤-trans (typeShrink dT) (drop2-≤ toks))
    arrowTailShrink {toks = toks} (pat-arrow _ dT) = <⇒≤ (<-≤-trans (typeShrink dT) (drop1-≤ toks))

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
    funcProdTailShrink {toks = toks} (pfpt-star _ dB dT) =
      <⇒≤ (≤-<-trans (funcProdTailShrink dT) (<-≤-trans (funcAtomShrink dB) (drop1-≤ toks)))

    funcSumShrink : ∀ {toks F rest} → ParsesFuncSumG toks F rest → length rest < length toks
    funcSumShrink (pfs-mk dA dT) = ≤-<-trans (funcSumTailShrink dT) (funcProdShrink dA)

    funcSumTailShrink : ∀ {l toks F rest} → ParsesFuncSumTailG l toks F rest → length rest ≤ length toks
    funcSumTailShrink (pfst-done _) = ≤-refl
    funcSumTailShrink {toks = toks} (pfst-plus _ dB dT) =
      <⇒≤ (≤-<-trans (funcSumTailShrink dT) (<-≤-trans (funcProdShrink dB) (drop1-≤ toks)))
