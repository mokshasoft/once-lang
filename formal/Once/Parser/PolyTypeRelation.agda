-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.PolyTypeRelation
--
-- Inductive parsing relations for polymorphic types (`PolyType`, with
-- `PTVar`). Mirrors `Once.Parser.TypeRelation` (atom → prod → sum → type
-- + tails + functor sub-grammar), adding the `PTVar` atom (lowercase
-- identifier) and using `PolyType`'s grade-annotated arrow `_P⇒[_]_`.
-- Plan 0.52 / 0.7 Phase 2: the `ParsesPolyType` spec paralleling
-- `ParsesType`.
------------------------------------------------------------------------

module Once.Parser.PolyTypeRelation where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (PolyType; PUnit; PVoid; PInt; PFloat; PBuffer; PStr;
                             _P*_; _P+_; _P⇒[_]_; PEff; Pμ-type; PTVar;
                             PolyFunctor; PK; PId; _P⊕_; _P⊗_;
                             Quantity; Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.PolyType using (isLowerWord)
open import Once.Parser.TypeRelation using (NotStar; NotStarPlus; NotArrowOrGrade; quantityTokenOf)

------------------------------------------------------------------------
-- Parsing relations (mutual inductive, one per grammar level).
------------------------------------------------------------------------

mutual

  -- atom ::= 'Unit'|'Void'|'Int'|'Float'|'Buffer'|'String'
  --        | 'Eff' atom atom | 'IO' atom | 'Mu' fAtom
  --        | lower_ident | '(' polytype ')'
  data ParsesPolyAtom : List Token → PolyType → List Token → Set where
    pa-unit    : ∀ rest → ParsesPolyAtom (TWord "Unit"   ∷ rest) PUnit   rest
    pa-void    : ∀ rest → ParsesPolyAtom (TWord "Void"   ∷ rest) PVoid   rest
    pa-int     : ∀ rest → ParsesPolyAtom (TWord "Int"    ∷ rest) PInt    rest
    pa-float   : ∀ rest → ParsesPolyAtom (TWord "Float"  ∷ rest) PFloat  rest
    pa-buffer  : ∀ rest → ParsesPolyAtom (TWord "Buffer" ∷ rest) PBuffer rest
    pa-string  : ∀ rest → ParsesPolyAtom (TWord "String" ∷ rest) PStr    rest
    pa-eff : ∀ {toks1 toks2 rest} {A B : PolyType}
           → ParsesPolyAtom toks1 A toks2 → ParsesPolyAtom toks2 B rest
           → ParsesPolyAtom (TWord "Eff" ∷ toks1) (PEff A B) rest
    pa-io : ∀ {toks1 rest} {A : PolyType}
          → ParsesPolyAtom toks1 A rest
          → ParsesPolyAtom (TWord "IO" ∷ toks1) (PEff PUnit A) rest
    pa-mu : ∀ {toks rest} {F : PolyFunctor}
          → ParsesPolyFuncAtom toks F rest
          → ParsesPolyAtom (TWord "Mu" ∷ toks) (Pμ-type F) rest
    pa-tvar : ∀ {name rest} → isLowerWord name ≡ true
            → ParsesPolyAtom (TWord name ∷ rest) (PTVar name) rest
    pa-paren : ∀ {toks rest1 rest2} {T : PolyType}
             → ParsesPolyType toks T rest1 → rest1 ≡ TRParen ∷ rest2
             → ParsesPolyAtom (TLParen ∷ toks) T rest2

  data ParsesPolyProd : List Token → PolyType → List Token → Set where
    pp-mk : ∀ {toks toks1 rest} {A T : PolyType}
          → ParsesPolyAtom toks A toks1 → ParsesPolyProdTail A toks1 T rest
          → ParsesPolyProd toks T rest

  data ParsesPolyProdTail : PolyType → List Token → PolyType → List Token → Set where
    ppt-done : ∀ {left toks} → NotStar toks → ParsesPolyProdTail left toks left toks
    ppt-star : ∀ {left toks1 toks2 rest} {B T : PolyType}
             → ParsesPolyAtom toks1 B toks2 → ParsesPolyProdTail (left P* B) toks2 T rest
             → ParsesPolyProdTail left (TStar ∷ toks1) T rest

  data ParsesPolySum : List Token → PolyType → List Token → Set where
    ps-mk : ∀ {toks toks1 rest} {A T : PolyType}
          → ParsesPolyProd toks A toks1 → ParsesPolySumTail A toks1 T rest
          → ParsesPolySum toks T rest

  data ParsesPolySumTail : PolyType → List Token → PolyType → List Token → Set where
    pst-done : ∀ {left toks} → NotStarPlus toks → ParsesPolySumTail left toks left toks
    pst-plus : ∀ {left toks1 toks2 rest} {B T : PolyType}
             → ParsesPolyProd toks1 B toks2 → ParsesPolySumTail (left P+ B) toks2 T rest
             → ParsesPolySumTail left (TPlus ∷ toks1) T rest

  data ParsesPolyType : List Token → PolyType → List Token → Set where
    pt-mk : ∀ {toks toks1 rest} {A T : PolyType}
          → ParsesPolySum toks A toks1 → ParsesPolyArrowTail A toks1 T rest
          → ParsesPolyType toks T rest

  data ParsesPolyArrowTail : PolyType → List Token → PolyType → List Token → Set where
    pat-done : ∀ {left toks} → NotArrowOrGrade toks → ParsesPolyArrowTail left toks left toks
    pat-arrow-g : ∀ {left toks rest} {B : PolyType} {q : Quantity}
                → ParsesPolyType toks B rest
                → ParsesPolyArrowTail left (quantityTokenOf q ∷ TArrow ∷ toks) (left P⇒[ q ] B) rest
    pat-arrow : ∀ {left toks rest} {B : PolyType}
              → ParsesPolyType toks B rest
              → ParsesPolyArrowTail left (TArrow ∷ toks) (left P⇒[ Many ] B) rest

  -- Functor sub-grammar (body of `Mu`). `Mu` takes a single fAtom; `K`'s
  -- argument is a polytype ATOM.
  data ParsesPolyFuncAtom : List Token → PolyFunctor → List Token → Set where
    pfa-id : ∀ rest → ParsesPolyFuncAtom (TWord "Id" ∷ rest) PId rest
    pfa-k  : ∀ {toks rest} {A : PolyType}
           → ParsesPolyAtom toks A rest → ParsesPolyFuncAtom (TWord "K" ∷ toks) (PK A) rest
    pfa-paren : ∀ {toks rest1 rest2} {F : PolyFunctor}
              → ParsesPolyFuncSum toks F rest1 → rest1 ≡ TRParen ∷ rest2
              → ParsesPolyFuncAtom (TLParen ∷ toks) F rest2

  data ParsesPolyFuncProd : List Token → PolyFunctor → List Token → Set where
    pfp-mk : ∀ {toks toks1 rest} {A F : PolyFunctor}
           → ParsesPolyFuncAtom toks A toks1 → ParsesPolyFuncProdTail A toks1 F rest
           → ParsesPolyFuncProd toks F rest

  data ParsesPolyFuncProdTail : PolyFunctor → List Token → PolyFunctor → List Token → Set where
    pfpt-done : ∀ {left toks} → NotStar toks → ParsesPolyFuncProdTail left toks left toks
    pfpt-star : ∀ {left toks1 toks2 rest} {B F : PolyFunctor}
              → ParsesPolyFuncAtom toks1 B toks2 → ParsesPolyFuncProdTail (left P⊗ B) toks2 F rest
              → ParsesPolyFuncProdTail left (TStar ∷ toks1) F rest

  data ParsesPolyFuncSum : List Token → PolyFunctor → List Token → Set where
    pfs-mk : ∀ {toks toks1 rest} {A F : PolyFunctor}
           → ParsesPolyFuncProd toks A toks1 → ParsesPolyFuncSumTail A toks1 F rest
           → ParsesPolyFuncSum toks F rest

  data ParsesPolyFuncSumTail : PolyFunctor → List Token → PolyFunctor → List Token → Set where
    pfst-done : ∀ {left toks} → NotStarPlus toks → ParsesPolyFuncSumTail left toks left toks
    pfst-plus : ∀ {left toks1 toks2 rest} {B F : PolyFunctor}
              → ParsesPolyFuncProd toks1 B toks2 → ParsesPolyFuncSumTail (left P⊕ B) toks2 F rest
              → ParsesPolyFuncSumTail left (TPlus ∷ toks1) F rest

------------------------------------------------------------------------
-- Shrinks (mutual structural induction on derivations).
------------------------------------------------------------------------

mutual
  ParsesPolyAtom-shrinks : ∀ {toks T rest} → ParsesPolyAtom toks T rest → length rest < length toks
  ParsesPolyAtom-shrinks (pa-unit   rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-void   rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-int    rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-float  rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-buffer rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-string rest) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-eff dA dB) =
    <-trans (ParsesPolyAtom-shrinks dB) (<-trans (ParsesPolyAtom-shrinks dA) (s≤s ≤-refl))
  ParsesPolyAtom-shrinks (pa-io dA) = <-trans (ParsesPolyAtom-shrinks dA) (s≤s ≤-refl)
  ParsesPolyAtom-shrinks (pa-mu dF) = <-trans (ParsesPolyFuncAtom-shrinks dF) (s≤s ≤-refl)
  ParsesPolyAtom-shrinks (pa-tvar _) = s≤s ≤-refl
  ParsesPolyAtom-shrinks (pa-paren dT refl) =
    <-trans (s≤s ≤-refl) (<-trans (ParsesPolyType-shrinks dT) (s≤s ≤-refl))

  ParsesPolyProd-shrinks : ∀ {toks T rest} → ParsesPolyProd toks T rest → length rest < length toks
  ParsesPolyProd-shrinks (pp-mk dA dT) =
    ≤-<-trans (ParsesPolyProdTail-shrinks dT) (ParsesPolyAtom-shrinks dA)

  ParsesPolyProdTail-shrinks : ∀ {l toks T rest} → ParsesPolyProdTail l toks T rest → length rest ≤ length toks
  ParsesPolyProdTail-shrinks (ppt-done _) = ≤-refl
  ParsesPolyProdTail-shrinks (ppt-star dB dT) =
    <⇒≤ (≤-<-trans (ParsesPolyProdTail-shrinks dT) (<-trans (ParsesPolyAtom-shrinks dB) (s≤s ≤-refl)))

  ParsesPolySum-shrinks : ∀ {toks T rest} → ParsesPolySum toks T rest → length rest < length toks
  ParsesPolySum-shrinks (ps-mk dA dT) =
    ≤-<-trans (ParsesPolySumTail-shrinks dT) (ParsesPolyProd-shrinks dA)

  ParsesPolySumTail-shrinks : ∀ {l toks T rest} → ParsesPolySumTail l toks T rest → length rest ≤ length toks
  ParsesPolySumTail-shrinks (pst-done _) = ≤-refl
  ParsesPolySumTail-shrinks (pst-plus dB dT) =
    <⇒≤ (≤-<-trans (ParsesPolySumTail-shrinks dT) (<-trans (ParsesPolyProd-shrinks dB) (s≤s ≤-refl)))

  ParsesPolyArrowTail-shrinks : ∀ {l toks T rest} → ParsesPolyArrowTail l toks T rest → length rest ≤ length toks
  ParsesPolyArrowTail-shrinks (pat-done _) = ≤-refl
  ParsesPolyArrowTail-shrinks (pat-arrow-g {q = Zero} dT) = <⇒≤ (<-trans (ParsesPolyType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesPolyArrowTail-shrinks (pat-arrow-g {q = One}  dT) = <⇒≤ (<-trans (ParsesPolyType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesPolyArrowTail-shrinks (pat-arrow-g {q = Many} dT) = <⇒≤ (<-trans (ParsesPolyType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesPolyArrowTail-shrinks (pat-arrow dT) = <⇒≤ (<-trans (ParsesPolyType-shrinks dT) (s≤s ≤-refl))

  ParsesPolyType-shrinks : ∀ {toks T rest} → ParsesPolyType toks T rest → length rest < length toks
  ParsesPolyType-shrinks (pt-mk dS dA) =
    ≤-<-trans (ParsesPolyArrowTail-shrinks dA) (ParsesPolySum-shrinks dS)

  ParsesPolyFuncAtom-shrinks : ∀ {toks F rest} → ParsesPolyFuncAtom toks F rest → length rest < length toks
  ParsesPolyFuncAtom-shrinks (pfa-id rest) = s≤s ≤-refl
  ParsesPolyFuncAtom-shrinks (pfa-k dA) = <-trans (ParsesPolyAtom-shrinks dA) (s≤s ≤-refl)
  ParsesPolyFuncAtom-shrinks (pfa-paren dF refl) =
    <-trans (s≤s ≤-refl) (<-trans (ParsesPolyFuncSum-shrinks dF) (s≤s ≤-refl))

  ParsesPolyFuncProd-shrinks : ∀ {toks F rest} → ParsesPolyFuncProd toks F rest → length rest < length toks
  ParsesPolyFuncProd-shrinks (pfp-mk dA dT) =
    ≤-<-trans (ParsesPolyFuncProdTail-shrinks dT) (ParsesPolyFuncAtom-shrinks dA)

  ParsesPolyFuncProdTail-shrinks : ∀ {l toks F rest} → ParsesPolyFuncProdTail l toks F rest → length rest ≤ length toks
  ParsesPolyFuncProdTail-shrinks (pfpt-done _) = ≤-refl
  ParsesPolyFuncProdTail-shrinks (pfpt-star dB dT) =
    <⇒≤ (≤-<-trans (ParsesPolyFuncProdTail-shrinks dT) (<-trans (ParsesPolyFuncAtom-shrinks dB) (s≤s ≤-refl)))

  ParsesPolyFuncSum-shrinks : ∀ {toks F rest} → ParsesPolyFuncSum toks F rest → length rest < length toks
  ParsesPolyFuncSum-shrinks (pfs-mk dA dT) =
    ≤-<-trans (ParsesPolyFuncSumTail-shrinks dT) (ParsesPolyFuncProd-shrinks dA)

  ParsesPolyFuncSumTail-shrinks : ∀ {l toks F rest} → ParsesPolyFuncSumTail l toks F rest → length rest ≤ length toks
  ParsesPolyFuncSumTail-shrinks (pfst-done _) = ≤-refl
  ParsesPolyFuncSumTail-shrinks (pfst-plus dB dT) =
    <⇒≤ (≤-<-trans (ParsesPolyFuncSumTail-shrinks dT) (<-trans (ParsesPolyFuncProd-shrinks dB) (s≤s ≤-refl)))
