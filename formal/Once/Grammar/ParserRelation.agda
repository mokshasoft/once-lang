-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ParserRelation
--
-- Inductive parsing relations for Once types. Mirrors the precedence
-- structure of `Once.Parser.Type`'s mutual parsers (atom → prod → sum
-- → type) but as a set of inference rules instead of a recursive
-- function.
--
-- `ParsesX toks T rest` reads: "starting from token list `toks`, the
-- X-level parser produces type `T` and leaves residual tokens `rest`".
--
-- Why a relation (plan 0.3, task #40 redesign):
--   * Downstream proofs (`Roundtrip`, `ParserInvariant`) become
--     structural induction on derivations instead of equational
--     reasoning over opaque WF-parser reductions.
--   * The one-time bridge `ParsesType ↔ parseType` (soundness +
--     completeness) is proved once in `ParserCorrect`, isolating the
--     Acc-irrelevance / function-reduction reasoning.
------------------------------------------------------------------------

module Once.Grammar.ParserRelation where

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Eff; Quantity; Zero; One; Many)
open import Once.Parser.Token

import Once.Grammar as G
open G using (GType)
open import Once.Grammar.Printer using (Concrete;
                                        c-unit; c-void; c-int; c-float;
                                        c-buffer; c-string; c-prod; c-sum;
                                        c-fun; c-eff)

-- | Convert a concrete GType to its internal Type. Shared between the
-- relational and function-based round-trip modules.
toType : ∀ {g : GType} → Concrete g → Type
toType c-unit   = Unit
toType c-void   = Void
toType c-int    = Int
toType c-float  = Float
toType c-buffer = Buffer
toType c-string = Str
toType (c-prod cA cB) = toType cA * toType cB
toType (c-sum  cA cB) = toType cA + toType cB
toType (c-fun {q = q} cA cB) = toType cA ⇒[ q ] toType cB
toType (c-eff  cA cB) = Eff (toType cA) (toType cB)

------------------------------------------------------------------------
-- Predicate: these tokens STOP a prod/sum/arrow tail. Mirrors the
-- `NotStar` / `NotStarPlus` / `NotCont` predicates in `Roundtrip`.
------------------------------------------------------------------------

-- True if `toks` does not start with `TStar` — the only token that
-- triggers a product-tail continuation.
NotStar : List Token → Set
NotStar [] = Data.Unit.⊤ where open import Data.Unit
NotStar (TStar ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotStar (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- True if `toks` does not start with `TPlus` — the token that triggers
-- a sum-tail continuation. (TStar is admitted; lower-level prod-tail
-- handled it before sum-tail was called.)
NotStarPlus : List Token → Set
NotStarPlus [] = Data.Unit.⊤ where open import Data.Unit
NotStarPlus (TPlus ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotStarPlus (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- True if `toks` does not start with a token that arrow-tail consumes
-- (`TArrow`) or begins to consume (`TCaret0/1/W`). TStar/TPlus admitted.
NotArrowOrGrade : List Token → Set
NotArrowOrGrade [] = Data.Unit.⊤ where open import Data.Unit
NotArrowOrGrade (TArrow  ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaret0 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaret1 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaretW ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- All-clean: rejects every token that any tail-parser would consume.
-- The user-facing round-trip premise: the trailing tokens don't look
-- like a type continuation at any precedence level.
NotCont : List Token → Set
NotCont [] = Data.Unit.⊤ where open import Data.Unit
NotCont (TStar   ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (TPlus   ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (TArrow  ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (TCaret0 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (TCaret1 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (TCaretW ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotCont (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

------------------------------------------------------------------------
-- Parsing relations (mutual inductive, one per grammar level)
------------------------------------------------------------------------

mutual

  -- atom ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
  --        | 'Eff' atom atom | 'IO' atom
  --        | '(' type ')'
  data ParsesAtom : List Token → Type → List Token → Set where

    pa-unit    : ∀ rest → ParsesAtom (TWord "Unit"   ∷ rest) Unit   rest
    pa-void    : ∀ rest → ParsesAtom (TWord "Void"   ∷ rest) Void   rest
    pa-int     : ∀ rest → ParsesAtom (TWord "Int"    ∷ rest) Int    rest
    pa-float   : ∀ rest → ParsesAtom (TWord "Float"  ∷ rest) Float  rest
    pa-buffer  : ∀ rest → ParsesAtom (TWord "Buffer" ∷ rest) Buffer rest
    pa-string  : ∀ rest → ParsesAtom (TWord "String" ∷ rest) Str    rest

    -- Eff A B
    pa-eff : ∀ {toks1 toks2 rest} {A B : Type}
           → ParsesAtom toks1 A toks2
           → ParsesAtom toks2 B rest
           → ParsesAtom (TWord "Eff" ∷ toks1) (Eff A B) rest

    -- IO A  desugars to  Eff Unit A
    pa-io : ∀ {toks1 rest} {A : Type}
          → ParsesAtom toks1 A rest
          → ParsesAtom (TWord "IO" ∷ toks1) (Eff Unit A) rest

    -- `( type )`
    pa-paren : ∀ {toks rest1 rest2} {T : Type}
             → ParsesType toks T rest1
             → rest1 ≡ TRParen ∷ rest2
             → ParsesAtom (TLParen ∷ toks) T rest2

  -- prod ::= atom ('*' atom)*
  data ParsesProd : List Token → Type → List Token → Set where
    pp-mk : ∀ {toks toks1 rest} {A T : Type}
          → ParsesAtom toks A toks1
          → ParsesProdTail A toks1 T rest
          → ParsesProd toks T rest

  -- prodTail[left] ::= '*' atom prodTail[left*right] | ε
  data ParsesProdTail : Type → List Token → Type → List Token → Set where
    ppt-done : ∀ {left toks} → NotStar toks → ParsesProdTail left toks left toks
    ppt-star : ∀ {left toks1 toks2 rest} {B T : Type}
             → ParsesAtom toks1 B toks2
             → ParsesProdTail (left * B) toks2 T rest
             → ParsesProdTail left (TStar ∷ toks1) T rest

  -- sum ::= prod ('+' prod)*
  data ParsesSum : List Token → Type → List Token → Set where
    ps-mk : ∀ {toks toks1 rest} {A T : Type}
          → ParsesProd toks A toks1
          → ParsesSumTail A toks1 T rest
          → ParsesSum toks T rest

  -- sumTail[left] ::= '+' prod sumTail[left+right] | ε
  data ParsesSumTail : Type → List Token → Type → List Token → Set where
    pst-done : ∀ {left toks} → NotStarPlus toks → ParsesSumTail left toks left toks
    pst-plus : ∀ {left toks1 toks2 rest} {B T : Type}
             → ParsesProd toks1 B toks2
             → ParsesSumTail (left + B) toks2 T rest
             → ParsesSumTail left (TPlus ∷ toks1) T rest

  -- type ::= sum (grade? '->' type)?
  data ParsesType : List Token → Type → List Token → Set where
    pt-mk : ∀ {toks toks1 rest} {A T : Type}
          → ParsesSum toks A toks1
          → ParsesArrowTail A toks1 T rest
          → ParsesType toks T rest

  -- arrowTail[left] ::= ε | '^q' '->' type | '->' type
  data ParsesArrowTail : Type → List Token → Type → List Token → Set where
    pat-done : ∀ {left toks} → NotArrowOrGrade toks → ParsesArrowTail left toks left toks
    -- Grade-annotated arrow
    pat-arrow-g : ∀ {left toks rest} {B : Type} {q : Quantity}
                → ParsesType toks B rest
                → ParsesArrowTail left
                    (quantityTokenOf q ∷ TArrow ∷ toks)
                    (left ⇒[ q ] B) rest
    -- Plain arrow defaults to Many
    pat-arrow : ∀ {left toks rest} {B : Type}
              → ParsesType toks B rest
              → ParsesArrowTail left (TArrow ∷ toks) (left ⇒[ Many ] B) rest

  -- Token for a grade annotation. Mirrors `quantityToken` in Printer.
  quantityTokenOf : Quantity → Token
  quantityTokenOf Zero = TCaret0
  quantityTokenOf One  = TCaret1
  quantityTokenOf Many = TCaretW

------------------------------------------------------------------------
-- Shrinks lemmas: every successful derivation leaves a strictly
-- smaller (or ≤) residual. Pure structural induction on derivations,
-- no parser machinery involved. Used by the parser itself (see
-- `Once.Parser.Type`) to construct the Acc arguments of its recursive
-- sub-calls, and by soundness proofs downstream.
------------------------------------------------------------------------

open import Data.List using (length)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤;
                                        n≤1+n)

mutual

  ParsesAtom-shrinks :
    ∀ {toks T rest} → ParsesAtom toks T rest → length rest < length toks
  ParsesAtom-shrinks (pa-unit   rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-void   rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-int    rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-float  rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-buffer rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-string rest) = s≤s ≤-refl
  ParsesAtom-shrinks (pa-eff dA dB) =
    <-trans (ParsesAtom-shrinks dB)
            (<-trans (ParsesAtom-shrinks dA) (s≤s ≤-refl))
  ParsesAtom-shrinks (pa-io dA) =
    <-trans (ParsesAtom-shrinks dA) (s≤s ≤-refl)
  ParsesAtom-shrinks (pa-paren dT refl) =
    <-trans (s≤s ≤-refl)
            (<-trans (ParsesType-shrinks dT) (s≤s ≤-refl))

  ParsesProd-shrinks :
    ∀ {toks T rest} → ParsesProd toks T rest → length rest < length toks
  ParsesProd-shrinks (pp-mk dA dTail) =
    ≤-<-trans (ParsesProdTail-shrinks dTail) (ParsesAtom-shrinks dA)

  ParsesProdTail-shrinks :
    ∀ {left toks T rest} → ParsesProdTail left toks T rest
    → length rest ≤ length toks
  ParsesProdTail-shrinks (ppt-done _) = ≤-refl
  ParsesProdTail-shrinks (ppt-star dB dTail) =
    <⇒≤ (≤-<-trans (ParsesProdTail-shrinks dTail)
                   (<-trans (ParsesAtom-shrinks dB) (s≤s ≤-refl)))

  ParsesSum-shrinks :
    ∀ {toks T rest} → ParsesSum toks T rest → length rest < length toks
  ParsesSum-shrinks (ps-mk dA dTail) =
    ≤-<-trans (ParsesSumTail-shrinks dTail) (ParsesProd-shrinks dA)

  ParsesSumTail-shrinks :
    ∀ {left toks T rest} → ParsesSumTail left toks T rest
    → length rest ≤ length toks
  ParsesSumTail-shrinks (pst-done _) = ≤-refl
  ParsesSumTail-shrinks (pst-plus dB dTail) =
    <⇒≤ (≤-<-trans (ParsesSumTail-shrinks dTail)
                   (<-trans (ParsesProd-shrinks dB) (s≤s ≤-refl)))

  ParsesArrowTail-shrinks :
    ∀ {left toks T rest} → ParsesArrowTail left toks T rest
    → length rest ≤ length toks
  ParsesArrowTail-shrinks (pat-done _) = ≤-refl
  ParsesArrowTail-shrinks (pat-arrow-g {q = Zero} dT) =
    <⇒≤ (<-trans (ParsesType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesArrowTail-shrinks (pat-arrow-g {q = One}  dT) =
    <⇒≤ (<-trans (ParsesType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesArrowTail-shrinks (pat-arrow-g {q = Many} dT) =
    <⇒≤ (<-trans (ParsesType-shrinks dT) (s≤s (n≤1+n _)))
  ParsesArrowTail-shrinks (pat-arrow dT) =
    <⇒≤ (<-trans (ParsesType-shrinks dT) (s≤s ≤-refl))

  ParsesType-shrinks :
    ∀ {toks T rest} → ParsesType toks T rest → length rest < length toks
  ParsesType-shrinks (pt-mk dS dA) =
    ≤-<-trans (ParsesArrowTail-shrinks dA) (ParsesSum-shrinks dS)
