-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.TypeRelation
--
-- Inductive parsing relations for Once types, at the `Once.Parser.*`
-- layer (i.e. below Once.Grammar.*). Mirrors the precedence structure
-- of `Once.Parser.Type`'s mutual parsers: atom → prod → sum → type,
-- plus the three tail parsers. Each `ParsesX toks T rest` reads as:
-- "from `toks`, the X-level parser produces type `T` and leaves
-- residual tokens `rest`."
--
-- Kept in the `Once.Parser.*` hierarchy (not `Once.Grammar.*`) so the
-- parser function itself can use these relations in its return type —
-- the "Dec-valued parser" design for plan 0.3 task #40. Downstream
-- grammar-side proofs (`Once.Grammar.ParserRelation` / `RelRoundtrip`
-- / `Roundtrip`) re-export from this module.
------------------------------------------------------------------------

module Once.Parser.TypeRelation where

open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Nat using (_<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; <-trans; ≤-<-trans; <⇒≤;
                                        n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Quantity; Zero; One; Many; mk-kind; pure; eff;
                             Functor; K; Id; _⊕_; _⊗_; μ-type)
open import Once.Parser.Token

------------------------------------------------------------------------
-- Predicates on residuals: which tokens stop a prod / sum / arrow tail.
------------------------------------------------------------------------

-- Residual doesn't start with `TStar` — the only product-tail trigger.
NotStar : List Token → Set
NotStar [] = Data.Unit.⊤ where open import Data.Unit
NotStar (TStar ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotStar (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- Residual doesn't start with `TPlus` — the only sum-tail trigger.
-- (TStar allowed as a pass-through since lower-level prod-tail
-- already handled it before sum-tail was called.)
NotStarPlus : List Token → Set
NotStarPlus [] = Data.Unit.⊤ where open import Data.Unit
NotStarPlus (TPlus ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotStarPlus (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- Residual doesn't start with an arrow-tail consumption trigger
-- (`TArrow` or `TCaret0/1/W`). TStar/TPlus are admitted (they sit
-- below arrow-tail in the grammar).
NotArrowOrGrade : List Token → Set
NotArrowOrGrade [] = Data.Unit.⊤ where open import Data.Unit
NotArrowOrGrade (TArrow  ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaret0 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaret1 ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (TCaretW ∷ _) = Data.Empty.⊥ where open import Data.Empty
NotArrowOrGrade (_ ∷ _) = Data.Unit.⊤ where open import Data.Unit

-- All-clean: rejects every token any tail-parser would consume.
-- User-facing round-trip premise: trailing tokens look like none of
-- {TStar, TPlus, TArrow, TCaret*}.
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
-- Token form of a quantity annotation. Must match `quantityToken` in
-- `Once.Grammar.Printer` for the round-trip theorem to hold.
------------------------------------------------------------------------

quantityTokenOf : Quantity → Token
quantityTokenOf Zero = TCaret0
quantityTokenOf One  = TCaret1
quantityTokenOf Many = TCaretW

------------------------------------------------------------------------
-- Parsing relations (mutual inductive, one per grammar level).
------------------------------------------------------------------------

mutual

  -- atom ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
  --        | 'Eff' atom atom | 'IO' atom | '(' type ')'
  data ParsesAtom : List Token → Type → List Token → Set where

    pa-unit    : ∀ rest → ParsesAtom (TWord "Unit"   ∷ rest) Unit   rest
    pa-void    : ∀ rest → ParsesAtom (TWord "Void"   ∷ rest) Void   rest
    pa-int     : ∀ rest → ParsesAtom (TWord "Int"    ∷ rest) Int    rest
    pa-float   : ∀ rest → ParsesAtom (TWord "Float"  ∷ rest) Float  rest
    pa-buffer  : ∀ rest → ParsesAtom (TWord "Buffer" ∷ rest) Buffer rest
    pa-string  : ∀ rest → ParsesAtom (TWord "String" ∷ rest) Str    rest

    pa-eff : ∀ {toks1 toks2 rest} {A B : Type}
           → ParsesAtom toks1 A toks2
           → ParsesAtom toks2 B rest
           → ParsesAtom (TWord "Eff" ∷ toks1) (A ⇒[ mk-kind Many eff ] B) rest

    pa-io : ∀ {toks1 rest} {A : Type}
          → ParsesAtom toks1 A rest
          → ParsesAtom (TWord "IO" ∷ toks1) (Unit ⇒[ mk-kind Many eff ] A) rest

    pa-paren : ∀ {toks rest1 rest2} {T : Type}
             → ParsesType toks T rest1
             → rest1 ≡ TRParen ∷ rest2
             → ParsesAtom (TLParen ∷ toks) T rest2

    -- 'Mu' functor  — initial algebra of a polynomial functor.
    pa-mu : ∀ {toks rest} {F : Functor}
          → ParsesFunctorSum toks F rest
          → ParsesAtom (TWord "Mu" ∷ toks) (μ-type F) rest

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
    pat-arrow-g : ∀ {left toks rest} {B : Type} {q : Quantity}
                → ParsesType toks B rest
                → ParsesArrowTail left
                    (quantityTokenOf q ∷ TArrow ∷ toks)
                    (left ⇒[ mk-kind q pure ] B) rest
    pat-arrow : ∀ {left toks rest} {B : Type}
              → ParsesType toks B rest
              → ParsesArrowTail left (TArrow ∷ toks) (left ⇒[ mk-kind Many pure ] B) rest

  ------------------------------------------------------------------------
  -- Functor sub-grammar (the body of `Mu`). Mirrors the type levels:
  -- atom → prod → sum, left-associated, no arrow level. `K`'s argument
  -- is a type ATOM, parsed by the shared `ParsesAtom`.
  --
  --   fAtom ::= 'Id' | 'K' atom | '(' fSum ')'
  --   fProd ::= fAtom ('*' fAtom)*
  --   fSum  ::= fProd ('+' fProd)*
  ------------------------------------------------------------------------

  data ParsesFunctorAtom : List Token → Functor → List Token → Set where
    pfa-id : ∀ rest → ParsesFunctorAtom (TWord "Id" ∷ rest) Id rest
    pfa-k  : ∀ {toks rest} {A : Type}
           → ParsesAtom toks A rest
           → ParsesFunctorAtom (TWord "K" ∷ toks) (K A) rest
    pfa-paren : ∀ {toks rest1 rest2} {F : Functor}
              → ParsesFunctorSum toks F rest1
              → rest1 ≡ TRParen ∷ rest2
              → ParsesFunctorAtom (TLParen ∷ toks) F rest2

  data ParsesFunctorProd : List Token → Functor → List Token → Set where
    pfp-mk : ∀ {toks toks1 rest} {A F : Functor}
           → ParsesFunctorAtom toks A toks1
           → ParsesFunctorProdTail A toks1 F rest
           → ParsesFunctorProd toks F rest

  data ParsesFunctorProdTail : Functor → List Token → Functor → List Token → Set where
    pfpt-done : ∀ {left toks} → NotStar toks → ParsesFunctorProdTail left toks left toks
    pfpt-star : ∀ {left toks1 toks2 rest} {B F : Functor}
              → ParsesFunctorAtom toks1 B toks2
              → ParsesFunctorProdTail (left ⊗ B) toks2 F rest
              → ParsesFunctorProdTail left (TStar ∷ toks1) F rest

  data ParsesFunctorSum : List Token → Functor → List Token → Set where
    pfs-mk : ∀ {toks toks1 rest} {A F : Functor}
           → ParsesFunctorProd toks A toks1
           → ParsesFunctorSumTail A toks1 F rest
           → ParsesFunctorSum toks F rest

  data ParsesFunctorSumTail : Functor → List Token → Functor → List Token → Set where
    pfst-done : ∀ {left toks} → NotStarPlus toks → ParsesFunctorSumTail left toks left toks
    pfst-plus : ∀ {left toks1 toks2 rest} {B F : Functor}
              → ParsesFunctorProd toks1 B toks2
              → ParsesFunctorSumTail (left ⊕ B) toks2 F rest
              → ParsesFunctorSumTail left (TPlus ∷ toks1) F rest

------------------------------------------------------------------------
-- Shrinks: a successful derivation leaves a strictly smaller (or ≤
-- for tail parsers) residual. Mutual structural induction on
-- derivations — no parser involved. Used by the parser itself to
-- construct Acc arguments for WF recursive sub-calls.
------------------------------------------------------------------------

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
  ParsesAtom-shrinks (pa-mu dF) =
    <-trans (ParsesFunctorSum-shrinks dF) (s≤s ≤-refl)

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

  ParsesFunctorAtom-shrinks :
    ∀ {toks F rest} → ParsesFunctorAtom toks F rest → length rest < length toks
  ParsesFunctorAtom-shrinks (pfa-id rest) = s≤s ≤-refl
  ParsesFunctorAtom-shrinks (pfa-k dA) =
    <-trans (ParsesAtom-shrinks dA) (s≤s ≤-refl)
  ParsesFunctorAtom-shrinks (pfa-paren dF refl) =
    <-trans (s≤s ≤-refl)
            (<-trans (ParsesFunctorSum-shrinks dF) (s≤s ≤-refl))

  ParsesFunctorProd-shrinks :
    ∀ {toks F rest} → ParsesFunctorProd toks F rest → length rest < length toks
  ParsesFunctorProd-shrinks (pfp-mk dA dTail) =
    ≤-<-trans (ParsesFunctorProdTail-shrinks dTail) (ParsesFunctorAtom-shrinks dA)

  ParsesFunctorProdTail-shrinks :
    ∀ {left toks F rest} → ParsesFunctorProdTail left toks F rest
    → length rest ≤ length toks
  ParsesFunctorProdTail-shrinks (pfpt-done _) = ≤-refl
  ParsesFunctorProdTail-shrinks (pfpt-star dB dTail) =
    <⇒≤ (≤-<-trans (ParsesFunctorProdTail-shrinks dTail)
                   (<-trans (ParsesFunctorAtom-shrinks dB) (s≤s ≤-refl)))

  ParsesFunctorSum-shrinks :
    ∀ {toks F rest} → ParsesFunctorSum toks F rest → length rest < length toks
  ParsesFunctorSum-shrinks (pfs-mk dA dTail) =
    ≤-<-trans (ParsesFunctorSumTail-shrinks dTail) (ParsesFunctorProd-shrinks dA)

  ParsesFunctorSumTail-shrinks :
    ∀ {left toks F rest} → ParsesFunctorSumTail left toks F rest
    → length rest ≤ length toks
  ParsesFunctorSumTail-shrinks (pfst-done _) = ≤-refl
  ParsesFunctorSumTail-shrinks (pfst-plus dB dTail) =
    <⇒≤ (≤-<-trans (ParsesFunctorSumTail-shrinks dTail)
                   (<-trans (ParsesFunctorProd-shrinks dB) (s≤s ≤-refl)))
