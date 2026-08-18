-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.RelRoundtrip
--
-- Structural round-trip: for every `Concrete g`, the printed tokens
-- of `g` (plus any `NotCont` trailing tokens) are derived by the
-- parsing relation (`ParsesType`) to produce `toType g` with the
-- trailing tokens left intact.
--
-- The proofs are pure structural induction on `Concrete g`. No
-- function reductions, no Acc threading — the WF-parser function
-- does not appear anywhere in this module.
--
-- The function-level round-trip theorem lives in `Roundtrip.agda`;
-- it composes these structural derivations with the completeness
-- bridge (`parseType toks ≡ just (T, rest) ← ParsesType toks T rest`)
-- from `ParserBridge.agda`.
------------------------------------------------------------------------

module Once.Grammar.RelRoundtrip where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Once.Type using (Type; _*_; _+_; _⇒[_]_; Unit;
                             Quantity; Zero; One; Many; mk-kind; pure; eff)
open import Once.Parser.Token
import Once.Grammar as G
open G using (GType)
open import Once.Grammar.Printer using (printGType; quantityToken; Concrete;
                                        c-unit; c-void; c-int; c-float;
                                        c-buffer; c-string; c-prod; c-sum;
                                        c-fun; c-eff)
open import Once.Grammar.ParserRelation

------------------------------------------------------------------------
-- quantityToken from Printer matches quantityTokenOf in the relation
------------------------------------------------------------------------

quantityToken≡quantityTokenOf : ∀ q → quantityToken q ≡ quantityTokenOf q
quantityToken≡quantityTokenOf Zero = refl
quantityToken≡quantityTokenOf One  = refl
quantityToken≡quantityTokenOf Many = refl

------------------------------------------------------------------------
-- Helpers: NotCont implies the weaker NotStar / NotStarPlus, and
-- quantity tokens don't trip up NotStar / NotStarPlus.
------------------------------------------------------------------------

NotCont→NotStar : ∀ {toks} → NotCont toks → NotStar toks
NotCont→NotStar {[]} _ = tt
NotCont→NotStar {TStar ∷ _} ()
NotCont→NotStar {TPlus ∷ _} _ = tt
NotCont→NotStar {TArrow ∷ _} _ = tt
NotCont→NotStar {TCaret0 ∷ _} _ = tt
NotCont→NotStar {TCaret1 ∷ _} _ = tt
NotCont→NotStar {TCaretW ∷ _} _ = tt
NotCont→NotStar {TLParen    ∷ _} _ = tt
NotCont→NotStar {TRParen    ∷ _} _ = tt
NotCont→NotStar {TLBrace    ∷ _} _ = tt
NotCont→NotStar {TRBrace    ∷ _} _ = tt
NotCont→NotStar {TColon     ∷ _} _ = tt
NotCont→NotStar {TEquals    ∷ _} _ = tt
NotCont→NotStar {TLambda    ∷ _} _ = tt
NotCont→NotStar {TComma     ∷ _} _ = tt
NotCont→NotStar {TSemicolon ∷ _} _ = tt
NotCont→NotStar {TAt        ∷ _} _ = tt
NotCont→NotStar {TPipe      ∷ _} _ = tt
NotCont→NotStar {TDot       ∷ _} _ = tt
NotCont→NotStar {TMinus     ∷ _} _ = tt
NotCont→NotStar {TSlash     ∷ _} _ = tt
NotCont→NotStar {TPercent   ∷ _} _ = tt
NotCont→NotStar {TAmpersand ∷ _} _ = tt
NotCont→NotStar {TLt        ∷ _} _ = tt
NotCont→NotStar {TLe        ∷ _} _ = tt
NotCont→NotStar {TGt        ∷ _} _ = tt
NotCont→NotStar {TGe        ∷ _} _ = tt
NotCont→NotStar {TEqEq      ∷ _} _ = tt
NotCont→NotStar {TNeq       ∷ _} _ = tt
NotCont→NotStar {TBang      ∷ _} _ = tt
NotCont→NotStar {TNewline   ∷ _} _ = tt
NotCont→NotStar {TEOF       ∷ _} _ = tt
NotCont→NotStar {TWord _    ∷ _} _ = tt
NotCont→NotStar {TInt _     ∷ _} _ = tt
NotCont→NotStar {TFloat _ _ _     ∷ _} _ = tt
NotCont→NotStar {TString _  ∷ _} _ = tt

NotCont→NotStarPlus : ∀ {toks} → NotCont toks → NotStarPlus toks
NotCont→NotStarPlus {[]} _ = tt
NotCont→NotStarPlus {TStar ∷ _} ()
NotCont→NotStarPlus {TPlus ∷ _} ()
NotCont→NotStarPlus {TArrow ∷ _} _ = tt
NotCont→NotStarPlus {TCaret0 ∷ _} _ = tt
NotCont→NotStarPlus {TCaret1 ∷ _} _ = tt
NotCont→NotStarPlus {TCaretW ∷ _} _ = tt
NotCont→NotStarPlus {TLParen    ∷ _} _ = tt
NotCont→NotStarPlus {TRParen    ∷ _} _ = tt
NotCont→NotStarPlus {TLBrace    ∷ _} _ = tt
NotCont→NotStarPlus {TRBrace    ∷ _} _ = tt
NotCont→NotStarPlus {TColon     ∷ _} _ = tt
NotCont→NotStarPlus {TEquals    ∷ _} _ = tt
NotCont→NotStarPlus {TLambda    ∷ _} _ = tt
NotCont→NotStarPlus {TComma     ∷ _} _ = tt
NotCont→NotStarPlus {TSemicolon ∷ _} _ = tt
NotCont→NotStarPlus {TAt        ∷ _} _ = tt
NotCont→NotStarPlus {TPipe      ∷ _} _ = tt
NotCont→NotStarPlus {TDot       ∷ _} _ = tt
NotCont→NotStarPlus {TMinus     ∷ _} _ = tt
NotCont→NotStarPlus {TSlash     ∷ _} _ = tt
NotCont→NotStarPlus {TPercent   ∷ _} _ = tt
NotCont→NotStarPlus {TAmpersand ∷ _} _ = tt
NotCont→NotStarPlus {TLt        ∷ _} _ = tt
NotCont→NotStarPlus {TLe        ∷ _} _ = tt
NotCont→NotStarPlus {TGt        ∷ _} _ = tt
NotCont→NotStarPlus {TGe        ∷ _} _ = tt
NotCont→NotStarPlus {TEqEq      ∷ _} _ = tt
NotCont→NotStarPlus {TNeq       ∷ _} _ = tt
NotCont→NotStarPlus {TBang      ∷ _} _ = tt
NotCont→NotStarPlus {TNewline   ∷ _} _ = tt
NotCont→NotStarPlus {TEOF       ∷ _} _ = tt
NotCont→NotStarPlus {TWord _    ∷ _} _ = tt
NotCont→NotStarPlus {TInt _     ∷ _} _ = tt
NotCont→NotStarPlus {TFloat _ _ _     ∷ _} _ = tt
NotCont→NotStarPlus {TString _  ∷ _} _ = tt

NotCont→NotStar-quantity : ∀ q {rest : List Token}
                        → NotStar (quantityTokenOf q ∷ rest)
NotCont→NotStar-quantity Zero = tt
NotCont→NotStar-quantity One  = tt
NotCont→NotStar-quantity Many = tt

NotCont→NotStarPlus-quantity : ∀ q {rest : List Token}
                            → NotStarPlus (quantityTokenOf q ∷ rest)
NotCont→NotStarPlus-quantity Zero = tt
NotCont→NotStarPlus-quantity One  = tt
NotCont→NotStarPlus-quantity Many = tt

-- NotCont rejects TArrow/TCaret[012W], so it implies NotArrowOrGrade.
NotCont→NotArrowOrGrade : ∀ {toks} → NotCont toks → NotArrowOrGrade toks
NotCont→NotArrowOrGrade {[]} _ = tt
NotCont→NotArrowOrGrade {TStar ∷ _} _ = tt
NotCont→NotArrowOrGrade {TPlus ∷ _} _ = tt
NotCont→NotArrowOrGrade {TArrow ∷ _} ()
NotCont→NotArrowOrGrade {TCaret0 ∷ _} ()
NotCont→NotArrowOrGrade {TCaret1 ∷ _} ()
NotCont→NotArrowOrGrade {TCaretW ∷ _} ()
NotCont→NotArrowOrGrade {TLParen    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TRParen    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TLBrace    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TRBrace    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TColon     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TEquals    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TLambda    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TComma     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TSemicolon ∷ _} _ = tt
NotCont→NotArrowOrGrade {TAt        ∷ _} _ = tt
NotCont→NotArrowOrGrade {TPipe      ∷ _} _ = tt
NotCont→NotArrowOrGrade {TDot       ∷ _} _ = tt
NotCont→NotArrowOrGrade {TMinus     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TSlash     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TPercent   ∷ _} _ = tt
NotCont→NotArrowOrGrade {TAmpersand ∷ _} _ = tt
NotCont→NotArrowOrGrade {TLt        ∷ _} _ = tt
NotCont→NotArrowOrGrade {TLe        ∷ _} _ = tt
NotCont→NotArrowOrGrade {TGt        ∷ _} _ = tt
NotCont→NotArrowOrGrade {TGe        ∷ _} _ = tt
NotCont→NotArrowOrGrade {TEqEq      ∷ _} _ = tt
NotCont→NotArrowOrGrade {TNeq       ∷ _} _ = tt
NotCont→NotArrowOrGrade {TBang      ∷ _} _ = tt
NotCont→NotArrowOrGrade {TNewline   ∷ _} _ = tt
NotCont→NotArrowOrGrade {TEOF       ∷ _} _ = tt
NotCont→NotArrowOrGrade {TWord _    ∷ _} _ = tt
NotCont→NotArrowOrGrade {TInt _     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TFloat _ _ _     ∷ _} _ = tt
NotCont→NotArrowOrGrade {TString _  ∷ _} _ = tt

------------------------------------------------------------------------
-- Structural round-trip lemmas, mutually defined per precedence level
------------------------------------------------------------------------

mutual

  -- `printGType g ++ rest` parses as an atom producing `toType c` and
  -- leaving `rest`. Compound cases use the outer TLParen + TRParen to
  -- wrap the inner full-type derivation.
  rt-atom : ∀ {g : GType} (c : Concrete g) (rest : List Token)
          → ParsesAtom (printGType g ++ rest) (toType c) rest
  rt-atom c-unit   rest = pa-unit   rest
  rt-atom c-void   rest = pa-void   rest
  rt-atom c-int    rest = pa-int    rest
  rt-atom c-float  rest = pa-float  rest
  rt-atom c-buffer rest = pa-buffer rest
  rt-atom c-string rest = pa-string rest

  -- Product: `(A * B)` prints as `TLParen ∷ printGType A ++ TStar ∷
  -- printGType B ++ TRParen ∷ []`. Inner full-type derivation parses
  -- A * B leaving `TRParen ∷ rest`, which the outer pa-paren strips.
  rt-atom (c-prod {A = A} {B = B} cA cB) rest
    rewrite ++-assoc (printGType A) (TStar ∷ printGType B ++ TRParen ∷ []) rest
          | ++-assoc (printGType B) (TRParen ∷ []) rest
    = pa-paren (rt-type-of-prod cA cB (TRParen ∷ rest) tt) refl

  rt-atom (c-sum {A = A} {B = B} cA cB) rest
    rewrite ++-assoc (printGType A) (TPlus ∷ printGType B ++ TRParen ∷ []) rest
          | ++-assoc (printGType B) (TRParen ∷ []) rest
    = pa-paren (rt-type-of-sum cA cB (TRParen ∷ rest) tt) refl

  rt-atom (c-fun {A = A} {B = B} {q = q} cA cB) rest
    rewrite ++-assoc (printGType A)
              (quantityToken q ∷ TArrow ∷ printGType B ++ TRParen ∷ []) rest
          | ++-assoc (printGType B) (TRParen ∷ []) rest
    = pa-paren (rt-type-of-fun cA cB q (TRParen ∷ rest) tt) refl

  -- Eff A B: `TLParen ∷ TWord "Eff" ∷ printGType A ++ printGType B ++
  -- TRParen ∷ []`. The inner derivation parses Eff A B at the atom
  -- level via pa-eff (two successive atoms).
  rt-atom (c-eff {A = A} {B = B} cA cB) rest
    rewrite ++-assoc (printGType A) (printGType B ++ TRParen ∷ []) rest
          | ++-assoc (printGType B) (TRParen ∷ []) rest
    = pa-paren
        (pt-mk
          (ps-mk
            (pp-mk (pa-eff (rt-atom cA (printGType B ++ TRParen ∷ rest))
                           (rt-atom cB (TRParen ∷ rest)))
                   (ppt-done tt))
            (pst-done tt))
          (pat-done tt))
        refl

  -- Helper: given a Concrete prod, the inner derivation at TYPE level
  -- produces `toType cA * toType cB` leaving the caller's rest.
  -- rest starts with TRParen (the closing paren of the outer atom's
  -- printGType), so all continuation tokens are rejected cleanly.
  rt-type-of-prod :
    ∀ {A B : GType} (cA : Concrete A) (cB : Concrete B)
      (rest : List Token) → NotCont rest
    → ParsesType (printGType A ++ TStar ∷ printGType B ++ rest)
                 (toType cA * toType cB) rest
  rt-type-of-prod {A = A} {B = B} cA cB rest nc =
    pt-mk
      (ps-mk
        (pp-mk (rt-atom cA (TStar ∷ printGType B ++ rest))
               (ppt-star (rt-atom cB rest)
                         (ppt-done (NotCont→NotStar nc))))
        (pst-done (NotCont→NotStarPlus nc)))
      (pat-done (NotCont→NotArrowOrGrade nc))

  rt-type-of-sum :
    ∀ {A B : GType} (cA : Concrete A) (cB : Concrete B)
      (rest : List Token) → NotCont rest
    → ParsesType (printGType A ++ TPlus ∷ printGType B ++ rest)
                 (toType cA + toType cB) rest
  rt-type-of-sum {A = A} {B = B} cA cB rest nc =
    pt-mk
      (ps-mk
        (pp-mk (rt-atom cA (TPlus ∷ printGType B ++ rest))
               (ppt-done tt))
        (pst-plus (pp-mk (rt-atom cB rest)
                         (ppt-done (NotCont→NotStar nc)))
                  (pst-done (NotCont→NotStarPlus nc))))
      (pat-done (NotCont→NotArrowOrGrade nc))

  rt-type-of-fun :
    ∀ {A B : GType} (cA : Concrete A) (cB : Concrete B) (q : Quantity)
      (rest : List Token) → NotCont rest
    → ParsesType (printGType A ++ quantityToken q ∷ TArrow
                 ∷ printGType B ++ rest)
                 (toType cA ⇒[ mk-kind q pure ] toType cB) rest
  rt-type-of-fun {A = A} {B = B} cA cB q rest nc
    rewrite quantityToken≡quantityTokenOf q
    = pt-mk
        (ps-mk
          (pp-mk (rt-atom cA (quantityTokenOf q ∷ TArrow
                              ∷ printGType B ++ rest))
                 (ppt-done (NotCont→NotStar-quantity q)))
          (pst-done (NotCont→NotStarPlus-quantity q)))
        (pat-arrow-g (rt-type cB rest nc))

  -- rt-type: full-type round-trip. Mostly defers to rt-atom for
  -- compound atoms, then lifts through the precedence chain.
  rt-type : ∀ {g : GType} (c : Concrete g) (rest : List Token)
          → NotCont rest
          → ParsesType (printGType g ++ rest) (toType c) rest
  rt-type c rest nc =
    pt-mk
      (ps-mk
        (pp-mk (rt-atom c rest)
               (ppt-done (NotCont→NotStar nc)))
        (pst-done (NotCont→NotStarPlus nc)))
      (pat-done (NotCont→NotArrowOrGrade nc))

------------------------------------------------------------------------
-- Helpers: NotCont implies the weaker NotStar / NotStarPlus, and
-- quantity tokens don't trip up NotStar / NotStarPlus.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Top-level: `Concrete g` derives `ParsesType (printGType g) (toType c) []`.
------------------------------------------------------------------------

round-trip-rel :
  ∀ {g : GType} (c : Concrete g)
  → ParsesType (printGType g) (toType c) []
round-trip-rel {g} c
  rewrite sym (Data.List.Properties.++-identityʳ (printGType g))
  = rt-type c [] tt
  where import Data.List.Properties
