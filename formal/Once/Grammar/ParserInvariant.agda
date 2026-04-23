-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ParserInvariant
--
-- Plan 0.3 gap G5: cross-stage invariant. `parseType` only produces
-- types that are grammar-expressible — i.e. satisfy `NoMuNu`.
-- Downstream stages (elaboration, IR lowering) can rely on the
-- absence of `μ-type` / `ν-type` in parser output.
--
-- Structure after the Dec-valued parser redesign (plan 0.3 task #40
-- option 1):
--
--   1. Structural `ParsesX-NoMuNu` lemmas per precedence level —
--      `ParsesType toks T rest → NoMuNu T`. Pure induction on
--      derivations; no parser machinery.
--   2. Wrapper `parseType-NoMuNu`: composes `sound-type` (trivial
--      projection from the Dec-valued parser's output Σ) with
--      `ParsesType-NoMuNu`.
------------------------------------------------------------------------

module Once.Grammar.ParserInvariant where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Quantity; Zero; One; Many; mk-kind; pure; eff)
open import Once.Parser.Token
open import Once.Parser.Type using (parseType; parseTypeAtom)
open import Once.Parser.TypeRelation
open import Once.Grammar.Convert using (NoMuNu;
                                         nmn-unit; nmn-void; nmn-int;
                                         nmn-float; nmn-str; nmn-buffer;
                                         nmn-prod; nmn-sum; nmn-fun; nmn-eff)
open import Once.Grammar.ParserBridge using (sound-type; sound-atom)

------------------------------------------------------------------------
-- Structural NoMuNu extraction per precedence level.
------------------------------------------------------------------------

mutual

  ParsesAtom-NoMuNu : ∀ {toks T rest} → ParsesAtom toks T rest → NoMuNu T
  ParsesAtom-NoMuNu (pa-unit   _) = nmn-unit
  ParsesAtom-NoMuNu (pa-void   _) = nmn-void
  ParsesAtom-NoMuNu (pa-int    _) = nmn-int
  ParsesAtom-NoMuNu (pa-float  _) = nmn-float
  ParsesAtom-NoMuNu (pa-buffer _) = nmn-buffer
  ParsesAtom-NoMuNu (pa-string _) = nmn-str
  ParsesAtom-NoMuNu (pa-eff dA dB) =
    nmn-eff (ParsesAtom-NoMuNu dA) (ParsesAtom-NoMuNu dB)
  ParsesAtom-NoMuNu (pa-io dA) =
    nmn-eff nmn-unit (ParsesAtom-NoMuNu dA)
  ParsesAtom-NoMuNu (pa-paren dT refl) = ParsesType-NoMuNu dT

  ParsesProd-NoMuNu : ∀ {toks T rest} → ParsesProd toks T rest → NoMuNu T
  ParsesProd-NoMuNu (pp-mk dA dTail) =
    ParsesProdTail-NoMuNu dTail (ParsesAtom-NoMuNu dA)

  ParsesProdTail-NoMuNu :
    ∀ {left toks T rest} → ParsesProdTail left toks T rest
    → NoMuNu left → NoMuNu T
  ParsesProdTail-NoMuNu (ppt-done _) nmL = nmL
  ParsesProdTail-NoMuNu (ppt-star dB dTail) nmL =
    ParsesProdTail-NoMuNu dTail (nmn-prod nmL (ParsesAtom-NoMuNu dB))

  ParsesSum-NoMuNu : ∀ {toks T rest} → ParsesSum toks T rest → NoMuNu T
  ParsesSum-NoMuNu (ps-mk dA dTail) =
    ParsesSumTail-NoMuNu dTail (ParsesProd-NoMuNu dA)

  ParsesSumTail-NoMuNu :
    ∀ {left toks T rest} → ParsesSumTail left toks T rest
    → NoMuNu left → NoMuNu T
  ParsesSumTail-NoMuNu (pst-done _) nmL = nmL
  ParsesSumTail-NoMuNu (pst-plus dB dTail) nmL =
    ParsesSumTail-NoMuNu dTail (nmn-sum nmL (ParsesProd-NoMuNu dB))

  ParsesArrowTail-NoMuNu :
    ∀ {left toks T rest} → ParsesArrowTail left toks T rest
    → NoMuNu left → NoMuNu T
  ParsesArrowTail-NoMuNu (pat-done _) nmL = nmL
  ParsesArrowTail-NoMuNu (pat-arrow-g dT) nmL =
    nmn-fun nmL (ParsesType-NoMuNu dT)
  ParsesArrowTail-NoMuNu (pat-arrow dT) nmL =
    nmn-fun nmL (ParsesType-NoMuNu dT)

  ParsesType-NoMuNu : ∀ {toks T rest} → ParsesType toks T rest → NoMuNu T
  ParsesType-NoMuNu (pt-mk dS dA) =
    ParsesArrowTail-NoMuNu dA (ParsesSum-NoMuNu dS)

------------------------------------------------------------------------
-- Function-level invariant: compose soundness with structural NoMuNu.
------------------------------------------------------------------------

parseType-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseType toks ≡ just (t , rest) → NoMuNu t
parseType-NoMuNu toks eq = ParsesType-NoMuNu (sound-type eq)

parseTypeAtom-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeAtom toks ≡ just (t , rest) → NoMuNu t
parseTypeAtom-NoMuNu toks eq = ParsesAtom-NoMuNu (sound-atom eq)
