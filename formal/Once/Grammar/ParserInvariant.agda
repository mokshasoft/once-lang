-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
                             _*_; _+_; _⇒[_]_; Quantity; Zero; One; Many; mk-kind; pure; eff;
                             Functor; K; Id; _⊕_; _⊗_; μ-type)
open import Once.Parser.Token
open import Once.Parser.Type using (parseType; parseTypeAtom)
open import Once.Parser.TypeRelation
open import Once.Grammar.Convert using (NoNu;
                                         nnu-unit; nnu-void; nnu-int;
                                         nnu-float; nnu-str; nnu-buffer;
                                         nnu-prod; nnu-sum; nnu-fun; nnu-eff;
                                         nnu-mu;
                                         NoNuF; nnuf-k; nnuf-id;
                                         nnuf-sum; nnuf-prod)
open import Once.Grammar.ParserBridge using (sound-type; sound-atom)

------------------------------------------------------------------------
-- Structural NoNu extraction per precedence level. With the functor
-- sub-grammar, `pa-mu` produces a μ-type, which is grammar-expressible
-- (NoNu allows μ); the functor body's expressibility is established by
-- the mutual `Parses*Functor*-NoNuF` lemmas.
------------------------------------------------------------------------

mutual

  ParsesAtom-NoNu : ∀ {toks T rest} → ParsesAtom toks T rest → NoNu T
  ParsesAtom-NoNu (pa-unit   _) = nnu-unit
  ParsesAtom-NoNu (pa-void   _) = nnu-void
  ParsesAtom-NoNu (pa-int    _) = nnu-int
  ParsesAtom-NoNu (pa-float  _) = nnu-float
  ParsesAtom-NoNu (pa-buffer _) = nnu-buffer
  ParsesAtom-NoNu (pa-string _) = nnu-str
  ParsesAtom-NoNu (pa-eff dA dB) =
    nnu-eff (ParsesAtom-NoNu dA) (ParsesAtom-NoNu dB)
  ParsesAtom-NoNu (pa-io dA) =
    nnu-eff nnu-unit (ParsesAtom-NoNu dA)
  ParsesAtom-NoNu (pa-paren dT refl) = ParsesType-NoNu dT
  ParsesAtom-NoNu (pa-mu dF) = nnu-mu (ParsesFunctorSum-NoNuF dF)

  ParsesProd-NoNu : ∀ {toks T rest} → ParsesProd toks T rest → NoNu T
  ParsesProd-NoNu (pp-mk dA dTail) =
    ParsesProdTail-NoNu dTail (ParsesAtom-NoNu dA)

  ParsesProdTail-NoNu :
    ∀ {left toks T rest} → ParsesProdTail left toks T rest
    → NoNu left → NoNu T
  ParsesProdTail-NoNu (ppt-done _) nmL = nmL
  ParsesProdTail-NoNu (ppt-star dB dTail) nmL =
    ParsesProdTail-NoNu dTail (nnu-prod nmL (ParsesAtom-NoNu dB))

  ParsesSum-NoNu : ∀ {toks T rest} → ParsesSum toks T rest → NoNu T
  ParsesSum-NoNu (ps-mk dA dTail) =
    ParsesSumTail-NoNu dTail (ParsesProd-NoNu dA)

  ParsesSumTail-NoNu :
    ∀ {left toks T rest} → ParsesSumTail left toks T rest
    → NoNu left → NoNu T
  ParsesSumTail-NoNu (pst-done _) nmL = nmL
  ParsesSumTail-NoNu (pst-plus dB dTail) nmL =
    ParsesSumTail-NoNu dTail (nnu-sum nmL (ParsesProd-NoNu dB))

  ParsesArrowTail-NoNu :
    ∀ {left toks T rest} → ParsesArrowTail left toks T rest
    → NoNu left → NoNu T
  ParsesArrowTail-NoNu (pat-done _) nmL = nmL
  ParsesArrowTail-NoNu (pat-arrow-g dT) nmL =
    nnu-fun nmL (ParsesType-NoNu dT)
  ParsesArrowTail-NoNu (pat-arrow dT) nmL =
    nnu-fun nmL (ParsesType-NoNu dT)

  ParsesType-NoNu : ∀ {toks T rest} → ParsesType toks T rest → NoNu T
  ParsesType-NoNu (pt-mk dS dA) =
    ParsesArrowTail-NoNu dA (ParsesSum-NoNu dS)

  -- Functor sub-grammar: each level preserves NoNuF.
  ParsesFunctorAtom-NoNuF :
    ∀ {toks F rest} → ParsesFunctorAtom toks F rest → NoNuF F
  ParsesFunctorAtom-NoNuF (pfa-id _) = nnuf-id
  ParsesFunctorAtom-NoNuF (pfa-k dA) = nnuf-k (ParsesAtom-NoNu dA)
  ParsesFunctorAtom-NoNuF (pfa-paren dF refl) = ParsesFunctorSum-NoNuF dF

  ParsesFunctorProd-NoNuF :
    ∀ {toks F rest} → ParsesFunctorProd toks F rest → NoNuF F
  ParsesFunctorProd-NoNuF (pfp-mk dA dTail) =
    ParsesFunctorProdTail-NoNuF dTail (ParsesFunctorAtom-NoNuF dA)

  ParsesFunctorProdTail-NoNuF :
    ∀ {left toks F rest} → ParsesFunctorProdTail left toks F rest
    → NoNuF left → NoNuF F
  ParsesFunctorProdTail-NoNuF (pfpt-done _) nmL = nmL
  ParsesFunctorProdTail-NoNuF (pfpt-star dB dTail) nmL =
    ParsesFunctorProdTail-NoNuF dTail (nnuf-prod nmL (ParsesFunctorAtom-NoNuF dB))

  ParsesFunctorSum-NoNuF :
    ∀ {toks F rest} → ParsesFunctorSum toks F rest → NoNuF F
  ParsesFunctorSum-NoNuF (pfs-mk dA dTail) =
    ParsesFunctorSumTail-NoNuF dTail (ParsesFunctorProd-NoNuF dA)

  ParsesFunctorSumTail-NoNuF :
    ∀ {left toks F rest} → ParsesFunctorSumTail left toks F rest
    → NoNuF left → NoNuF F
  ParsesFunctorSumTail-NoNuF (pfst-done _) nmL = nmL
  ParsesFunctorSumTail-NoNuF (pfst-plus dB dTail) nmL =
    ParsesFunctorSumTail-NoNuF dTail (nnuf-sum nmL (ParsesFunctorProd-NoNuF dB))

------------------------------------------------------------------------
-- Function-level invariant: compose soundness with structural NoNu.
------------------------------------------------------------------------

parseType-NoNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseType toks ≡ just (t , rest) → NoNu t
parseType-NoNu toks eq = ParsesType-NoNu (sound-type eq)

parseTypeAtom-NoNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeAtom toks ≡ just (t , rest) → NoNu t
parseTypeAtom-NoNu toks eq = ParsesAtom-NoNu (sound-atom eq)
