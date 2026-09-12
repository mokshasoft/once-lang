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
                             Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type)
open import Once.Parser.Token
open import Once.Parser.Type using (parseType; parseTypeAtom)
open import Once.Parser.TypeRelation
open import Once.Grammar.Convert using (Expressible;
                                         ex-unit; ex-void; ex-int;
                                         ex-float; ex-str; ex-buffer;
                                         ex-prod; ex-sum; ex-fun; ex-eff;
                                         ex-mu; ex-nu;
                                         ExpressibleF; exf-k; exf-id;
                                         exf-sum; exf-prod)
open import Once.Grammar.ParserBridge using (sound-type; sound-atom)

------------------------------------------------------------------------
-- Structural Expressible extraction per precedence level. With the functor
-- sub-grammar, `pa-mu` produces a μ-type, which is grammar-expressible
-- (Expressible allows μ); the functor body's expressibility is established by
-- the mutual `Parses*Functor*-ExpressibleF` lemmas.
------------------------------------------------------------------------

mutual

  ParsesAtom-Expressible : ∀ {toks T rest} → ParsesAtom toks T rest → Expressible T
  ParsesAtom-Expressible (pa-unit   _) = ex-unit
  ParsesAtom-Expressible (pa-void   _) = ex-void
  ParsesAtom-Expressible (pa-int    _) = ex-int
  ParsesAtom-Expressible (pa-float  _) = ex-float
  ParsesAtom-Expressible (pa-buffer _) = ex-buffer
  ParsesAtom-Expressible (pa-string _) = ex-str
  ParsesAtom-Expressible (pa-eff dA dB) =
    ex-eff (ParsesAtom-Expressible dA) (ParsesAtom-Expressible dB)
  ParsesAtom-Expressible (pa-io dA) =
    ex-eff ex-unit (ParsesAtom-Expressible dA)
  ParsesAtom-Expressible (pa-paren dT refl) = ParsesType-Expressible dT
  ParsesAtom-Expressible (pa-mu dF) = ex-mu (ParsesFunctorSum-ExpressibleF dF)
  ParsesAtom-Expressible (pa-nu dF) = ex-nu (ParsesFunctorSum-ExpressibleF dF)

  ParsesProd-Expressible : ∀ {toks T rest} → ParsesProd toks T rest → Expressible T
  ParsesProd-Expressible (pp-mk dA dTail) =
    ParsesProdTail-Expressible dTail (ParsesAtom-Expressible dA)

  ParsesProdTail-Expressible :
    ∀ {left toks T rest} → ParsesProdTail left toks T rest
    → Expressible left → Expressible T
  ParsesProdTail-Expressible (ppt-done _) nmL = nmL
  ParsesProdTail-Expressible (ppt-star dB dTail) nmL =
    ParsesProdTail-Expressible dTail (ex-prod nmL (ParsesAtom-Expressible dB))

  ParsesSum-Expressible : ∀ {toks T rest} → ParsesSum toks T rest → Expressible T
  ParsesSum-Expressible (ps-mk dA dTail) =
    ParsesSumTail-Expressible dTail (ParsesProd-Expressible dA)

  ParsesSumTail-Expressible :
    ∀ {left toks T rest} → ParsesSumTail left toks T rest
    → Expressible left → Expressible T
  ParsesSumTail-Expressible (pst-done _) nmL = nmL
  ParsesSumTail-Expressible (pst-plus dB dTail) nmL =
    ParsesSumTail-Expressible dTail (ex-sum nmL (ParsesProd-Expressible dB))

  ParsesArrowTail-Expressible :
    ∀ {left toks T rest} → ParsesArrowTail left toks T rest
    → Expressible left → Expressible T
  ParsesArrowTail-Expressible (pat-done _) nmL = nmL
  ParsesArrowTail-Expressible (pat-arrow-g dT) nmL =
    ex-fun nmL (ParsesType-Expressible dT)
  ParsesArrowTail-Expressible (pat-arrow dT) nmL =
    ex-fun nmL (ParsesType-Expressible dT)

  ParsesType-Expressible : ∀ {toks T rest} → ParsesType toks T rest → Expressible T
  ParsesType-Expressible (pt-mk dS dA) =
    ParsesArrowTail-Expressible dA (ParsesSum-Expressible dS)

  -- Functor sub-grammar: each level preserves ExpressibleF.
  ParsesFunctorAtom-ExpressibleF :
    ∀ {toks F rest} → ParsesFunctorAtom toks F rest → ExpressibleF F
  ParsesFunctorAtom-ExpressibleF (pfa-id _) = exf-id
  ParsesFunctorAtom-ExpressibleF (pfa-k dA) = exf-k (ParsesAtom-Expressible dA)
  ParsesFunctorAtom-ExpressibleF (pfa-paren dF refl) = ParsesFunctorSum-ExpressibleF dF

  ParsesFunctorProd-ExpressibleF :
    ∀ {toks F rest} → ParsesFunctorProd toks F rest → ExpressibleF F
  ParsesFunctorProd-ExpressibleF (pfp-mk dA dTail) =
    ParsesFunctorProdTail-ExpressibleF dTail (ParsesFunctorAtom-ExpressibleF dA)

  ParsesFunctorProdTail-ExpressibleF :
    ∀ {left toks F rest} → ParsesFunctorProdTail left toks F rest
    → ExpressibleF left → ExpressibleF F
  ParsesFunctorProdTail-ExpressibleF (pfpt-done _) nmL = nmL
  ParsesFunctorProdTail-ExpressibleF (pfpt-star dB dTail) nmL =
    ParsesFunctorProdTail-ExpressibleF dTail (exf-prod nmL (ParsesFunctorAtom-ExpressibleF dB))

  ParsesFunctorSum-ExpressibleF :
    ∀ {toks F rest} → ParsesFunctorSum toks F rest → ExpressibleF F
  ParsesFunctorSum-ExpressibleF (pfs-mk dA dTail) =
    ParsesFunctorSumTail-ExpressibleF dTail (ParsesFunctorProd-ExpressibleF dA)

  ParsesFunctorSumTail-ExpressibleF :
    ∀ {left toks F rest} → ParsesFunctorSumTail left toks F rest
    → ExpressibleF left → ExpressibleF F
  ParsesFunctorSumTail-ExpressibleF (pfst-done _) nmL = nmL
  ParsesFunctorSumTail-ExpressibleF (pfst-plus dB dTail) nmL =
    ParsesFunctorSumTail-ExpressibleF dTail (exf-sum nmL (ParsesFunctorProd-ExpressibleF dB))

------------------------------------------------------------------------
-- Function-level invariant: compose soundness with structural Expressible.
------------------------------------------------------------------------

parseType-Expressible :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseType toks ≡ just (t , rest) → Expressible t
parseType-Expressible toks eq = ParsesType-Expressible (sound-type eq)

parseTypeAtom-Expressible :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeAtom toks ≡ just (t , rest) → Expressible t
parseTypeAtom-Expressible toks eq = ParsesAtom-Expressible (sound-atom eq)
