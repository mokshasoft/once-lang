-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.ParserInvariant
--
-- Plan 0.3 gap G5: cross-stage invariant. `parseType` only produces
-- types that are grammar-expressible — i.e., satisfy `NoMuNu`.
-- Downstream stages (elaboration, IR lowering) can rely on the
-- absence of `μ-type` / `ν-type` in parser output. This closes the
-- pipeline's type-side: the parser's output domain matches the
-- typechecker's input domain (no internal-only shapes).
--
-- Combined with the G1 round-trip theorem (`Once.Grammar.Roundtrip`),
-- this pins parser semantics from both directions: the parser agrees
-- with the printer on canonical inputs, and never produces shapes
-- the grammar cannot re-serialise.
------------------------------------------------------------------------

module Once.Grammar.ParserInvariant where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Eff; Quantity; Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.Type
open import Once.Grammar.Convert using (NoMuNu;
                                         nmn-unit; nmn-void; nmn-int;
                                         nmn-float; nmn-str; nmn-buffer;
                                         nmn-prod; nmn-sum; nmn-fun; nmn-eff)

------------------------------------------------------------------------
-- Mutual NoMuNu claims for each parser level.
--
-- Each: if the parser returns `just (t, rest)`, then `NoMuNu t`.
------------------------------------------------------------------------

{-# TERMINATING #-}
parseTypeAtom-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeAtom toks ≡ just (t , rest) → NoMuNu t

parseTypeProdTail-NoMuNu :
  ∀ (left : Type) → NoMuNu left
  → ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeProdTail left toks ≡ just (t , rest) → NoMuNu t

parseTypeProd-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeProd toks ≡ just (t , rest) → NoMuNu t

parseTypeSumTail-NoMuNu :
  ∀ (left : Type) → NoMuNu left
  → ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeSumTail left toks ≡ just (t , rest) → NoMuNu t

parseTypeSum-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseTypeSum toks ≡ just (t , rest) → NoMuNu t

parseArrowTail-NoMuNu :
  ∀ (left : Type) → NoMuNu left
  → ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseArrowTail left toks ≡ just (t , rest) → NoMuNu t

parseType-NoMuNu :
  ∀ (toks : List Token) {t : Type} {rest : List Token}
  → parseType toks ≡ just (t , rest) → NoMuNu t

------------------------------------------------------------------------
-- `tryParseTypeVar` always returns `nothing` (both branches of the
-- `isUpperWord` dispatch return `nothing`). Makes the post-refactor
-- parser's non-keyword TWord path absurd.
------------------------------------------------------------------------

tryParseTypeVar-nothing :
  ∀ (n : String) (r : List Token) → tryParseTypeVar n r ≡ nothing
tryParseTypeVar-nothing _ _ = refl

------------------------------------------------------------------------
-- parseTypeAtom cases
------------------------------------------------------------------------

parseTypeAtom-NoMuNu [] ()

-- Non-TWord non-TLParen tokens: parser fails.
parseTypeAtom-NoMuNu (TInt _     ∷ _) ()
parseTypeAtom-NoMuNu (TString _  ∷ _) ()
parseTypeAtom-NoMuNu (TRParen    ∷ _) ()
parseTypeAtom-NoMuNu (TLBrace    ∷ _) ()
parseTypeAtom-NoMuNu (TRBrace    ∷ _) ()
parseTypeAtom-NoMuNu (TColon     ∷ _) ()
parseTypeAtom-NoMuNu (TEquals    ∷ _) ()
parseTypeAtom-NoMuNu (TArrow     ∷ _) ()
parseTypeAtom-NoMuNu (TCaret0    ∷ _) ()
parseTypeAtom-NoMuNu (TCaret1    ∷ _) ()
parseTypeAtom-NoMuNu (TCaretW    ∷ _) ()
parseTypeAtom-NoMuNu (TLambda    ∷ _) ()
parseTypeAtom-NoMuNu (TComma     ∷ _) ()
parseTypeAtom-NoMuNu (TSemicolon ∷ _) ()
parseTypeAtom-NoMuNu (TAt        ∷ _) ()
parseTypeAtom-NoMuNu (TPipe      ∷ _) ()
parseTypeAtom-NoMuNu (TDot       ∷ _) ()
parseTypeAtom-NoMuNu (TPlus      ∷ _) ()
parseTypeAtom-NoMuNu (TMinus     ∷ _) ()
parseTypeAtom-NoMuNu (TStar      ∷ _) ()
parseTypeAtom-NoMuNu (TSlash     ∷ _) ()
parseTypeAtom-NoMuNu (TPercent   ∷ _) ()
parseTypeAtom-NoMuNu (TAmpersand ∷ _) ()
parseTypeAtom-NoMuNu (TLt        ∷ _) ()
parseTypeAtom-NoMuNu (TLe        ∷ _) ()
parseTypeAtom-NoMuNu (TGt        ∷ _) ()
parseTypeAtom-NoMuNu (TGe        ∷ _) ()
parseTypeAtom-NoMuNu (TEqEq      ∷ _) ()
parseTypeAtom-NoMuNu (TNeq       ∷ _) ()
parseTypeAtom-NoMuNu (TNewline   ∷ _) ()
parseTypeAtom-NoMuNu (TEOF       ∷ _) ()

-- Parenthesised inner parseType → expect TRParen → return.
parseTypeAtom-NoMuNu (TLParen ∷ rest) eq
  with parseType rest in eqInner
parseTypeAtom-NoMuNu (TLParen ∷ rest) eq
  | just (t , TRParen ∷ rest')
  with eq
... | refl = parseType-NoMuNu rest eqInner

-- TWord clause: dispatch via the 8 keyword `_≟_` chain, mirroring
-- the refactored parseTypeAtom's structure.
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq with name ≟ "Unit"
... | yes _ with eq
...   | refl = nmn-unit
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq | no _ with name ≟ "Void"
... | yes _ with eq
...   | refl = nmn-void
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq | no _ | no _ with name ≟ "Int"
... | yes _ with eq
...   | refl = nmn-int
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq | no _ | no _ | no _ with name ≟ "Float"
... | yes _ with eq
...   | refl = nmn-float
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq | no _ | no _ | no _ | no _ with name ≟ "Buffer"
... | yes _ with eq
...   | refl = nmn-buffer
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq
  | no _ | no _ | no _ | no _ | no _ with name ≟ "String"
... | yes _ with eq
...   | refl = nmn-str
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq
  | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "Eff"
... | yes _ with parseTypeAtom rest in eqA
...   | just (a , rest')
    with parseTypeAtom rest' in eqB
...     | just (b , _)
      with eq
...       | refl = nmn-eff (parseTypeAtom-NoMuNu rest eqA) (parseTypeAtom-NoMuNu rest' eqB)
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "IO"
... | yes _ with parseTypeAtom rest in eqA
...   | just (a , _)
    with eq
...     | refl = nmn-eff nmn-unit (parseTypeAtom-NoMuNu rest eqA)
-- Non-keyword name: tryParseTypeVar returns nothing, absurd.
parseTypeAtom-NoMuNu (TWord name ∷ rest) eq
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  rewrite tryParseTypeVar-nothing name rest with eq
... | ()

------------------------------------------------------------------------
-- parseTypeProdTail
------------------------------------------------------------------------

parseTypeProdTail-NoMuNu left nmnL (TStar ∷ rest) eq
  with parseTypeAtom rest in eqAtom
parseTypeProdTail-NoMuNu left nmnL (TStar ∷ rest) eq
  | just (right , rest') =
  let nmnR = parseTypeAtom-NoMuNu rest eqAtom
  in parseTypeProdTail-NoMuNu (left * right) (nmn-prod nmnL nmnR) rest' eq
parseTypeProdTail-NoMuNu left nmnL (TStar ∷ _) refl | nothing = nmnL
parseTypeProdTail-NoMuNu left nmnL [] refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TLParen    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TRParen    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TLBrace    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TRBrace    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TColon     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TEquals    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TArrow     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TCaret0    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TCaret1    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TCaretW    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TLambda    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TComma     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TSemicolon ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TAt        ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TPipe      ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TDot       ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TPlus      ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TMinus     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TSlash     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TPercent   ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TAmpersand ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TLt        ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TLe        ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TGt        ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TGe        ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TEqEq      ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TNeq       ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TNewline   ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TEOF       ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TWord _    ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TInt _     ∷ _) refl = nmnL
parseTypeProdTail-NoMuNu left nmnL (TString _  ∷ _) refl = nmnL

------------------------------------------------------------------------
-- parseTypeProd
------------------------------------------------------------------------

parseTypeProd-NoMuNu toks eq
  with parseTypeAtom toks in eqAtom
parseTypeProd-NoMuNu toks eq | just (first , rest) =
  parseTypeProdTail-NoMuNu first (parseTypeAtom-NoMuNu toks eqAtom) rest eq

------------------------------------------------------------------------
-- parseTypeSumTail
------------------------------------------------------------------------

parseTypeSumTail-NoMuNu left nmnL (TPlus ∷ rest) eq
  with parseTypeProd rest in eqProd
parseTypeSumTail-NoMuNu left nmnL (TPlus ∷ rest) eq
  | just (right , rest') =
  let nmnR = parseTypeProd-NoMuNu rest eqProd
  in parseTypeSumTail-NoMuNu (left + right) (nmn-sum nmnL nmnR) rest' eq
parseTypeSumTail-NoMuNu left nmnL (TPlus ∷ _) refl | nothing = nmnL
parseTypeSumTail-NoMuNu left nmnL [] refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TLParen    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TRParen    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TLBrace    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TRBrace    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TColon     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TEquals    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TArrow     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TCaret0    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TCaret1    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TCaretW    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TLambda    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TComma     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TSemicolon ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TAt        ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TPipe      ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TDot       ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TStar      ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TMinus     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TSlash     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TPercent   ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TAmpersand ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TLt        ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TLe        ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TGt        ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TGe        ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TEqEq      ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TNeq       ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TNewline   ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TEOF       ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TWord _    ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TInt _     ∷ _) refl = nmnL
parseTypeSumTail-NoMuNu left nmnL (TString _  ∷ _) refl = nmnL

------------------------------------------------------------------------
-- parseTypeSum
------------------------------------------------------------------------

parseTypeSum-NoMuNu toks eq
  with parseTypeProd toks in eqProd
parseTypeSum-NoMuNu toks eq | just (first , rest) =
  parseTypeSumTail-NoMuNu first (parseTypeProd-NoMuNu toks eqProd) rest eq

------------------------------------------------------------------------
-- parseArrowTail: consumes TCaret∷TArrow or TArrow, then parseType.
-- `rewrite` captures `parseType rest` result; we delegate to the IH.
------------------------------------------------------------------------

parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TArrow ∷ rest) eq
  with parseType rest in eqT
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TArrow ∷ rest) refl
  | just (right , _) = nmn-fun nmnL (parseType-NoMuNu rest eqT)
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TArrow ∷ rest) eq
  with parseType rest in eqT
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TArrow ∷ rest) refl
  | just (right , _) = nmn-fun nmnL (parseType-NoMuNu rest eqT)
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TArrow ∷ rest) eq
  with parseType rest in eqT
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TArrow ∷ rest) refl
  | just (right , _) = nmn-fun nmnL (parseType-NoMuNu rest eqT)
-- Grade without arrow: parser rejects. Enumerate via a helper.
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TLParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TRParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TLBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TRBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TColon  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TEquals ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TCaret0 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TCaret1 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TCaretW ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TLambda ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TComma  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TSemicolon ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TAt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TPipe   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TDot    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TPlus   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TMinus  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TStar   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TSlash  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TPercent ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TAmpersand ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TLt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TLe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TGt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TGe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TEqEq   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TNeq    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TNewline ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TEOF    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TWord _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TInt _  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ TString _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret1 ∷ [])     ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TLParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TRParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TLBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TRBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TColon  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TEquals ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TCaret0 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TCaret1 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TCaretW ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TLambda ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TComma  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TSemicolon ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TAt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TPipe   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TDot    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TPlus   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TMinus  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TStar   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TSlash  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TPercent ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TAmpersand ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TLt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TLe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TGt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TGe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TEqEq   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TNeq    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TNewline ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TEOF    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TWord _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TInt _  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ TString _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaret0 ∷ [])     ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TLParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TRParen ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TLBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TRBrace ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TColon  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TEquals ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TCaret0 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TCaret1 ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TCaretW ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TLambda ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TComma  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TSemicolon ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TAt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TPipe   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TDot    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TPlus   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TMinus  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TStar   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TSlash  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TPercent ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TAmpersand ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TLt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TLe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TGt     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TGe     ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TEqEq   ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TNeq    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TNewline ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TEOF    ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TWord _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TInt _  ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ TString _ ∷ _) ()
parseArrowTail-NoMuNu left nmnL (TCaretW ∷ [])     ()
-- Plain TArrow: default to Many.
parseArrowTail-NoMuNu left nmnL (TArrow ∷ rest) eq
  with parseType rest in eqT
parseArrowTail-NoMuNu left nmnL (TArrow ∷ rest) refl
  | just (right , _) = nmn-fun nmnL (parseType-NoMuNu rest eqT)
-- Catchall: no arrow, return left.
parseArrowTail-NoMuNu left nmnL [] refl = nmnL
parseArrowTail-NoMuNu left nmnL (TLParen    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TRParen    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TLBrace    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TRBrace    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TColon     ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TEquals    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TLambda    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TComma     ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TSemicolon ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TAt        ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TPipe      ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TDot       ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TPlus      ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TMinus     ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TStar      ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TSlash     ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TPercent   ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TAmpersand ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TLt        ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TLe        ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TGt        ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TGe        ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TEqEq      ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TNeq       ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TNewline   ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TEOF       ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TWord _    ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TInt _     ∷ _) refl = nmnL
parseArrowTail-NoMuNu left nmnL (TString _  ∷ _) refl = nmnL

------------------------------------------------------------------------
-- parseType
------------------------------------------------------------------------

parseType-NoMuNu toks eq
  with parseTypeSum toks in eqSum
parseType-NoMuNu toks eq | just (left , rest) =
  parseArrowTail-NoMuNu left (parseTypeSum-NoMuNu toks eqSum) rest eq
