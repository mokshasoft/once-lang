-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Type
--
-- Parser for Once types.
-- Produces Once.Type values directly (no intermediate representation).
--
-- Grammar:
--   Type     ::= TypeSum ArrowTail | TypeSum                  (right-assoc arrow)
--   ArrowTail ::= GradeAnn? '->' Type
--   GradeAnn  ::= '^1' | '^0' | '^w'                          (QTT argument grade)
--   TypeSum  ::= TypeProd ('+' TypeProd)*                     (left-assoc sum)
--   TypeProd ::= TypeAtom ('*' TypeAtom)*                     (left-assoc product)
--   TypeAtom ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
--              | 'Eff' TypeAtom TypeAtom | 'IO' TypeAtom
--              | UpperIdent                                   (type variable)
--              | '(' Type ')'
--
-- Termination: well-founded recursion on `length toks`. Every parser
-- carries an `Acc _<_ (length toks)` argument and returns a Σ-packaged
-- result that includes a length-bound witness. Per plan 0.3 task #40.
--
-- External callers use `parseType : Parser Type` (the top-level
-- wrapper at the end of this file) which forgets the length bound.
-- The WF-indexed entry points (parseTypeWF, parseTypeAtomWF, …) are
-- available for proof contexts that need the length-bound Σ-return.
------------------------------------------------------------------------

module Once.Parser.Type where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Char using (isAlpha; isLower)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans;
                                        ≤-<-trans; <-≤-trans;
                                        n<1+n; m≤n⇒m≤1+n; ≤-step;
                                        n≤1+n; <⇒≤)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Eff; Quantity; Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.Core

------------------------------------------------------------------------
-- Type Atom Parser
------------------------------------------------------------------------

-- | Check if a word starts with an uppercase letter (type variable)
isUpperWord : String → Bool
isUpperWord s with Data.String.toList s
... | [] = false
... | (c ∷ _) = isAlpha c ∧ not (isLower c)

-- | Try to parse a type variable (uppercase word).
-- Per 0.2.5: user-written types are concrete; type variables live only
-- inside `PolyType` signatures. This function always returns `nothing`.
tryParseTypeVar : String → List Token → Maybe (Type × List Token)
tryParseTypeVar _ _ = nothing

------------------------------------------------------------------------
-- Length-bounded result types
--
-- ParseT< : strict decrease (level parsers that always consume on
--   success — parseTypeAtomWF, parseTypeWF, parseTypeSumWF, parseTypeProdWF).
-- ParseT≤ : non-strict (tail parsers that may no-op — parseTypeProdTailWF,
--   parseTypeSumTailWF, parseArrowTailWF).
--
-- Return Σ-types instead of plain `Maybe (Type × List Token)` so the
-- length bound is threaded structurally, allowing the Eff case's
-- second parseTypeAtomWF call to derive its Acc input.
------------------------------------------------------------------------

ParseT< : List Token → Set
ParseT< toks = Maybe (Σ[ t ∈ Type ] Σ[ rest ∈ List Token ] length rest < length toks)

ParseT≤ : List Token → Set
ParseT≤ toks = Maybe (Σ[ t ∈ Type ] Σ[ rest ∈ List Token ] length rest ≤ length toks)

-- | Lift a ParseT< to ParseT≤ (strict < implies non-strict ≤).
weakenBound : ∀ {toks} → ParseT< toks → ParseT≤ toks
weakenBound nothing = nothing
weakenBound (just (t , rest , bound)) = just (t , rest , <⇒≤ bound)

------------------------------------------------------------------------
-- Mutual WF parsers
------------------------------------------------------------------------

-- | Parse a type atom (highest precedence)
parseTypeAtomWF : (toks : List Token) → Acc _<_ (length toks) → ParseT< toks

-- | Parse a full type (lowest precedence, entry point)
parseTypeWF : (toks : List Token) → Acc _<_ (length toks) → ParseT< toks

-- | Parse type sum level (left-assoc +)
parseTypeSumWF : (toks : List Token) → Acc _<_ (length toks) → ParseT< toks

-- | Parse type product level (left-assoc *)
parseTypeProdWF : (toks : List Token) → Acc _<_ (length toks) → ParseT< toks

-- | Parse continuation of product: ('*' TypeAtom)*
parseTypeProdTailWF : (left : Type) (toks : List Token)
                  → Acc _<_ (length toks) → ParseT≤ toks

-- | Parse continuation of sum: ('+' TypeProd)*
parseTypeSumTailWF : (left : Type) (toks : List Token)
                 → Acc _<_ (length toks) → ParseT≤ toks

-- | Parse arrow tail (optional grade + '->' Type), or no-op.
parseArrowTailWF : (left : Type) (toks : List Token)
               → Acc _<_ (length toks) → ParseT≤ toks

------------------------------------------------------------------------
-- parseTypeAtomWF
------------------------------------------------------------------------

parseTypeAtomWF [] _ = nothing

-- TWord dispatch via decidable string equality.
parseTypeAtomWF (TWord name ∷ rest) _ with name ≟ "Unit"
... | yes _ = just (Unit , rest , s≤s ≤-refl)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ with name ≟ "Void"
... | yes _ = just (Void , rest , s≤s ≤-refl)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ with name ≟ "Int"
... | yes _ = just (Int , rest , s≤s ≤-refl)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ with name ≟ "Float"
... | yes _ = just (Float , rest , s≤s ≤-refl)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ | no _ with name ≟ "Buffer"
... | yes _ = just (Buffer , rest , s≤s ≤-refl)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ | no _ | no _ with name ≟ "String"
... | yes _ = just (Str , rest , s≤s ≤-refl)
-- Eff: two successive parseTypeAtomWF calls; use Σ-bounds for the
-- second Acc derivation.
parseTypeAtomWF (TWord name ∷ rest) (acc rec)
  | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "Eff"
... | yes _ with parseTypeAtomWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (a , rest1 , bound1) with parseTypeAtomWF rest1
                                         (rec (<-trans bound1 (s≤s ≤-refl)))
...     | nothing = nothing
...     | just (b , rest2 , bound2) =
          just (Eff a b , rest2 ,
                <-trans bound2 (<-trans bound1 (s≤s ≤-refl)))
-- IO A desugars to Eff Unit A
parseTypeAtomWF (TWord name ∷ rest) (acc rec)
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "IO"
... | yes _ with parseTypeAtomWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (a , rest1 , bound1) =
        just (Eff Unit a , rest1 , <-trans bound1 (s≤s ≤-refl))
-- Non-keyword TWord: tryParseTypeVar returns nothing always.
parseTypeAtomWF (TWord name ∷ rest) _
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = nothing

-- TLParen: inner parseTypeWF + expect TRParen.
parseTypeAtomWF (TLParen ∷ rest) (acc rec) with parseTypeWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (t , TRParen ∷ rest' , bound) =
      just (t , rest' , <-trans (s≤s ≤-refl) (<-trans bound (s≤s ≤-refl)))
-- After `just (t , rest' , bound)`, rest' wasn't `TRParen ∷ _` → fail.
... | just (_ , [] , _) = nothing
... | just (_ , TLParen    ∷ _ , _) = nothing
... | just (_ , TLBrace    ∷ _ , _) = nothing
... | just (_ , TRBrace    ∷ _ , _) = nothing
... | just (_ , TColon     ∷ _ , _) = nothing
... | just (_ , TEquals    ∷ _ , _) = nothing
... | just (_ , TArrow     ∷ _ , _) = nothing
... | just (_ , TCaret0    ∷ _ , _) = nothing
... | just (_ , TCaret1    ∷ _ , _) = nothing
... | just (_ , TCaretW    ∷ _ , _) = nothing
... | just (_ , TLambda    ∷ _ , _) = nothing
... | just (_ , TComma     ∷ _ , _) = nothing
... | just (_ , TSemicolon ∷ _ , _) = nothing
... | just (_ , TAt        ∷ _ , _) = nothing
... | just (_ , TPipe      ∷ _ , _) = nothing
... | just (_ , TDot       ∷ _ , _) = nothing
... | just (_ , TPlus      ∷ _ , _) = nothing
... | just (_ , TMinus     ∷ _ , _) = nothing
... | just (_ , TStar      ∷ _ , _) = nothing
... | just (_ , TSlash     ∷ _ , _) = nothing
... | just (_ , TPercent   ∷ _ , _) = nothing
... | just (_ , TAmpersand ∷ _ , _) = nothing
... | just (_ , TLt        ∷ _ , _) = nothing
... | just (_ , TLe        ∷ _ , _) = nothing
... | just (_ , TGt        ∷ _ , _) = nothing
... | just (_ , TGe        ∷ _ , _) = nothing
... | just (_ , TEqEq      ∷ _ , _) = nothing
... | just (_ , TNeq       ∷ _ , _) = nothing
... | just (_ , TNewline   ∷ _ , _) = nothing
... | just (_ , TEOF       ∷ _ , _) = nothing
... | just (_ , TWord _    ∷ _ , _) = nothing
... | just (_ , TInt _     ∷ _ , _) = nothing
... | just (_ , TString _  ∷ _ , _) = nothing

-- Other tokens: parser fails.
parseTypeAtomWF (TInt _     ∷ _) _ = nothing
parseTypeAtomWF (TString _  ∷ _) _ = nothing
parseTypeAtomWF (TRParen    ∷ _) _ = nothing
parseTypeAtomWF (TLBrace    ∷ _) _ = nothing
parseTypeAtomWF (TRBrace    ∷ _) _ = nothing
parseTypeAtomWF (TColon     ∷ _) _ = nothing
parseTypeAtomWF (TEquals    ∷ _) _ = nothing
parseTypeAtomWF (TArrow     ∷ _) _ = nothing
parseTypeAtomWF (TCaret0    ∷ _) _ = nothing
parseTypeAtomWF (TCaret1    ∷ _) _ = nothing
parseTypeAtomWF (TCaretW    ∷ _) _ = nothing
parseTypeAtomWF (TLambda    ∷ _) _ = nothing
parseTypeAtomWF (TComma     ∷ _) _ = nothing
parseTypeAtomWF (TSemicolon ∷ _) _ = nothing
parseTypeAtomWF (TAt        ∷ _) _ = nothing
parseTypeAtomWF (TPipe      ∷ _) _ = nothing
parseTypeAtomWF (TDot       ∷ _) _ = nothing
parseTypeAtomWF (TPlus      ∷ _) _ = nothing
parseTypeAtomWF (TMinus     ∷ _) _ = nothing
parseTypeAtomWF (TStar      ∷ _) _ = nothing
parseTypeAtomWF (TSlash     ∷ _) _ = nothing
parseTypeAtomWF (TPercent   ∷ _) _ = nothing
parseTypeAtomWF (TAmpersand ∷ _) _ = nothing
parseTypeAtomWF (TLt        ∷ _) _ = nothing
parseTypeAtomWF (TLe        ∷ _) _ = nothing
parseTypeAtomWF (TGt        ∷ _) _ = nothing
parseTypeAtomWF (TGe        ∷ _) _ = nothing
parseTypeAtomWF (TEqEq      ∷ _) _ = nothing
parseTypeAtomWF (TNeq       ∷ _) _ = nothing
parseTypeAtomWF (TNewline   ∷ _) _ = nothing
parseTypeAtomWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseTypeProdTailWF (left-assoc *)
------------------------------------------------------------------------

parseTypeProdTailWF left [] _ = just (left , [] , ≤-refl)
parseTypeProdTailWF left (TStar ∷ rest) (acc rec)
  with parseTypeAtomWF rest (rec (s≤s ≤-refl))
... | nothing = just (left , TStar ∷ rest , ≤-refl)
... | just (right , rest' , bound') with parseTypeProdTailWF (left * right) rest'
                                          (rec (<-trans bound' (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (t , rest'' , bound'') =
        just (t , rest'' ,
              <⇒≤ (≤-trans (s≤s bound'')
                                               (<-trans bound' (s≤s ≤-refl))))

-- No TStar: return (left, toks) unchanged.
parseTypeProdTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , ≤-refl)
parseTypeProdTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , ≤-refl)
parseTypeProdTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , ≤-refl)
parseTypeProdTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , ≤-refl)
parseTypeProdTailWF left (TPlus      ∷ rest) _ = just (left , TPlus      ∷ rest , ≤-refl)
parseTypeProdTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , ≤-refl)
parseTypeProdTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , ≤-refl)
parseTypeProdTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , ≤-refl)
parseTypeProdTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , ≤-refl)
parseTypeProdTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , ≤-refl)
parseTypeProdTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , ≤-refl)
parseTypeProdTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , ≤-refl)
parseTypeProdTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , ≤-refl)
parseTypeProdTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , ≤-refl)
parseTypeProdTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , ≤-refl)
parseTypeProdTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , ≤-refl)
parseTypeProdTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , ≤-refl)
parseTypeProdTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , ≤-refl)

------------------------------------------------------------------------
-- parseTypeProdWF: Atom + ProdTail
------------------------------------------------------------------------

parseTypeProdWF toks (acc rec) with parseTypeAtomWF toks (acc rec)
... | nothing = nothing
... | just (first , rest , bound) with parseTypeProdTailWF first rest
                                        (rec bound)
...   | nothing = nothing
...   | just (t , rest' , boundT) =
        just (t , rest' , ≤-<-trans boundT bound)

------------------------------------------------------------------------
-- parseTypeSumTailWF (left-assoc +)
------------------------------------------------------------------------

parseTypeSumTailWF left [] _ = just (left , [] , ≤-refl)
parseTypeSumTailWF left (TPlus ∷ rest) (acc rec)
  with parseTypeProdWF rest (rec (s≤s ≤-refl))
... | nothing = just (left , TPlus ∷ rest , ≤-refl)
... | just (right , rest' , bound') with parseTypeSumTailWF (left + right) rest'
                                          (rec (<-trans bound' (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (t , rest'' , bound'') =
        just (t , rest'' ,
              <⇒≤ (≤-trans (s≤s bound'')
                                               (<-trans bound' (s≤s ≤-refl))))

parseTypeSumTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , ≤-refl)
parseTypeSumTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , ≤-refl)
parseTypeSumTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , ≤-refl)
parseTypeSumTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , ≤-refl)
parseTypeSumTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TStar      ∷ rest) _ = just (left , TStar      ∷ rest , ≤-refl)
parseTypeSumTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , ≤-refl)
parseTypeSumTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , ≤-refl)
parseTypeSumTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , ≤-refl)
parseTypeSumTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , ≤-refl)
parseTypeSumTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , ≤-refl)
parseTypeSumTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , ≤-refl)
parseTypeSumTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , ≤-refl)
parseTypeSumTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , ≤-refl)
parseTypeSumTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , ≤-refl)
parseTypeSumTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , ≤-refl)
parseTypeSumTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , ≤-refl)
parseTypeSumTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , ≤-refl)
parseTypeSumTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , ≤-refl)

------------------------------------------------------------------------
-- parseTypeSumWF: Prod + SumTail
------------------------------------------------------------------------

parseTypeSumWF toks (acc rec) with parseTypeProdWF toks (acc rec)
... | nothing = nothing
... | just (first , rest , bound) with parseTypeSumTailWF first rest
                                        (rec bound)
...   | nothing = nothing
...   | just (t , rest' , boundT) =
        just (t , rest' , ≤-<-trans boundT bound)

------------------------------------------------------------------------
-- parseArrowTailWF (right-assoc ->)
------------------------------------------------------------------------

parseArrowTailWF left [] _ = just (left , [] , ≤-refl)

-- Grade + arrow: consume 2 tokens, recurse via parseTypeWF.
parseArrowTailWF left (TCaret1 ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (right , rest' , bound) =
      just (left ⇒[ One ] right , rest' ,
            <⇒≤ (<-trans bound (s≤s (n≤1+n _))))

parseArrowTailWF left (TCaret0 ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (right , rest' , bound) =
      just (left ⇒[ Zero ] right , rest' ,
            <⇒≤ (<-trans bound (s≤s (n≤1+n _))))

parseArrowTailWF left (TCaretW ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (right , rest' , bound) =
      just (left ⇒[ Many ] right , rest' ,
            <⇒≤ (<-trans bound (s≤s (n≤1+n _))))

-- Grade without arrow: strict reject.
parseArrowTailWF left (TCaret1 ∷ _)           _ = nothing
parseArrowTailWF left (TCaret0 ∷ _)           _ = nothing
parseArrowTailWF left (TCaretW ∷ _)           _ = nothing
-- Plain arrow (no grade, default Many).
parseArrowTailWF left (TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (right , rest' , bound) =
      just (left ⇒[ Many ] right , rest' ,
            <⇒≤ (<-trans bound (s≤s ≤-refl)))

-- Any other first token: no consumption.
parseArrowTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , ≤-refl)
parseArrowTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , ≤-refl)
parseArrowTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , ≤-refl)
parseArrowTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , ≤-refl)
parseArrowTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , ≤-refl)
parseArrowTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , ≤-refl)
parseArrowTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , ≤-refl)
parseArrowTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , ≤-refl)
parseArrowTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , ≤-refl)
parseArrowTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , ≤-refl)
parseArrowTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , ≤-refl)
parseArrowTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , ≤-refl)
parseArrowTailWF left (TPlus      ∷ rest) _ = just (left , TPlus      ∷ rest , ≤-refl)
parseArrowTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , ≤-refl)
parseArrowTailWF left (TStar      ∷ rest) _ = just (left , TStar      ∷ rest , ≤-refl)
parseArrowTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , ≤-refl)
parseArrowTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , ≤-refl)
parseArrowTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , ≤-refl)
parseArrowTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , ≤-refl)
parseArrowTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , ≤-refl)
parseArrowTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , ≤-refl)
parseArrowTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , ≤-refl)
parseArrowTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , ≤-refl)
parseArrowTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , ≤-refl)
parseArrowTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , ≤-refl)
parseArrowTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , ≤-refl)
parseArrowTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , ≤-refl)
parseArrowTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , ≤-refl)
parseArrowTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , ≤-refl)

------------------------------------------------------------------------
-- parseTypeWF: Sum + ArrowTail
------------------------------------------------------------------------

parseTypeWF toks (acc rec) with parseTypeSumWF toks (acc rec)
... | nothing = nothing
... | just (first , rest , bound) with parseArrowTailWF first rest
                                        (rec bound)
...   | nothing = nothing
...   | just (t , rest' , boundT) =
        just (t , rest' , ≤-<-trans boundT bound)

------------------------------------------------------------------------
-- Top-level convenience wrapper for external callers.
--
-- `parseType : Parser Type` matches the old `Parser Type` shape.
-- Strips the Σ-bound. Callers in `Once.Parser.Expr`, `Once.Parser.Module`,
-- and `Once.Parser.Tests` use this. Downstream PROOFS
-- (`Once.Grammar.Roundtrip`, `Once.Grammar.ParserInvariant`) thread
-- the Acc explicitly and use the Σ-return directly.
------------------------------------------------------------------------

parseType : Parser Type
parseType toks with parseTypeWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseTypeAtom : Parser Type
parseTypeAtom toks with parseTypeAtomWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseTypeSum : Parser Type
parseTypeSum toks with parseTypeSumWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseTypeProd : Parser Type
parseTypeProd toks with parseTypeProdWF toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseTypeProdTail : (left : Type) → Parser Type
parseTypeProdTail left toks with parseTypeProdTailWF left toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseTypeSumTail : (left : Type) → Parser Type
parseTypeSumTail left toks with parseTypeSumTailWF left toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)

parseArrowTail : (left : Type) → Parser Type
parseArrowTail left toks with parseArrowTailWF left toks (<-wellFounded (length toks))
... | nothing = nothing
... | just (t , rest , _) = just (t , rest)
