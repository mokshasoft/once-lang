-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
                             _*_; _+_; _⇒[_]_; Quantity; Zero; One; Many; mk-kind; pure; eff;
                             Functor; K; Id; _⊕_; _⊗_; μ-type)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.TypeRelation

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

------------------------------------------------------------------------
-- Dec-valued return types: success carries a *derivation* in the
-- corresponding parsing relation, not just a length bound. The bound
-- is recovered on demand via the relation's `ParsesX-shrinks` lemma.
--
-- Plan 0.3 task #40 option 1: by making the parser's success result
-- carry the derivation structurally, soundness is a trivial
-- projection and ParserInvariant (NoMuNu) reduces to structural
-- induction on the derivation.
------------------------------------------------------------------------

ParseAtomD : List Token → Set
ParseAtomD toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesAtom toks T rest)

ParseProdD : List Token → Set
ParseProdD toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesProd toks T rest)

ParseSumD : List Token → Set
ParseSumD toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesSum toks T rest)

ParseTypeD : List Token → Set
ParseTypeD toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesType toks T rest)

ParseProdTailD : Type → List Token → Set
ParseProdTailD left toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesProdTail left toks T rest)

ParseSumTailD : Type → List Token → Set
ParseSumTailD left toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesSumTail left toks T rest)

ParseArrowTailD : Type → List Token → Set
ParseArrowTailD left toks = Maybe (Σ[ T ∈ Type ] Σ[ rest ∈ List Token ] ParsesArrowTail left toks T rest)

-- Functor sub-grammar (body of `Mu`).
ParseFunctorAtomD : List Token → Set
ParseFunctorAtomD toks = Maybe (Σ[ F ∈ Functor ] Σ[ rest ∈ List Token ] ParsesFunctorAtom toks F rest)

ParseFunctorProdD : List Token → Set
ParseFunctorProdD toks = Maybe (Σ[ F ∈ Functor ] Σ[ rest ∈ List Token ] ParsesFunctorProd toks F rest)

ParseFunctorProdTailD : Functor → List Token → Set
ParseFunctorProdTailD left toks = Maybe (Σ[ F ∈ Functor ] Σ[ rest ∈ List Token ] ParsesFunctorProdTail left toks F rest)

ParseFunctorSumD : List Token → Set
ParseFunctorSumD toks = Maybe (Σ[ F ∈ Functor ] Σ[ rest ∈ List Token ] ParsesFunctorSum toks F rest)

ParseFunctorSumTailD : Functor → List Token → Set
ParseFunctorSumTailD left toks = Maybe (Σ[ F ∈ Functor ] Σ[ rest ∈ List Token ] ParsesFunctorSumTail left toks F rest)

------------------------------------------------------------------------
-- Mutual WF parsers
------------------------------------------------------------------------

-- | Parse a type atom (highest precedence)
parseTypeAtomWF : (toks : List Token) → Acc _<_ (length toks) → ParseAtomD toks

-- | Parse a full type (lowest precedence, entry point)
parseTypeWF : (toks : List Token) → Acc _<_ (length toks) → ParseTypeD toks

-- | Parse type sum level (left-assoc +)
parseTypeSumWF : (toks : List Token) → Acc _<_ (length toks) → ParseSumD toks

-- | Parse type product level (left-assoc *)
parseTypeProdWF : (toks : List Token) → Acc _<_ (length toks) → ParseProdD toks

-- | Parse continuation of product: ('*' TypeAtom)*
parseTypeProdTailWF : (left : Type) (toks : List Token)
                  → Acc _<_ (length toks) → ParseProdTailD left toks

-- | Parse continuation of sum: ('+' TypeProd)*
parseTypeSumTailWF : (left : Type) (toks : List Token)
                 → Acc _<_ (length toks) → ParseSumTailD left toks

-- | Parse arrow tail (optional grade + '->' Type), or no-op.
parseArrowTailWF : (left : Type) (toks : List Token)
               → Acc _<_ (length toks) → ParseArrowTailD left toks

-- | Functor sub-grammar parsers (the body of `Mu`).
parseFunctorAtomWF : (toks : List Token) → Acc _<_ (length toks) → ParseFunctorAtomD toks
parseFunctorProdWF : (toks : List Token) → Acc _<_ (length toks) → ParseFunctorProdD toks
parseFunctorProdTailWF : (left : Functor) (toks : List Token)
                       → Acc _<_ (length toks) → ParseFunctorProdTailD left toks
parseFunctorSumWF : (toks : List Token) → Acc _<_ (length toks) → ParseFunctorSumD toks
parseFunctorSumTailWF : (left : Functor) (toks : List Token)
                      → Acc _<_ (length toks) → ParseFunctorSumTailD left toks

-- | Parse `( functor )`: inner functor-sum then TRParen suffix.
parseFunctorAtomWF-TLParen :
  (rest : List Token) → Acc _<_ (length rest)
  → ParseFunctorAtomD (TLParen ∷ rest)

------------------------------------------------------------------------
-- Named helpers for `parseTypeAtomWF`'s consume-and-recurse clauses.
-- Each takes the POST-Acc-destructured sub-Acc directly, so the nested
-- `with parseX …` tree lives in a top-level helper instead of inside
-- parseTypeAtomWF's own `with` chain.
------------------------------------------------------------------------

-- | Parse `( type )`: inner full-type then TRParen suffix.
parseTypeAtomWF-TLParen :
  (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomD (TLParen ∷ rest)

------------------------------------------------------------------------
-- parseTypeAtomWF
------------------------------------------------------------------------

parseTypeAtomWF [] _ = nothing

-- TWord dispatch via decidable string equality.
parseTypeAtomWF (TWord name ∷ rest) _ with name ≟ "Unit"
... | yes refl = just (Unit , rest , pa-unit rest)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ with name ≟ "Void"
... | yes refl = just (Void , rest , pa-void rest)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ with name ≟ "Int"
... | yes refl = just (Int , rest , pa-int rest)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ with name ≟ "Float"
... | yes refl = just (Float , rest , pa-float rest)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ | no _ with name ≟ "Buffer"
... | yes refl = just (Buffer , rest , pa-buffer rest)
parseTypeAtomWF (TWord name ∷ rest) _ | no _ | no _ | no _ | no _ | no _ with name ≟ "String"
... | yes refl = just (Str , rest , pa-string rest)
-- Eff: two successive parseTypeAtomWF calls. WF sub-call Accs derive
-- from `ParsesAtom-shrinks` applied to the earlier sub-derivation.
parseTypeAtomWF (TWord name ∷ rest) (acc rec)
  | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "Eff"
... | yes refl with parseTypeAtomWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (A , rest1 , dA) with parseTypeAtomWF rest1
                                     (rec (<-trans (ParsesAtom-shrinks dA) (s≤s ≤-refl)))
...     | nothing = nothing
...     | just (B , rest2 , dB) = just (A ⇒[ mk-kind Many eff ] B , rest2 , pa-eff dA dB)
-- IO A desugars to Eff Unit A.
parseTypeAtomWF (TWord name ∷ rest) (acc rec)
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "IO"
... | yes refl with parseTypeAtomWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (A , rest1 , dA) = just (Unit ⇒[ mk-kind Many eff ] A , rest1 , pa-io dA)
-- Mu F: parse the functor body (initial algebra).
parseTypeAtomWF (TWord name ∷ rest) (acc rec)
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ with name ≟ "Mu"
... | yes refl with parseFunctorSumWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (F , rest1 , dF) = just (μ-type F , rest1 , pa-mu dF)
-- Non-keyword TWord: no derivation exists.
parseTypeAtomWF (TWord name ∷ rest) _
  | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = nothing

-- TLParen: delegate to the named helper.
parseTypeAtomWF (TLParen ∷ rest) (acc rec) = parseTypeAtomWF-TLParen rest (rec (s≤s ≤-refl))

-- Other tokens: parser fails.
parseTypeAtomWF (TInt _     ∷ _) _ = nothing
-- Plan 0.71: a float literal is no more a type than an integer literal is.
parseTypeAtomWF (TFloat _ _ _ ∷ _) _ = nothing
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
parseTypeAtomWF (TBang      ∷ _) _ = nothing
parseTypeAtomWF (TNewline   ∷ _) _ = nothing
parseTypeAtomWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseTypeAtomWF-TLParen / -Eff / -IO (Acc-neutral helpers)
--
-- Each takes `rest` + Acc on `length rest` directly. The nested
-- `with parseX …` tree lives here instead of inside parseTypeAtomWF's
-- body, so downstream proofs can `with` the helper's result without
-- tangling with Agda's termination checker through nested withs in a
-- mutual Acc-recursive block.
------------------------------------------------------------------------

parseTypeAtomWF-TLParen rest a with parseTypeWF rest a
... | nothing = nothing
... | just (t , TRParen ∷ rest' , dT) = just (t , rest' , pa-paren dT refl)
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
... | just (_ , TBang      ∷ _ , _) = nothing
... | just (_ , TNewline   ∷ _ , _) = nothing
... | just (_ , TEOF       ∷ _ , _) = nothing
... | just (_ , TWord _    ∷ _ , _) = nothing
... | just (_ , TInt _     ∷ _ , _) = nothing
... | just (_ , TFloat _ _ _ ∷ _ , _) = nothing
... | just (_ , TString _  ∷ _ , _) = nothing


------------------------------------------------------------------------
-- parseTypeProdTailWF (left-assoc *)
------------------------------------------------------------------------

parseTypeProdTailWF left [] _ = just (left , [] , ppt-done tt)
  where open import Data.Unit
-- TStar with invalid atom after is a parse ERROR, not a pass-through
-- (same strict choice as before; preserves semantics).
parseTypeProdTailWF left (TStar ∷ rest) (acc rec)
  with parseTypeAtomWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (B , rest' , dB) with parseTypeProdTailWF (left * B) rest'
                                   (rec (<-trans (ParsesAtom-shrinks dB)
                                                 (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (T , rest'' , dTail) = just (T , rest'' , ppt-star dB dTail)

-- No TStar: return (left, toks) unchanged with a `ppt-done` derivation.
parseTypeProdTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TPlus      ∷ rest) _ = just (left , TPlus      ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TBang      ∷ rest) _ = just (left , TBang      ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TFloat i f l ∷ rest) _ = just (left , TFloat i f l ∷ rest , ppt-done tt) where open import Data.Unit
parseTypeProdTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , ppt-done tt) where open import Data.Unit

------------------------------------------------------------------------
-- parseTypeProdWF: Atom + ProdTail
------------------------------------------------------------------------

parseTypeProdWF toks (acc rec) with parseTypeAtomWF toks (acc rec)
... | nothing = nothing
... | just (A , rest , dA) with parseTypeProdTailWF A rest
                                 (rec (ParsesAtom-shrinks dA))
...   | nothing = nothing
...   | just (T , rest' , dTail) = just (T , rest' , pp-mk dA dTail)

------------------------------------------------------------------------
-- parseTypeSumTailWF (left-assoc +)
------------------------------------------------------------------------

parseTypeSumTailWF left [] _ = just (left , [] , pst-done tt)
  where open import Data.Unit
parseTypeSumTailWF left (TPlus ∷ rest) (acc rec)
  with parseTypeProdWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (B , rest' , dB) with parseTypeSumTailWF (left + B) rest'
                                   (rec (<-trans (ParsesProd-shrinks dB)
                                                 (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (T , rest'' , dTail) = just (T , rest'' , pst-plus dB dTail)

parseTypeSumTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TStar      ∷ rest) _ = just (left , TStar      ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TBang      ∷ rest) _ = just (left , TBang      ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TFloat i f l ∷ rest) _ = just (left , TFloat i f l ∷ rest , pst-done tt) where open import Data.Unit
parseTypeSumTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , pst-done tt) where open import Data.Unit

------------------------------------------------------------------------
-- parseTypeSumWF: Prod + SumTail
------------------------------------------------------------------------

parseTypeSumWF toks (acc rec) with parseTypeProdWF toks (acc rec)
... | nothing = nothing
... | just (A , rest , dA) with parseTypeSumTailWF A rest
                                 (rec (ParsesProd-shrinks dA))
...   | nothing = nothing
...   | just (T , rest' , dTail) = just (T , rest' , ps-mk dA dTail)

------------------------------------------------------------------------
-- parseArrowTailWF (right-assoc ->)
------------------------------------------------------------------------

parseArrowTailWF left [] _ = just (left , [] , pat-done tt)
  where open import Data.Unit

-- Grade + arrow: consume 2 tokens, recurse via parseTypeWF.
parseArrowTailWF left (TCaret1 ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (B , rest' , dT) =
      just (left ⇒[ mk-kind One pure ] B , rest' , pat-arrow-g dT)

parseArrowTailWF left (TCaret0 ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (B , rest' , dT) =
      just (left ⇒[ mk-kind Zero pure ] B , rest' , pat-arrow-g dT)

parseArrowTailWF left (TCaretW ∷ TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s (n≤1+n _)))
... | nothing = nothing
... | just (B , rest' , dT) =
      just (left ⇒[ mk-kind Many pure ] B , rest' , pat-arrow-g dT)

-- Grade without arrow: strict reject.
parseArrowTailWF left (TCaret1 ∷ _)           _ = nothing
parseArrowTailWF left (TCaret0 ∷ _)           _ = nothing
parseArrowTailWF left (TCaretW ∷ _)           _ = nothing
-- Plain arrow (no grade, default Many).
parseArrowTailWF left (TArrow ∷ rest) (acc rec)
  with parseTypeWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (B , rest' , dT) =
      just (left ⇒[ mk-kind Many pure ] B , rest' , pat-arrow dT)

-- Any other first token: no consumption.
parseArrowTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TPlus      ∷ rest) _ = just (left , TPlus      ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TStar      ∷ rest) _ = just (left , TStar      ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TBang      ∷ rest) _ = just (left , TBang      ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TFloat i f l ∷ rest) _ = just (left , TFloat i f l ∷ rest , pat-done tt) where open import Data.Unit
parseArrowTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , pat-done tt) where open import Data.Unit

------------------------------------------------------------------------
-- parseTypeWF: Sum + ArrowTail
------------------------------------------------------------------------

parseTypeWF toks (acc rec) with parseTypeSumWF toks (acc rec)
... | nothing = nothing
... | just (A , rest , dS) with parseArrowTailWF A rest
                                 (rec (ParsesSum-shrinks dS))
...   | nothing = nothing
...   | just (T , rest' , dA) = just (T , rest' , pt-mk dS dA)

------------------------------------------------------------------------
-- Functor sub-grammar parsers (body of `Mu`). Mirror the type levels.
------------------------------------------------------------------------

-- fAtom ::= 'Id' | 'K' atom | '(' fSum ')'
parseFunctorAtomWF (TWord name ∷ rest) _ with name ≟ "Id"
... | yes refl = just (Id , rest , pfa-id rest)
parseFunctorAtomWF (TWord name ∷ rest) (acc rec) | no _ with name ≟ "K"
... | yes refl with parseTypeAtomWF rest (rec (s≤s ≤-refl))
...   | nothing = nothing
...   | just (A , rest1 , dA) = just (K A , rest1 , pfa-k dA)
parseFunctorAtomWF (TWord name ∷ rest) _ | no _ | no _ = nothing
parseFunctorAtomWF (TLParen ∷ rest) (acc rec) =
  parseFunctorAtomWF-TLParen rest (rec (s≤s ≤-refl))
-- Any other leading token: not a functor atom.
parseFunctorAtomWF _ _ = nothing

parseFunctorAtomWF-TLParen rest a with parseFunctorSumWF rest a
... | nothing = nothing
... | just (F , TRParen ∷ rest' , dF) = just (F , rest' , pfa-paren dF refl)
... | just (_ , _ , _) = nothing

-- fProd ::= fAtom ('*' fAtom)*
parseFunctorProdWF toks (acc rec) with parseFunctorAtomWF toks (acc rec)
... | nothing = nothing
... | just (A , rest , dA) with parseFunctorProdTailWF A rest
                                 (rec (ParsesFunctorAtom-shrinks dA))
...   | nothing = nothing
...   | just (F , rest' , dTail) = just (F , rest' , pfp-mk dA dTail)

parseFunctorProdTailWF left [] _ = just (left , [] , pfpt-done tt)
  where open import Data.Unit
parseFunctorProdTailWF left (TStar ∷ rest) (acc rec)
  with parseFunctorAtomWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (B , rest' , dB) with parseFunctorProdTailWF (left ⊗ B) rest'
                                   (rec (<-trans (ParsesFunctorAtom-shrinks dB)
                                                 (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (F , rest'' , dTail) = just (F , rest'' , pfpt-star dB dTail)
parseFunctorProdTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TPlus      ∷ rest) _ = just (left , TPlus      ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TBang      ∷ rest) _ = just (left , TBang      ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TFloat i f l ∷ rest) _ = just (left , TFloat i f l ∷ rest , pfpt-done tt) where open import Data.Unit
parseFunctorProdTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , pfpt-done tt) where open import Data.Unit

-- fSum ::= fProd ('+' fProd)*
parseFunctorSumWF toks (acc rec) with parseFunctorProdWF toks (acc rec)
... | nothing = nothing
... | just (A , rest , dA) with parseFunctorSumTailWF A rest
                                 (rec (ParsesFunctorProd-shrinks dA))
...   | nothing = nothing
...   | just (F , rest' , dTail) = just (F , rest' , pfs-mk dA dTail)

parseFunctorSumTailWF left [] _ = just (left , [] , pfst-done tt)
  where open import Data.Unit
parseFunctorSumTailWF left (TPlus ∷ rest) (acc rec)
  with parseFunctorProdWF rest (rec (s≤s ≤-refl))
... | nothing = nothing
... | just (B , rest' , dB) with parseFunctorSumTailWF (left ⊕ B) rest'
                                   (rec (<-trans (ParsesFunctorProd-shrinks dB)
                                                 (s≤s ≤-refl)))
...   | nothing = nothing
...   | just (F , rest'' , dTail) = just (F , rest'' , pfst-plus dB dTail)
parseFunctorSumTailWF left (TLParen    ∷ rest) _ = just (left , TLParen    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TRParen    ∷ rest) _ = just (left , TRParen    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TLBrace    ∷ rest) _ = just (left , TLBrace    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TRBrace    ∷ rest) _ = just (left , TRBrace    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TColon     ∷ rest) _ = just (left , TColon     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TEquals    ∷ rest) _ = just (left , TEquals    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TArrow     ∷ rest) _ = just (left , TArrow     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TCaret0    ∷ rest) _ = just (left , TCaret0    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TCaret1    ∷ rest) _ = just (left , TCaret1    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TCaretW    ∷ rest) _ = just (left , TCaretW    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TLambda    ∷ rest) _ = just (left , TLambda    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TComma     ∷ rest) _ = just (left , TComma     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TSemicolon ∷ rest) _ = just (left , TSemicolon ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TAt        ∷ rest) _ = just (left , TAt        ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TPipe      ∷ rest) _ = just (left , TPipe      ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TDot       ∷ rest) _ = just (left , TDot       ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TMinus     ∷ rest) _ = just (left , TMinus     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TStar      ∷ rest) _ = just (left , TStar      ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TSlash     ∷ rest) _ = just (left , TSlash     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TPercent   ∷ rest) _ = just (left , TPercent   ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TAmpersand ∷ rest) _ = just (left , TAmpersand ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TLt        ∷ rest) _ = just (left , TLt        ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TLe        ∷ rest) _ = just (left , TLe        ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TGt        ∷ rest) _ = just (left , TGt        ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TGe        ∷ rest) _ = just (left , TGe        ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TEqEq      ∷ rest) _ = just (left , TEqEq      ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TNeq       ∷ rest) _ = just (left , TNeq       ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TBang      ∷ rest) _ = just (left , TBang      ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TNewline   ∷ rest) _ = just (left , TNewline   ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TEOF       ∷ rest) _ = just (left , TEOF       ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TWord s    ∷ rest) _ = just (left , TWord s    ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TInt n     ∷ rest) _ = just (left , TInt n     ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TFloat i f l ∷ rest) _ = just (left , TFloat i f l ∷ rest , pfst-done tt) where open import Data.Unit
parseFunctorSumTailWF left (TString s  ∷ rest) _ = just (left , TString s  ∷ rest , pfst-done tt) where open import Data.Unit

------------------------------------------------------------------------
-- Top-level convenience wrapper for external callers.
--
-- `parseType : Parser Type` matches the old `Parser Type` shape.
-- Strips the Σ-bound. Callers in `Once.Parser.Expr`, `Once.Parser.Module`,
-- and `Once.Parser.Tests` use this. Downstream PROOFS
-- (`Once.Grammar.Roundtrip`, `Once.Grammar.ParserInvariant`) thread
-- the Acc explicitly and use the Σ-return directly.
------------------------------------------------------------------------

-- | Strip the derivation from a Dec-valued parser result, recovering
-- the plain `Parser Type` shape. Kept at module scope and with `toks`
-- explicit so downstream bridge lemmas can reference the exact
-- definition used by the wrappers.
stripAtom : (toks : List Token) → ParseAtomD toks → Maybe (Type × List Token)
stripAtom _ nothing = nothing
stripAtom _ (just (t , rest , _)) = just (t , rest)

stripProd : (toks : List Token) → ParseProdD toks → Maybe (Type × List Token)
stripProd _ nothing = nothing
stripProd _ (just (t , rest , _)) = just (t , rest)

stripSum : (toks : List Token) → ParseSumD toks → Maybe (Type × List Token)
stripSum _ nothing = nothing
stripSum _ (just (t , rest , _)) = just (t , rest)

stripType : (toks : List Token) → ParseTypeD toks → Maybe (Type × List Token)
stripType _ nothing = nothing
stripType _ (just (t , rest , _)) = just (t , rest)

stripProdTail : (left : Type) (toks : List Token)
              → ParseProdTailD left toks → Maybe (Type × List Token)
stripProdTail _ _ nothing = nothing
stripProdTail _ _ (just (t , rest , _)) = just (t , rest)

stripSumTail : (left : Type) (toks : List Token)
             → ParseSumTailD left toks → Maybe (Type × List Token)
stripSumTail _ _ nothing = nothing
stripSumTail _ _ (just (t , rest , _)) = just (t , rest)

stripArrowTail : (left : Type) (toks : List Token)
               → ParseArrowTailD left toks → Maybe (Type × List Token)
stripArrowTail _ _ nothing = nothing
stripArrowTail _ _ (just (t , rest , _)) = just (t , rest)

parseType : Parser Type
parseType toks = stripType toks (parseTypeWF toks (<-wellFounded (length toks)))

parseTypeAtom : Parser Type
parseTypeAtom toks = stripAtom toks (parseTypeAtomWF toks (<-wellFounded (length toks)))

parseTypeSum : Parser Type
parseTypeSum toks = stripSum toks (parseTypeSumWF toks (<-wellFounded (length toks)))

parseTypeProd : Parser Type
parseTypeProd toks = stripProd toks (parseTypeProdWF toks (<-wellFounded (length toks)))

parseTypeProdTail : (left : Type) → Parser Type
parseTypeProdTail left toks = stripProdTail left toks (parseTypeProdTailWF left toks (<-wellFounded (length toks)))

parseTypeSumTail : (left : Type) → Parser Type
parseTypeSumTail left toks = stripSumTail left toks (parseTypeSumTailWF left toks (<-wellFounded (length toks)))

parseArrowTail : (left : Type) → Parser Type
parseArrowTail left toks = stripArrowTail left toks (parseArrowTailWF left toks (<-wellFounded (length toks)))
