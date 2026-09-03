-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Core
--
-- Parser monad and basic combinators for recursive descent parsing.
-- The parser works on a list of tokens and produces results via Maybe.
------------------------------------------------------------------------

module Once.Parser.Core where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)

open import Once.Parser.Token

------------------------------------------------------------------------
-- Parser Type
------------------------------------------------------------------------

-- | A parser consumes tokens and produces a value with remaining tokens.
-- Nothing = parse failure, Just (a, rest) = success.
Parser : Set → Set
Parser A = List Token → Maybe (A × List Token)

------------------------------------------------------------------------
-- Monad Operations
------------------------------------------------------------------------

-- | Always succeeds without consuming input
return : {A : Set} → A → Parser A
return a toks = just (a , toks)

-- | Sequential composition (bind)
_>>=_ : {A B : Set} → Parser A → (A → Parser B) → Parser B
(p >>= f) toks with p toks
... | nothing = nothing
... | just (a , rest) = f a rest

-- | Sequential composition, discard first result
_>>_ : {A B : Set} → Parser A → Parser B → Parser B
p >> q = p >>= λ _ → q

-- | Map over parser result
_<$>_ : {A B : Set} → (A → B) → Parser A → Parser B
(f <$> p) toks with p toks
... | nothing = nothing
... | just (a , rest) = just (f a , rest)

-- | Always fails
fail : {A : Set} → Parser A
fail _ = nothing

-- | Try first parser, if it fails try second (ordered choice)
_<|>_ : {A : Set} → Parser A → Parser A → Parser A
(p <|> q) toks with p toks
... | just result = just result
... | nothing = q toks

infixl 1 _>>=_
infixl 1 _>>_
infixl 3 _<|>_
infixl 4 _<$>_

------------------------------------------------------------------------
-- Basic Combinators
------------------------------------------------------------------------

-- | Consume one token if it satisfies the predicate
satisfy : {A : Set} → (Token → Maybe A) → Parser A
satisfy f [] = nothing
satisfy f (t ∷ ts) with f t
... | just a  = just (a , ts)
... | nothing = nothing

-- | Peek at the next token without consuming
peek : Parser (Maybe Token)
peek [] = just (nothing , [])
peek (t ∷ ts) = just (just t , t ∷ ts)

-- | Consume a specific token or fail
expect : Token → Parser Token
expect _ [] = nothing
expect expected (t ∷ ts) = matchToken expected t ts
  where
  matchToken : Token → Token → List Token → Maybe (Token × List Token)
  matchToken TLParen TLParen rest = just (TLParen , rest)
  matchToken TRParen TRParen rest = just (TRParen , rest)
  matchToken TLBrace TLBrace rest = just (TLBrace , rest)
  matchToken TRBrace TRBrace rest = just (TRBrace , rest)
  matchToken TColon TColon rest = just (TColon , rest)
  matchToken TEquals TEquals rest = just (TEquals , rest)
  matchToken TArrow TArrow rest = just (TArrow , rest)
  matchToken TLambda TLambda rest = just (TLambda , rest)
  matchToken TComma TComma rest = just (TComma , rest)
  matchToken TSemicolon TSemicolon rest = just (TSemicolon , rest)
  matchToken TAt TAt rest = just (TAt , rest)
  matchToken TPipe TPipe rest = just (TPipe , rest)
  matchToken TDot TDot rest = just (TDot , rest)
  matchToken TPlus TPlus rest = just (TPlus , rest)
  matchToken TMinus TMinus rest = just (TMinus , rest)
  matchToken TStar TStar rest = just (TStar , rest)
  matchToken TSlash TSlash rest = just (TSlash , rest)
  matchToken TPercent TPercent rest = just (TPercent , rest)
  matchToken TLt TLt rest = just (TLt , rest)
  matchToken TLe TLe rest = just (TLe , rest)
  matchToken TGt TGt rest = just (TGt , rest)
  matchToken TGe TGe rest = just (TGe , rest)
  matchToken TEqEq TEqEq rest = just (TEqEq , rest)
  matchToken TNeq TNeq rest = just (TNeq , rest)
  matchToken TNewline TNewline rest = just (TNewline , rest)
  matchToken TEOF TEOF rest = just (TEOF , rest)
  matchToken _ _ _ = nothing

-- | Expect a specific keyword/identifier
word : String → Parser String
word w = satisfy check
  where
  check : Token → Maybe String
  check (TWord s) with w ≟ s
  ... | yes _ = just w
  ... | no _  = nothing
  check _ = nothing

-- | Parse any identifier (TWord that is not a reserved word)
anyWord : Parser String
anyWord = satisfy λ where
  (TWord s) → just s
  _ → nothing

-- | Optional: try to parse, return nothing if it fails
optional : {A : Set} → Parser A → Parser (Maybe A)
optional p toks with p toks
... | just (a , rest) = just (just a , rest)
... | nothing = just (nothing , toks)

-- | Skip newlines (zero or more).
-- Specialised to `TNewline` so termination is structurally visible:
-- each successful consumption removes exactly one token from the list.
-- The prior generic `many : Parser A → Parser (List A)` combinator
-- was removed (used only by `skipNewlines`; retaining it required a
-- `TERMINATING` pragma since generic `many p` has no
-- length-bound witness on `p`).
skipNewlines : Parser (List Token)
skipNewlines [] = just ([] , [])
skipNewlines (TNewline ∷ rest) with skipNewlines rest
... | just (ns , rest') = just (TNewline ∷ ns , rest')
... | nothing = just (TNewline ∷ [] , rest)
skipNewlines (t ∷ rest) = just ([] , t ∷ rest)