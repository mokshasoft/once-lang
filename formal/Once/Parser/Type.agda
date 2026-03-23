-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Type
--
-- Parser for Once types.
-- Produces Once.Type values directly (no intermediate representation).
--
-- Grammar:
--   Type     ::= TypeSum '->' Type | TypeSum     (right-assoc arrow)
--   TypeSum  ::= TypeProd ('+' TypeProd)*         (left-assoc sum)
--   TypeProd ::= TypeAtom ('*' TypeAtom)*         (left-assoc product)
--   TypeAtom ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
--              | 'Eff' TypeAtom TypeAtom | 'IO' TypeAtom
--              | UpperIdent                       (type variable)
--              | '(' Type ')'
-- Note: Fix removed by OCP-0003. Use μ-type/ν-type for recursive types.
------------------------------------------------------------------------

module Once.Parser.Type where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Char using (isAlpha; isLower)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Eff; TVar; Quantity; Many)
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

-- | Try to parse a type variable (uppercase word)
tryParseTypeVar : String → List Token → Maybe (Type × List Token)
tryParseTypeVar name rest with isUpperWord name
... | true = just (TVar name , rest)
... | false = nothing

-- | Parse a type atom (highest precedence)
{-# TERMINATING #-}
parseTypeAtom : Parser Type

-- | Parse a full type (lowest precedence, entry point)
parseType : Parser Type

-- | Parse type sum level (left-assoc +)
parseTypeSum : Parser Type

-- | Parse type product level (left-assoc *)
parseTypeProd : Parser Type

parseTypeAtom [] = nothing
parseTypeAtom (TWord "Unit" ∷ rest) = just (Unit , rest)
parseTypeAtom (TWord "Void" ∷ rest) = just (Void , rest)
parseTypeAtom (TWord "Int" ∷ rest) = just (Int , rest)
parseTypeAtom (TWord "Float" ∷ rest) = just (Float , rest)
parseTypeAtom (TWord "Buffer" ∷ rest) = just (Buffer , rest)
parseTypeAtom (TWord "String" ∷ rest) = just (Str , rest)
parseTypeAtom (TWord "Eff" ∷ rest) =
  (parseTypeAtom >>= λ a →
   parseTypeAtom >>= λ b →
   return (Eff a b)) rest
parseTypeAtom (TWord "IO" ∷ rest) =
  (parseTypeAtom >>= λ a →
   return (Eff Unit a)) rest
-- Fix removed by OCP-0003: use μ-type/ν-type with structured recursion schemes
parseTypeAtom (TLParen ∷ rest) =
  (parseType >>= λ t →
   expect TRParen >>
   return t) rest
parseTypeAtom (TWord name ∷ rest) = tryParseTypeVar name rest
parseTypeAtom (_ ∷ _) = nothing

------------------------------------------------------------------------
-- Type Product Parser (left-associative *)
------------------------------------------------------------------------

-- | Try to consume a * and parse another atom
tryProdCont : List Token → Maybe (Type × List Token)
tryProdCont (TStar ∷ rest) = parseTypeAtom rest
tryProdCont _ = nothing

-- | Parse continuation of product: ('*' TypeAtom)*
parseTypeProdTail : Type → Parser Type
parseTypeProdTail left toks with tryProdCont toks
... | just (right , rest) = parseTypeProdTail (left Once.Type.* right) rest
... | nothing = just (left , toks)

parseTypeProd toks with parseTypeAtom toks
... | just (first , rest) = parseTypeProdTail first rest
... | nothing = nothing

------------------------------------------------------------------------
-- Type Sum Parser (left-associative +)
------------------------------------------------------------------------

-- | Try to consume a + and parse another product
trySumCont : List Token → Maybe (Type × List Token)
trySumCont (TPlus ∷ rest) = parseTypeProd rest
trySumCont _ = nothing

-- | Parse continuation of sum: ('+' TypeProd)*
parseTypeSumTail : Type → Parser Type
parseTypeSumTail left toks with trySumCont toks
... | just (right , rest) = parseTypeSumTail (left Once.Type.+ right) rest
... | nothing = just (left , toks)

parseTypeSum toks with parseTypeProd toks
... | just (first , rest) = parseTypeSumTail first rest
... | nothing = nothing

------------------------------------------------------------------------
-- Type Arrow Parser (right-associative ->)
------------------------------------------------------------------------

-- | Try to parse an arrow continuation
parseArrowTail : Type → List Token → Maybe (Type × List Token)
parseArrowTail left (TArrow ∷ rest) with parseType rest
... | just (right , rest') = just (left ⇒[ Many ] right , rest')
... | nothing = nothing
parseArrowTail left toks = just (left , toks)

parseType toks with parseTypeSum toks
... | nothing = nothing
... | just (left , rest) = parseArrowTail left rest