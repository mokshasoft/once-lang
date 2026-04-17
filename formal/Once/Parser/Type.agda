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
-- The `A^q -> B` form desugars to the graded arrow `A ⇒[ q ] B` internally.
-- Grade annotations are only valid immediately before `->`; using them
-- elsewhere (on the output, inside a product, etc.) is a parse error.
--
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

-- | Try to parse a type variable (uppercase word)
-- NOTE: Type variables are now only used internally during type inference.
-- User-written types should be concrete. This function is kept for
-- backward compatibility but will likely fail at elaboration time.
-- For proper polymorphism support, use PolyType instead.
tryParseTypeVar : String → List Token → Maybe (Type × List Token)
tryParseTypeVar name rest with isUpperWord name
... | true = nothing  -- Type variables not allowed in user-written types
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

-- | Try to parse an arrow continuation, optionally preceded by a grade:
--     `A^1 -> B` → A ⇒[ One ]  B
--     `A^0 -> B` → A ⇒[ Zero ] B
--     `A^w -> B` → A ⇒[ Many ] B
--     `A   -> B` → A ⇒[ Many ] B   (default, unrestricted)
--
-- A grade annotation NOT followed by `->` is a parse error (not silently
-- dropped) — that way `A^1`, `A^1 * B`, etc. fail loudly, making clear
-- that type-level grades are only allowed in argument position on arrows.
parseArrowTail : Type → List Token → Maybe (Type × List Token)
parseArrowTail left (TCaret1 ∷ TArrow ∷ rest) with parseType rest
... | just (right , rest') = just (left ⇒[ One ] right , rest')
... | nothing = nothing
parseArrowTail left (TCaret0 ∷ TArrow ∷ rest) with parseType rest
... | just (right , rest') = just (left ⇒[ Zero ] right , rest')
... | nothing = nothing
parseArrowTail left (TCaretW ∷ TArrow ∷ rest) with parseType rest
... | just (right , rest') = just (left ⇒[ Many ] right , rest')
... | nothing = nothing
-- Grade annotation not followed by `->` → reject (strict error, not a warning).
parseArrowTail left (TCaret1 ∷ _) = nothing
parseArrowTail left (TCaret0 ∷ _) = nothing
parseArrowTail left (TCaretW ∷ _) = nothing
parseArrowTail left (TArrow ∷ rest) with parseType rest
... | just (right , rest') = just (left ⇒[ Many ] right , rest')
... | nothing = nothing
parseArrowTail left toks = just (left , toks)

parseType toks with parseTypeSum toks
... | nothing = nothing
... | just (left , rest) = parseArrowTail left rest