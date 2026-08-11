-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Tests
--
-- Plan 0.3, gap G1 (partial): machine-checked parser behaviour on
-- canonical token inputs. Each theorem documents a specific input
-- shape the parser must accept (or reject) with the expected result.
--
-- These are smoke tests, not general properties — they complement
-- the round-trip claims in `Once.Grammar.Printer` and the grammar-
-- conformance theorem in `Once.Grammar.Convert`.
------------------------------------------------------------------------

module Once.Parser.Tests where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; mk-kind; pure; eff;
                             Zero; One; Many)
open import Once.Parser.Token
open import Once.Parser.Type using (parseType)

------------------------------------------------------------------------
-- Empty input rejection
------------------------------------------------------------------------

parseType-empty-fails : parseType [] ≡ nothing
parseType-empty-fails = refl

------------------------------------------------------------------------
-- Base types: parseType accepts every keyword-token atom
------------------------------------------------------------------------

parseType-Unit   : parseType (TWord "Unit" ∷ []) ≡ just (Unit   , [])
parseType-Unit   = refl

parseType-Void   : parseType (TWord "Void" ∷ []) ≡ just (Void   , [])
parseType-Void   = refl

parseType-Int    : parseType (TWord "Int" ∷ []) ≡ just (Int    , [])
parseType-Int    = refl

parseType-Float  : parseType (TWord "Float" ∷ []) ≡ just (Float  , [])
parseType-Float  = refl

parseType-Buffer : parseType (TWord "Buffer" ∷ []) ≡ just (Buffer , [])
parseType-Buffer = refl

parseType-String : parseType (TWord "String" ∷ []) ≡ just (Str    , [])
parseType-String = refl

------------------------------------------------------------------------
-- Leftover-tokens behaviour
------------------------------------------------------------------------

parseType-Unit-leftover :
  parseType (TWord "Unit" ∷ TRParen ∷ TArrow ∷ [])
    ≡ just (Unit , TRParen ∷ TArrow ∷ [])
parseType-Unit-leftover = refl

------------------------------------------------------------------------
-- Product and sum
------------------------------------------------------------------------

parseType-Unit*Int :
  parseType (TWord "Unit" ∷ TStar ∷ TWord "Int" ∷ [])
    ≡ just (Unit * Int , [])
parseType-Unit*Int = refl

parseType-Int+Str :
  parseType (TWord "Int" ∷ TPlus ∷ TWord "String" ∷ [])
    ≡ just (Int + Str , [])
parseType-Int+Str = refl

------------------------------------------------------------------------
-- Arrow grades: all three quantity annotations round-trip to the
-- expected graded function type.
------------------------------------------------------------------------

parseType-Int⇒Int-default :
  parseType (TWord "Int" ∷ TArrow ∷ TWord "Int" ∷ [])
    ≡ just (Int ⇒[ mk-kind Many pure ] Int , [])
parseType-Int⇒Int-default = refl

parseType-Int-linear-Int :
  parseType (TWord "Int" ∷ TCaret1 ∷ TArrow ∷ TWord "Int" ∷ [])
    ≡ just (Int ⇒[ mk-kind One pure ] Int , [])
parseType-Int-linear-Int = refl

parseType-Int-erased-Unit :
  parseType (TWord "Int" ∷ TCaret0 ∷ TArrow ∷ TWord "Unit" ∷ [])
    ≡ just (Int ⇒[ mk-kind Zero pure ] Unit , [])
parseType-Int-erased-Unit = refl

------------------------------------------------------------------------
-- Paren-wrapped
------------------------------------------------------------------------

parseType-paren-Int :
  parseType (TLParen ∷ TWord "Int" ∷ TRParen ∷ [])
    ≡ just (Int , [])
parseType-paren-Int = refl

------------------------------------------------------------------------
-- Non-matching input: the parser rejects.
------------------------------------------------------------------------

parseType-arrow-alone : parseType (TArrow ∷ []) ≡ nothing
parseType-arrow-alone = refl

parseType-star-alone : parseType (TStar ∷ []) ≡ nothing
parseType-star-alone = refl
