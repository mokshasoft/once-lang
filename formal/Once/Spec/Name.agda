{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Name — the resolved identity of a definition.
--
-- A `CanonicalName` is a definition's module path followed by its name:
-- `canonical (Cars ∷ All ∷ foo ∷ [])` is `foo` in module `Cars.All`, and a
-- definition of the program's own module is a single component (`own`).
--
-- The categorical generators (`id`, `fst`, `inl`, …) live in a namespace of
-- their own, `Generators`, which no user module can occupy: a user's `fst`
-- and the generator `fst` are different names. The words that name a
-- generator are reserved (`GenWord`).
------------------------------------------------------------------------

module Once.Spec.Name where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.String using (String)
import Data.String as String
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record CanonicalName : Set where
  constructor canonical
  field parts : List String

-- A one-component name.
bare : String → CanonicalName
bare s = canonical (s ∷ [])

-- The generator `g`. A pattern, so that it can index a rule and be matched on.
pattern gen g = canonical ("Generators" ∷ g ∷ [])

-- A definition of the program's own module.
pattern own x = canonical (x ∷ [])

-- The reserved words: every generator name, including those that are only
-- ever applied. A definition with one of these names is reached as `name@this`.
genWords : List String
genWords = "id" ∷ "fst" ∷ "snd" ∷ "inl" ∷ "inr" ∷ "unit" ∷ "pair" ∷ "terminal"
         ∷ "initial" ∷ "curry" ∷ "apply" ∷ "compose" ∷ "case" ∷ "cata" ∷ "ana"
         ∷ "In" ∷ "Out" ∷ []

GenWord : String → Set
GenWord x = Any (x ≡_) genWords

-- The eight generators that are names (the others are only applied).
genNames : List String
genNames = "id" ∷ "fst" ∷ "snd" ∷ "terminal" ∷ "initial" ∷ "inl" ∷ "inr" ∷ "unit" ∷ []

-- `cn` is none of the eight.
NotGenerator : CanonicalName → Set
NotGenerator cn = All (λ g → cn ≢ gen g) genNames

-- The dotted form, used as an external operation's key.
showCanonical : CanonicalName → String
showCanonical (canonical [])        = ""
showCanonical (canonical (x ∷ []))  = x
{-# CATCHALL #-}
showCanonical (canonical (x ∷ xs))  = x String.++ "." String.++ showCanonical (canonical xs)
