-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.TypeAlias
--
-- Type alias expansion.
-- Substitutes type alias references with their definitions.
------------------------------------------------------------------------

module Once.Parser.TypeAlias where

open import Data.List using (List; []; _∷_; length; zip)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (yes; no)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_;
                             Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type)
-- TVar removed: Type variables only exist in PolyType (for type inference).
-- User-written types must be concrete. Type aliases without parameters
-- are still supported via name lookup in the alias environment.

------------------------------------------------------------------------
-- Type Alias Environment
------------------------------------------------------------------------

-- | A type alias: name, parameters, body
-- Example: type Pair A B = A * B
--   → ("Pair", ["A", "B"], A * B)
TypeAlias : Set
TypeAlias = String × List String × Type

TypeAliasEnv : Set
TypeAliasEnv = List TypeAlias

-- | Look up a type alias by name
lookupAlias : String → TypeAliasEnv → Maybe (List String × Type)
lookupAlias _ [] = nothing
lookupAlias name ((n , params , body) ∷ rest) with name ≟ n
... | yes _ = just (params , body)
... | no _  = lookupAlias name rest

------------------------------------------------------------------------
-- Type Substitution (Simplified)
------------------------------------------------------------------------

-- Note: Type variable substitution was removed because TVar is no longer
-- part of Type (only PolyType). User-written types must be concrete.
-- Parametric type aliases are not currently supported.
-- If needed in the future, parametric aliases should use PolyType.

------------------------------------------------------------------------
-- Alias Expansion (Simplified)
------------------------------------------------------------------------

-- Note: Since TVar is no longer in Type, type aliases cannot be
-- referenced in user-written types. Alias expansion is now a no-op.
-- For proper type alias support, the parser would need to directly
-- recognize alias names and expand them during parsing.

-- | Expand type aliases in a type (currently a no-op)
mutual
  expandAliasesF : TypeAliasEnv → Functor → Functor
  expandAliasesF env (K A) = K (expandAliases env A)
  expandAliasesF _ Id = Id
  expandAliasesF env (F ⊕ G) = expandAliasesF env F ⊕ expandAliasesF env G
  expandAliasesF env (F ⊗ G) = expandAliasesF env F ⊗ expandAliasesF env G

  expandAliases : TypeAliasEnv → Type → Type
  expandAliases _ Unit = Unit
  expandAliases _ Void = Void
  expandAliases _ Int = Int
  expandAliases _ Float = Float
  expandAliases _ Buffer = Buffer
  expandAliases _ Str = Str
  expandAliases env (a * b) = expandAliases env a * expandAliases env b
  expandAliases env (a + b) = expandAliases env a + expandAliases env b
  expandAliases env (a ⇒[ k ] b) = expandAliases env a ⇒[ k ] expandAliases env b
  expandAliases env (μ-type F) = μ-type (expandAliasesF env F)
  expandAliases env (ν-type F) = ν-type (expandAliasesF env F)