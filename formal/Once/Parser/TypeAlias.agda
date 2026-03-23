-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
                             _*_; _+_; _⇒[_]_; Eff; TVar;
                             Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type)

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
-- Type Substitution
------------------------------------------------------------------------

-- | Substitute a type variable with a type
mutual
  substTVarF : String → Type → Functor → Functor
  substTVarF name rep (K A) = K (substTVar name rep A)
  substTVarF _ _ Id = Id
  substTVarF name rep (F ⊕ G) = substTVarF name rep F ⊕ substTVarF name rep G
  substTVarF name rep (F ⊗ G) = substTVarF name rep F ⊗ substTVarF name rep G

  substTVar : String → Type → Type → Type
  substTVar name replacement (TVar v) with name ≟ v
  ... | yes _ = replacement
  ... | no _  = TVar v
  substTVar _ _ Unit = Unit
  substTVar _ _ Void = Void
  substTVar _ _ Int = Int
  substTVar _ _ Float = Float
  substTVar _ _ Buffer = Buffer
  substTVar _ _ Str = Str
  substTVar name rep (a * b) = substTVar name rep a * substTVar name rep b
  substTVar name rep (a + b) = substTVar name rep a + substTVar name rep b
  substTVar name rep (a ⇒[ q ] b) = substTVar name rep a ⇒[ q ] substTVar name rep b
  substTVar name rep (Eff a b) = Eff (substTVar name rep a) (substTVar name rep b)
  substTVar name rep (μ-type F) = μ-type (substTVarF name rep F)
  substTVar name rep (ν-type F) = ν-type (substTVarF name rep F)

-- | Apply multiple substitutions (params zipped with args)
applySubsts : List (String × Type) → Type → Type
applySubsts [] body = body
applySubsts ((name , arg) ∷ rest) body = applySubsts rest (substTVar name arg body)

------------------------------------------------------------------------
-- Alias Expansion
------------------------------------------------------------------------

-- | Expand type aliases in a type (single pass)
{-# TERMINATING #-}
mutual
  expandAliasesF : TypeAliasEnv → Functor → Functor
  expandAliasesF env (K A) = K (expandAliases env A)
  expandAliasesF _ Id = Id
  expandAliasesF env (F ⊕ G) = expandAliasesF env F ⊕ expandAliasesF env G
  expandAliasesF env (F ⊗ G) = expandAliasesF env F ⊗ expandAliasesF env G

  expandAliases : TypeAliasEnv → Type → Type
  expandAliases env (TVar name) with lookupAlias name env
  ... | just ([] , body) = expandAliases env body  -- nullary alias
  ... | _ = TVar name  -- not an alias or has params (need args)
  expandAliases _ Unit = Unit
  expandAliases _ Void = Void
  expandAliases _ Int = Int
  expandAliases _ Float = Float
  expandAliases _ Buffer = Buffer
  expandAliases _ Str = Str
  expandAliases env (a * b) = expandAliases env a * expandAliases env b
  expandAliases env (a + b) = expandAliases env a + expandAliases env b
  expandAliases env (a ⇒[ q ] b) = expandAliases env a ⇒[ q ] expandAliases env b
  expandAliases env (Eff a b) = Eff (expandAliases env a) (expandAliases env b)
  expandAliases env (μ-type F) = μ-type (expandAliasesF env F)
  expandAliases env (ν-type F) = ν-type (expandAliasesF env F)