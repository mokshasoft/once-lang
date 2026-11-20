{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Syntax — what a programmer writes, as a tree.
--
-- A module is a list of declarations: imports, type aliases, signatures of
-- the operations it is compiled against, type signatures and definitions.
-- An expression names variables by string; a reference to something global
-- is RESOLVED (`Spec.Surface.Resolution`) to the canonical name it denotes,
-- or to the generator it names. A type in a signature is a type as written
-- (`Spec.Surface.Type`); an annotation is a ground type.
------------------------------------------------------------------------

module Once.Spec.Surface.Syntax where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type using (Type)
open import Once.Spec.Float.Value using (Sign)
open import Once.Spec.Surface.Operator using (BinOp)
open import Once.Spec.Surface.Generators using (Gen)
open import Once.Spec.Surface.Type using (PolyType)

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

data Expr : Set where
  RVar       : String → Expr                       -- x
  RQualified : String → String → Expr              -- name@alias
  RResolved  : CanonicalName → Expr                -- a resolved global reference
  RGen       : Gen → Expr                          -- a resolved generator
  RApp       : Expr → Expr → Expr                  -- f a
  RLam       : String → Expr → Expr                -- \x -> e
  RLet       : String → Expr → Expr → Expr         -- let x = e₁ in e₂
  RPair      : Expr → Expr → Expr                  -- (e₁, e₂)
  RDestruct  : Expr → String → Expr → String → Expr → Expr   -- destruct e | x -> e₁ | y -> e₂
  RUnit      : Expr                                -- ()
  RInt       : ℤ → Expr                            -- 5, -5 (a signed literal, plan 0.150 N4)
  RFloat     : Sign → ℕ → ℕ → ℕ → Expr             -- sign, integer part, fraction digits, their number
  RAnnot     : Expr → Type → Expr                  -- (e : T)
  RBinOp     : BinOp → Expr → Expr → Expr
  RNeg       : Expr → Expr                         -- -e

------------------------------------------------------------------------
-- Modules
------------------------------------------------------------------------

record Import : Set where
  constructor mkImport
  field
    path  : List String
    alias : Maybe String

data Decl : Set where
  DTypeSig   : String → PolyType → Decl            -- f : T
  DFunDef    : String → Expr → Decl                -- f = e
  DSignature : String → PolyType → Decl                  -- signature op : T
  DTypeAlias : String → List String → PolyType → Decl    -- type Name a b = T
  DImport    : Import → Decl

record Module : Set where
  constructor mkModule
  field
    decls : List Decl
