{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Syntax — what a programmer writes, as a tree.
--
-- A module is a list of declarations: imports, type aliases, signatures of
-- the operations it is compiled against, type signatures and definitions.
-- An expression names variables by string; a reference to something global
-- is RESOLVED (`Spec.Surface.Resolution`) to the canonical name it denotes.
-- A type in a signature may mention named type variables (`PTVar`); an
-- annotation is a ground type.
------------------------------------------------------------------------

module Once.Spec.Surface.Syntax where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Once.Spec.Grade using (Quantity; Purity)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type using (Type)

------------------------------------------------------------------------
-- Types as written
------------------------------------------------------------------------

mutual
  data PolyFunctor : Set where
    PK   : PolyType → PolyFunctor
    PId  : PolyFunctor
    _P⊕_ : PolyFunctor → PolyFunctor → PolyFunctor
    _P⊗_ : PolyFunctor → PolyFunctor → PolyFunctor

  data PolyType : Set where
    PUnit PVoid PInt PFloat : PolyType
    _P*_ _P+_ : PolyType → PolyType → PolyType
    _P⇒[_]_   : PolyType → Quantity → PolyType → PolyType   -- a pure arrow
    PAct PEff : PolyType → PolyType → PolyType               -- `Act A B`, `Eff A B`
    Pμ        : PolyFunctor → PolyType                       -- `Mu F`
    Pν        : PolyFunctor → Purity → PolyType              -- `Nu F`, `Nu (Act F)`, `Nu (Eff F)`
    PTVar     : String → PolyType                            -- a type variable

infixr 40 _P⊕_
infixr 50 _P⊗_
infixr 30 _P⇒[_]_
infixr 40 _P+_
infixr 50 _P*_

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

data BinOp : Set where
  OpAdd OpSub OpMul OpDiv OpMod : BinOp
  OpLt OpLe OpGt OpGe OpEq OpNe : BinOp

data Expr : Set where
  RVar       : String → Expr                       -- x
  RQualified : String → String → Expr              -- name@alias
  RResolved  : CanonicalName → Expr                -- a resolved global reference
  RApp       : Expr → Expr → Expr                  -- f a
  RLam       : String → Expr → Expr                -- \x -> e
  RLet       : String → Expr → Expr → Expr         -- let x = e₁ in e₂
  RPair      : Expr → Expr → Expr                  -- (e₁, e₂)
  RDestruct  : Expr → String → Expr → String → Expr → Expr   -- destruct e | x -> e₁ | y -> e₂
  RUnit      : Expr                                -- ()
  RInt       : ℤ → Expr
  RFloat     : ℕ → ℕ → ℕ → Expr                    -- integer part, fraction digits, their number
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
