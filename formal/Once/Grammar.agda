-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar
--
-- Formal grammar specification for the Once surface syntax.
-- Defines valid syntax trees as inductive types.
--
-- The parser should produce values of these types, and parser
-- correctness means: parse ∘ pretty ≡ just for well-formed input.
------------------------------------------------------------------------

module Once.Grammar where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.String using (String)

open import Once.Type using (Quantity)

------------------------------------------------------------------------
-- Identifiers
------------------------------------------------------------------------

-- | Lower-case identifier (variables, function names)
LowerIdent : Set
LowerIdent = String

-- | Upper-case identifier (type names, module names, constructors)
UpperIdent : Set
UpperIdent = String

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | Type syntax
--
-- The function arrow is graded with a QTT Quantity (the grade that the
-- docs render as `A^q -> B` in surface syntax). The parser desugars
-- `A^q -> B` to `_⇒[_]_ A q B`; a bare `A -> B` uses `Many` (unrestricted).
-- Grade annotations are only allowed as arrow-argument grades — they
-- are parse errors in any other position, so the grammar's `GType` does
-- not carry grades inside products, sums, or on outputs.
mutual

 data GType : Set where
  -- Primitive types
  TUnit   : GType
  TVoid   : GType
  TInt    : GType
  TFloat  : GType
  TBuffer : GType
  TString : GType

  -- Type constructors
  _⇒[_]_  : GType → Quantity → GType → GType  -- Graded function: A -q> B (A^q -> B)
  _⊗_     : GType → GType → GType              -- Product: A * B
  _⊕_     : GType → GType → GType              -- Sum: A + B
  TEff    : GType → GType → GType              -- Effect: Eff A B

  -- Initial algebra of a polynomial functor: Mu F.
  GMu     : GFunctor → GType

  -- Type variable (for polymorphism and aliases)
  TVar    : UpperIdent → GType

 -- | Grammar-level polynomial functor (body of `Mu`).
 -- Mirrors `Once.Type.Functor` (K / Id / ⊕ / ⊗).
 data GFunctor : Set where
  GFK    : GType → GFunctor               -- constant functor: K T
  GFId   : GFunctor                        -- identity functor: Id
  GFSum  : GFunctor → GFunctor → GFunctor  -- functor sum: F + G
  GFProd : GFunctor → GFunctor → GFunctor  -- functor product: F * G

-- | Convenience alias for the unrestricted (Many) arrow, matching
-- the common `A -> B` surface form.
_⇒_ : GType → GType → GType
A ⇒ B = _⇒[_]_ A Once.Type.Many B

infixr 20 _⇒_
infixr 20 _⇒[_]_
infixl 25 _⊕_
infixl 30 _⊗_

-- | IO A is sugar for Eff Unit A
pattern TIO A = TEff TUnit A

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

-- | Binary operators
data BinOp : Set where
  OpAdd OpSub OpMul OpDiv OpMod : BinOp    -- Arithmetic
  OpLt OpLe OpGt OpGe OpEq OpNe : BinOp    -- Comparison

-- | Unary operators
data UnaryOp : Set where
  OpNeg : UnaryOp                          -- Negation

-- | Expression syntax
data GExpr : Set where
  -- Literals
  EUnit      : GExpr                       -- ()
  EInt       : ℕ → GExpr                   -- integer literal
  EString    : String → GExpr              -- string literal

  -- Variables
  EVar       : LowerIdent → GExpr
  EQualified : LowerIdent → LowerIdent → GExpr  -- name@module

  -- Lambda and application
  ELam       : LowerIdent → GExpr → GExpr  -- \x -> e
  EApp       : GExpr → GExpr → GExpr       -- f x

  -- Pairs
  EPair      : GExpr → GExpr → GExpr       -- (e1, e2)

  -- Let binding (multi-line, no semicolons)
  -- let x = e1
  --     y = e2
  -- in body
  ELet       : List (LowerIdent × GExpr) → GExpr → GExpr

  -- Sum elimination
  EDestruct  : GExpr → LowerIdent → GExpr → LowerIdent → GExpr → GExpr
               -- destruct e of { Left x -> e1 ; Right y -> e2 }

  -- Operators
  EBinOp     : BinOp → GExpr → GExpr → GExpr
  EUnaryOp   : UnaryOp → GExpr → GExpr

  -- Composition (f . g desugars to compose f g)
  ECompose   : GExpr → GExpr → GExpr

  -- Type annotation
  EAnnot     : GExpr → GType → GExpr       -- (e : T)

------------------------------------------------------------------------
-- Allocation Strategy
------------------------------------------------------------------------

-- D142: `AllocStrategy` is REMOVED — allocation is mechanical, nothing in the
-- source picks where a value lives. Supersedes D012/D013/D014; plan 0.86.

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- | Module path for imports
ModulePath : Set
ModulePath = List UpperIdent

-- | Declaration syntax
data GDecl : Set where
  -- Type signature: name : Type
  DTypeSig   : LowerIdent → GType → GDecl

  -- Function definition: name params = expr
  -- Allocation annotation comes after parameters, before '='
  -- Example: foo x y @stack = x + y
  -- Note: Must follow a DTypeSig with matching name
  DFunDef    : LowerIdent → List LowerIdent → GExpr → GDecl

  -- Primitive: primitive name : Type
  DSignature : LowerIdent → GType → GDecl

  -- Type alias: type Name params = Type
  DTypeAlias : UpperIdent → List LowerIdent → GType → GDecl

  -- Import: import Path [as Alias]
  DImport    : ModulePath → Maybe UpperIdent → GDecl

------------------------------------------------------------------------
-- Module
------------------------------------------------------------------------

-- | A module is a list of declarations
record GModule : Set where
  constructor mkGModule
  field
    decls : List GDecl

------------------------------------------------------------------------
-- Well-formedness constraints
------------------------------------------------------------------------

-- These could be defined as predicates on GModule:
--
-- 1. Every DFunDef must be immediately preceded by a DTypeSig
--    with the same name.
--
-- 2. For executable modules, there must be exactly one function
--    named "main" with type Eff Unit A for some A.
--
-- 3. Type aliases must not be cyclic.
--
-- 4. All referenced type variables must be in scope.

-- | Predicate: declaration pairs a type sig with its definition
data ValidDeclPair : GDecl → GDecl → Set where
  validPair : ∀ {name ty params body}
            → ValidDeclPair (DTypeSig name ty) (DFunDef name params body)

-- | Predicate: a type is valid for main
data ValidMainType : GType → Set where
  validMain : ∀ {A} → ValidMainType (TEff TUnit A)
