module Once.Syntax
  ( -- * Modules
    Module (..)
  , Decl (..)
    -- * Expressions
  , Expr (..)
    -- * Types
  , SType (..)
    -- * Names
  , Name
  ) where

import Data.Text (Text)

import Once.Quantity (Quantity)

-- | Variable and type names
type Name = Text

-- | A module is a list of declarations
newtype Module = Module { moduleDecls :: [Decl] }
  deriving (Eq, Show)

-- | Top-level declarations
data Decl
  = TypeSig Name SType           -- ^ Type signature: name : Type
  | FunDef Name Expr             -- ^ Function definition: name = expr
  | Primitive Name SType         -- ^ Primitive declaration: primitive name : Type
  deriving (Eq, Show)

-- | Surface syntax expressions (before elaboration to IR)
--
-- Generators (fst, snd, pair, etc.) are represented as EVar with
-- reserved names. The elaborator recognizes these and produces IR.
data Expr
  = EVar Name                       -- ^ Variable or generator: x, fst, snd, pair, ...
  | EApp Expr Expr                  -- ^ Application: f x
  | ELam Name Expr                  -- ^ Lambda: \x -> e
  | EPair Expr Expr                 -- ^ Pair literal: (e1, e2)
  | ECase Expr Name Expr Name Expr  -- ^ Case: case e of { Left x -> e1; Right y -> e2 }
  | EUnit                           -- ^ Unit value: ()
  | EInt Integer                    -- ^ Integer literal: 0, 1, 42, ...
  | EAnnot Expr SType               -- ^ Type annotation: (e : T)
  deriving (Eq, Show)

-- | Surface syntax types
data SType
  = STVar Name                   -- ^ Type variable: A
  | STUnit                       -- ^ Unit type: Unit
  | STVoid                       -- ^ Void type: Void
  | STInt                        -- ^ Integer type: Int
  | STProduct SType SType        -- ^ Product: A * B
  | STSum SType SType            -- ^ Sum: A + B
  | STArrow SType SType          -- ^ Function: A -> B
  | STQuant Quantity SType       -- ^ Quantity annotation: A^1
  deriving (Eq, Show)
