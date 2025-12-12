module Once.Syntax
  ( -- * Modules
    Module (..)
  , Decl (..)
  , Import (..)
    -- * Expressions
  , Expr (..)
    -- * Types
  , SType (..)
    -- * Allocation
  , AllocStrategy (..)
    -- * Names
  , Name
  , ModuleName
  ) where

import Data.Text (Text)

import Once.Quantity (Quantity)
import Once.Type (Encoding)

-- | Variable and type names
type Name = Text

-- | Module names (dot-separated path)
type ModuleName = [Text]

-- | Import declaration
data Import = Import
  { importModule :: ModuleName   -- ^ Module path: ["Canonical", "Product"]
  , importAlias  :: Maybe Name   -- ^ Optional alias: `import Foo as F`
  } deriving (Eq, Show)

-- | A module is a list of imports and declarations
data Module = Module
  { moduleImports :: [Import]
  , moduleDecls   :: [Decl]
  } deriving (Eq, Show)

-- | Allocation strategy for buffer outputs
data AllocStrategy
  = AllocStack    -- ^ Stack-allocated, automatic lifetime
  | AllocHeap     -- ^ Heap-allocated via malloc/free
  | AllocPool     -- ^ Fixed-size block pool
  | AllocArena    -- ^ Bump allocation, bulk free
  | AllocConst    -- ^ Read-only constant section (string literals)
  deriving (Eq, Show)

-- | Top-level declarations
data Decl
  = TypeSig Name SType                        -- ^ Type signature: name : Type
  | FunDef Name (Maybe AllocStrategy) Expr    -- ^ Function definition: name [@alloc] = expr
  | Primitive Name SType                      -- ^ Primitive declaration: primitive name : Type
  | TypeAlias Name [Name] SType               -- ^ Type alias: type Name A B = Type
  deriving (Eq, Show)

-- | Surface syntax expressions (before elaboration to IR)
--
-- Generators (fst, snd, pair, etc.) are represented as EVar with
-- reserved names. The elaborator recognizes these and produces IR.
data Expr
  = EVar Name                       -- ^ Variable or generator: x, fst, snd, pair, ...
  | EQualified Name ModuleName      -- ^ Qualified access: swap@Canonical.Product
  | EApp Expr Expr                  -- ^ Application: f x
  | ELam Name Expr                  -- ^ Lambda: \x -> e
  | ELet Name Expr Expr             -- ^ Let binding: let x = e1 in e2
  | EPair Expr Expr                 -- ^ Pair literal: (e1, e2)
  | ECase Expr Name Expr Name Expr  -- ^ Case: case e of { Left x -> e1; Right y -> e2 }
  | EUnit                           -- ^ Unit value: ()
  | EInt Integer                    -- ^ Integer literal: 0, 1, 42, ...
  | EStringLit Text                 -- ^ String literal: "hello"
  | EAnnot Expr SType               -- ^ Type annotation: (e : T)
  deriving (Eq, Show)

-- | Surface syntax types
data SType
  = STVar Name                   -- ^ Type variable: A
  | STUnit                       -- ^ Unit type: Unit
  | STVoid                       -- ^ Void type: Void
  | STInt                        -- ^ Integer type: Int
  | STBuffer                     -- ^ Buffer type: Buffer
  | STString Encoding            -- ^ String type with encoding: String Utf8
  | STProduct SType SType        -- ^ Product: A * B
  | STSum SType SType            -- ^ Sum: A + B
  | STArrow SType SType          -- ^ Function: A -> B (pure)
  | STEff SType SType            -- ^ Effectful morphism: Eff A B (see D032)
  | STQuant Quantity SType       -- ^ Quantity annotation: A^1
  | STApp Name [SType]           -- ^ Type application: Maybe A, List Int
  | STFix SType                  -- ^ Fixed point: Fix F (for recursive types)
  deriving (Eq, Show)
