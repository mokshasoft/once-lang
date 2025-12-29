------------------------------------------------------------------------
-- Once.TypeCheck.Raw
--
-- Raw (untyped) syntax for Once programs.
-- Mirrors compiler/src/Once/Syntax.hs with named variables.
--
-- Part of OCP-0003: Verified Type Checker
------------------------------------------------------------------------

module Once.TypeCheck.Raw where

open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Once.Type using (Type)

------------------------------------------------------------------------
-- Binary Operators (OCP-0002)
------------------------------------------------------------------------

-- | Binary operators for infix syntax
-- Mirrors Once.Syntax.BinOp from Haskell
data BinOp : Set where
  -- Arithmetic operators
  OpAdd : BinOp    -- a + b
  OpSub : BinOp    -- a - b
  OpMul : BinOp    -- a * b
  OpDiv : BinOp    -- a / b
  OpMod : BinOp    -- a % b
  -- Comparison operators
  OpLt  : BinOp    -- a < b
  OpLe  : BinOp    -- a <= b
  OpGt  : BinOp    -- a > b
  OpGe  : BinOp    -- a >= b
  OpEq  : BinOp    -- a == b
  OpNe  : BinOp    -- a != b

------------------------------------------------------------------------
-- Unary Operators
------------------------------------------------------------------------

-- | Unary operators
-- Mirrors Once.Syntax.UnaryOp from Haskell
data UnaryOp : Set where
  OpNeg : UnaryOp  -- -x

------------------------------------------------------------------------
-- Raw Expressions
------------------------------------------------------------------------

-- | Raw expressions with named variables
-- Mirrors Once.Syntax.Expr from Haskell
--
-- These are the expressions produced by the parser, before
-- type checking converts them to well-typed intrinsic terms.
data RawExpr : Set where
  -- Variable reference
  RVar      : String → RawExpr

  -- Function application
  RApp      : RawExpr → RawExpr → RawExpr

  -- Lambda abstraction: λx. body
  RLam      : String → RawExpr → RawExpr

  -- Let binding: let x = e1 in e2
  RLet      : String → RawExpr → RawExpr → RawExpr

  -- Pair introduction: (e1, e2)
  RPair     : RawExpr → RawExpr → RawExpr

  -- Case analysis: case e of { Left x -> e1; Right y -> e2 }
  RCase     : RawExpr → String → RawExpr → String → RawExpr → RawExpr

  -- Unit value: ()
  RUnit     : RawExpr

  -- Integer literal
  RInt      : ℤ → RawExpr

  -- String literal
  RStringLit : String → RawExpr

  -- Type annotation: (e : T)
  RAnnot    : RawExpr → Type → RawExpr

  -- Binary operator application (OCP-0002)
  RBinOp    : BinOp → RawExpr → RawExpr → RawExpr

  -- Unary operator application (OCP-0002)
  RUnaryOp  : UnaryOp → RawExpr → RawExpr

------------------------------------------------------------------------
-- Raw Types (with type variable names)
------------------------------------------------------------------------

-- | Raw surface types
-- Mirrors Once.Syntax.SType from Haskell
-- Used for type annotations before resolution
data RawType : Set where
  RTVar     : String → RawType              -- Type variable: A
  RTUnit    : RawType                       -- Unit
  RTVoid    : RawType                       -- Void
  RTInt     : RawType                       -- Int
  RTFloat   : RawType                       -- Float
  RTBuffer  : RawType                       -- Buffer
  RTStr     : RawType                       -- String
  RTProduct : RawType → RawType → RawType   -- A * B
  RTSum     : RawType → RawType → RawType   -- A + B
  RTArrow   : RawType → RawType → RawType   -- A -> B
  RTEff     : RawType → RawType → RawType   -- Eff A B
  RTFix     : RawType → RawType             -- Fix F

------------------------------------------------------------------------
-- Utility: Operator result type classification
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false)

-- | Is this a comparison operator?
-- Comparison operators return Bool (encoded as Unit + Unit)
isComparisonOp : BinOp → Bool
isComparisonOp OpLt = true
isComparisonOp OpLe = true
isComparisonOp OpGt = true
isComparisonOp OpGe = true
isComparisonOp OpEq = true
isComparisonOp OpNe = true
isComparisonOp _    = false

-- | Is this an arithmetic operator?
isArithmeticOp : BinOp → Bool
isArithmeticOp OpAdd = true
isArithmeticOp OpSub = true
isArithmeticOp OpMul = true
isArithmeticOp OpDiv = true
isArithmeticOp OpMod = true
isArithmeticOp _     = false
