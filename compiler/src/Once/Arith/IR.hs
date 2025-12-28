{-# LANGUAGE DeriveFunctor #-}
-- | Arithmetic IR for efficient register-based computation
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module defines a separate IR for arithmetic expressions that
-- compiles orthogonally to the categorical generators, enabling
-- baremetal performance through direct register allocation.
module Once.Arith.IR
  ( -- * Numeric types
    NumType (..)
  , bitwidth
  , isFloat
  , isInteger
    -- * Arithmetic IR
  , ArithIR (..)
  , CmpOp (..)
    -- * Helpers
  , arithType
  , freeVars
  ) where

import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as Set

-- | Numeric types supported by the arithmetic compiler
--
-- These map directly to machine types for efficient codegen.
data NumType
  = I8    -- ^ 8-bit signed integer
  | I16   -- ^ 16-bit signed integer
  | I32   -- ^ 32-bit signed integer
  | I64   -- ^ 64-bit signed integer
  | F32   -- ^ 32-bit IEEE 754 float
  | F64   -- ^ 64-bit IEEE 754 double
  deriving (Eq, Show, Ord)

-- | Bit width of a numeric type
bitwidth :: NumType -> Int
bitwidth I8  = 8
bitwidth I16 = 16
bitwidth I32 = 32
bitwidth I64 = 64
bitwidth F32 = 32
bitwidth F64 = 64

-- | Check if type is floating-point
isFloat :: NumType -> Bool
isFloat F32 = True
isFloat F64 = True
isFloat _   = False

-- | Check if type is integer
isInteger :: NumType -> Bool
isInteger = not . isFloat

-- | Arithmetic expression IR
--
-- This is a simple expression tree with:
-- - Literals and variables
-- - Binary arithmetic operations
-- - Unary negation
-- - Comparisons (return Bool for control flow boundary)
--
-- Linearity is tracked separately during recognition; here we use
-- a simple free variable representation.
data ArithIR
  -- | Integer literal
  = ALitInt NumType Integer

  -- | Float literal
  | ALitFloat NumType Double

  -- | Variable reference (name and type)
  | AVar Text NumType

  -- | Addition
  | AAdd ArithIR ArithIR

  -- | Subtraction
  | ASub ArithIR ArithIR

  -- | Multiplication
  | AMul ArithIR ArithIR

  -- | Division (integer: truncating, float: IEEE)
  | ADiv ArithIR ArithIR

  -- | Modulo (integers only)
  | AMod ArithIR ArithIR

  -- | Negation
  | ANeg ArithIR

  -- | Comparison (returns Bool = Unit + Unit for control flow)
  | ACmp CmpOp ArithIR ArithIR

  -- | Type conversion/promotion (OCP-0002)
  -- Widens a value to a larger type within the same domain
  | AConv NumType ArithIR

  deriving (Eq, Show)

-- | Comparison operators
data CmpOp
  = CmpLt   -- ^ Less than
  | CmpLe   -- ^ Less than or equal
  | CmpGt   -- ^ Greater than
  | CmpGe   -- ^ Greater than or equal
  | CmpEq   -- ^ Equal
  | CmpNe   -- ^ Not equal
  deriving (Eq, Show, Ord)

-- | Get the type of an arithmetic expression
--
-- Assumes the expression is well-typed (all operands have same type).
arithType :: ArithIR -> NumType
arithType (ALitInt t _)   = t
arithType (ALitFloat t _) = t
arithType (AVar _ t)      = t
arithType (AAdd e _)      = arithType e
arithType (ASub e _)      = arithType e
arithType (AMul e _)      = arithType e
arithType (ADiv e _)      = arithType e
arithType (AMod e _)      = arithType e
arithType (ANeg e)        = arithType e
arithType (ACmp _ e _)    = arithType e  -- Comparison type is based on operands
arithType (AConv t _)     = t            -- Conversion produces target type

-- | Get free variables in an arithmetic expression
--
-- Returns set of (name, type) pairs.
freeVars :: ArithIR -> Set (Text, NumType)
freeVars (ALitInt _ _)   = Set.empty
freeVars (ALitFloat _ _) = Set.empty
freeVars (AVar n t)      = Set.singleton (n, t)
freeVars (AAdd e1 e2)    = freeVars e1 `Set.union` freeVars e2
freeVars (ASub e1 e2)    = freeVars e1 `Set.union` freeVars e2
freeVars (AMul e1 e2)    = freeVars e1 `Set.union` freeVars e2
freeVars (ADiv e1 e2)    = freeVars e1 `Set.union` freeVars e2
freeVars (AMod e1 e2)    = freeVars e1 `Set.union` freeVars e2
freeVars (ANeg e)        = freeVars e
freeVars (ACmp _ e1 e2)  = freeVars e1 `Set.union` freeVars e2
freeVars (AConv _ e)     = freeVars e
