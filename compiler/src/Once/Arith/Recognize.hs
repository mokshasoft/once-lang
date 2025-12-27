-- | Recognition of arithmetic regions in the main IR
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module identifies pure arithmetic subexpressions that can be
-- compiled with the efficient register-based arithmetic compiler
-- instead of the general categorical generator machinery.
module Once.Arith.Recognize
  ( -- * Recognition
    recognizeArith
  , isArithPrim
    -- * Primitive mappings
  , arithPrimOp
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Once.IR (IR (..))
import Once.Type (Type (..), Name)
import Once.Arith.IR

-- | Attempt to recognize an IR expression as pure arithmetic
--
-- Returns @Just arithIR@ if the expression is pure arithmetic,
-- @Nothing@ if it contains non-arithmetic operations (branching,
-- effects, closures, etc.)
--
-- Recognition criteria:
-- 1. Numeric types only (Int, Float)
-- 2. Arithmetic primitives only (+, -, *, /, %)
-- 3. No internal branching (no Case)
-- 4. No effects (no Eff types)
-- 5. No closures (no Curry/Apply)
recognizeArith :: IR -> Maybe ArithIR
recognizeArith ir = case ir of
  -- Primitives that are arithmetic operations
  Prim name inTy outTy
    | Just op <- arithPrimOp name
    -> Just $ primToArith op outTy

  -- Integer literals encoded as primitives
  Prim name _ outTy
    | Just n <- parseIntLit name
    , Just numTy <- typeToNumType outTy
    -> Just $ ALitInt numTy n

  -- Float literals encoded as primitives
  Prim name _ outTy
    | Just f <- parseFloatLit name
    , Just numTy <- typeToNumType outTy
    -> Just $ ALitFloat numTy f

  -- Local variables (from let bindings)
  LocalVar name
    -> Nothing  -- Need type info; handled at higher level

  -- Composition of arithmetic operations
  Compose f g -> do
    -- Both must be arithmetic
    af <- recognizeArith f
    ag <- recognizeArith g
    -- Composition in arithmetic is function application
    -- This is tricky - need to handle binary ops
    combineArith af ag

  -- Pair of arithmetic expressions (for binary op inputs)
  Pair f g -> do
    af <- recognizeArith f
    ag <- recognizeArith g
    -- Return as a marker; actual combination happens in Compose
    Nothing  -- Pairs are handled specially

  -- Not arithmetic
  _ -> Nothing

-- | Check if a primitive name is an arithmetic operation
isArithPrim :: Name -> Bool
isArithPrim name = case arithPrimOp name of
  Just _  -> True
  Nothing -> False

-- | Map primitive names to arithmetic operations
--
-- Returns the operation type if recognized.
data ArithOp
  = OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpMod
  | OpNeg
  | OpLt
  | OpLe
  | OpGt
  | OpGe
  | OpEq
  | OpNe
  deriving (Eq, Show)

arithPrimOp :: Name -> Maybe ArithOp
arithPrimOp name = case name of
  -- Integer operations
  "__add_i8"  -> Just OpAdd
  "__add_i16" -> Just OpAdd
  "__add_i32" -> Just OpAdd
  "__add_i64" -> Just OpAdd
  "__add_f32" -> Just OpAdd
  "__add_f64" -> Just OpAdd

  "__sub_i8"  -> Just OpSub
  "__sub_i16" -> Just OpSub
  "__sub_i32" -> Just OpSub
  "__sub_i64" -> Just OpSub
  "__sub_f32" -> Just OpSub
  "__sub_f64" -> Just OpSub

  "__mul_i8"  -> Just OpMul
  "__mul_i16" -> Just OpMul
  "__mul_i32" -> Just OpMul
  "__mul_i64" -> Just OpMul
  "__mul_f32" -> Just OpMul
  "__mul_f64" -> Just OpMul

  "__div_i8"  -> Just OpDiv
  "__div_i16" -> Just OpDiv
  "__div_i32" -> Just OpDiv
  "__div_i64" -> Just OpDiv
  "__div_f32" -> Just OpDiv
  "__div_f64" -> Just OpDiv

  "__mod_i8"  -> Just OpMod
  "__mod_i16" -> Just OpMod
  "__mod_i32" -> Just OpMod
  "__mod_i64" -> Just OpMod

  "__neg_i8"  -> Just OpNeg
  "__neg_i16" -> Just OpNeg
  "__neg_i32" -> Just OpNeg
  "__neg_i64" -> Just OpNeg
  "__neg_f32" -> Just OpNeg
  "__neg_f64" -> Just OpNeg

  -- Comparisons
  "__lt_i8"  -> Just OpLt
  "__lt_i16" -> Just OpLt
  "__lt_i32" -> Just OpLt
  "__lt_i64" -> Just OpLt
  "__lt_f32" -> Just OpLt
  "__lt_f64" -> Just OpLt

  "__le_i8"  -> Just OpLe
  "__le_i16" -> Just OpLe
  "__le_i32" -> Just OpLe
  "__le_i64" -> Just OpLe
  "__le_f32" -> Just OpLe
  "__le_f64" -> Just OpLe

  "__gt_i8"  -> Just OpGt
  "__gt_i16" -> Just OpGt
  "__gt_i32" -> Just OpGt
  "__gt_i64" -> Just OpGt
  "__gt_f32" -> Just OpGt
  "__gt_f64" -> Just OpGt

  "__ge_i8"  -> Just OpGe
  "__ge_i16" -> Just OpGe
  "__ge_i32" -> Just OpGe
  "__ge_i64" -> Just OpGe
  "__ge_f32" -> Just OpGe
  "__ge_f64" -> Just OpGe

  "__eq_i8"  -> Just OpEq
  "__eq_i16" -> Just OpEq
  "__eq_i32" -> Just OpEq
  "__eq_i64" -> Just OpEq
  "__eq_f32" -> Just OpEq
  "__eq_f64" -> Just OpEq

  "__ne_i8"  -> Just OpNe
  "__ne_i16" -> Just OpNe
  "__ne_i32" -> Just OpNe
  "__ne_i64" -> Just OpNe
  "__ne_f32" -> Just OpNe
  "__ne_f64" -> Just OpNe

  _ -> Nothing

-- | Convert Once Type to NumType
typeToNumType :: Type -> Maybe NumType
typeToNumType TInt = Just I64  -- Default Int is 64-bit
typeToNumType TFloat = Just F64  -- Default Float is 64-bit
typeToNumType _ = Nothing

-- | Parse integer literal from primitive name
-- Format: __int_N where N is the integer value
parseIntLit :: Name -> Maybe Integer
parseIntLit name
  | "__int_" `T.isPrefixOf` name
  = case reads (T.unpack $ T.drop 6 name) of
      [(n, "")] -> Just n
      _         -> Nothing
  | otherwise = Nothing

-- | Parse float literal from primitive name
-- Format: __float_X where X is the float value
parseFloatLit :: Name -> Maybe Double
parseFloatLit name
  | "__float_" `T.isPrefixOf` name
  = case reads (T.unpack $ T.drop 8 name) of
      [(f, "")] -> Just f
      _         -> Nothing
  | otherwise = Nothing

-- | Convert a primitive operation to ArithIR
-- This is a placeholder; actual conversion needs operands
primToArith :: ArithOp -> Type -> ArithIR
primToArith op ty = case typeToNumType ty of
  Just numTy -> ALitInt numTy 0  -- Placeholder
  Nothing    -> ALitInt I64 0

-- | Combine two arithmetic expressions
-- This handles the case of binary operations composed with their inputs
combineArith :: ArithIR -> ArithIR -> Maybe ArithIR
combineArith _ _ = Nothing  -- Placeholder; full implementation needs more context
