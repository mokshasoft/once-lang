-- | C code generation for arithmetic expressions
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- Generates efficient C expressions from ArithIR. Since C already has
-- native support for arithmetic operators, this is straightforward -
-- we just emit the corresponding C operators.
--
-- The key benefit is that arithmetic expressions bypass the categorical
-- generator machinery and compile directly to C expressions, which the
-- C compiler can then optimize with its own register allocator.
module Once.Arith.CodeGen.C
  ( -- * Code generation
    arithToC
  , arithToCExpr
    -- * Type mapping
  , numTypeToC
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Once.Arith.IR

-- | Generate a complete C expression from ArithIR
--
-- The result is a C expression string that can be used directly
-- in assignments, return statements, or as subexpressions.
arithToC :: ArithIR -> Text
arithToC = arithToCExpr

-- | Generate C expression with proper parenthesization
arithToCExpr :: ArithIR -> Text
arithToCExpr expr = case expr of
  -- Literals
  ALitInt _ n
    | n < 0     -> "(" <> T.pack (show n) <> ")"
    | otherwise -> T.pack (show n)

  ALitFloat _ f
    | f < 0     -> "(" <> T.pack (show f) <> ")"
    | otherwise -> T.pack (show f)

  -- Variable reference
  AVar name _ -> name

  -- Binary operations - parenthesize for safety
  AAdd e1 e2 -> parens $ arithToCExpr e1 <> " + " <> arithToCExpr e2
  ASub e1 e2 -> parens $ arithToCExpr e1 <> " - " <> arithToCExpr e2
  AMul e1 e2 -> parens $ arithToCExpr e1 <> " * " <> arithToCExpr e2
  ADiv e1 e2 -> parens $ arithToCExpr e1 <> " / " <> arithToCExpr e2
  AMod e1 e2 -> parens $ arithToCExpr e1 <> " % " <> arithToCExpr e2

  -- Unary negation
  ANeg e -> parens $ "-" <> arithToCExpr e

  -- Comparisons - return int (0 or 1) in C
  ACmp op e1 e2 -> parens $ arithToCExpr e1 <> cmpOpToC op <> arithToCExpr e2

  -- Type conversion/promotion (OCP-0002)
  AConv targetTy e -> parens $ "(" <> numTypeToC targetTy <> ")" <> arithToCExpr e

-- | Wrap in parentheses
parens :: Text -> Text
parens t = "(" <> t <> ")"

-- | Convert comparison operator to C
cmpOpToC :: CmpOp -> Text
cmpOpToC CmpLt = " < "
cmpOpToC CmpLe = " <= "
cmpOpToC CmpGt = " > "
cmpOpToC CmpGe = " >= "
cmpOpToC CmpEq = " == "
cmpOpToC CmpNe = " != "

-- | Convert NumType to C type name
numTypeToC :: NumType -> Text
numTypeToC I8  = "int8_t"
numTypeToC I16 = "int16_t"
numTypeToC I32 = "int32_t"
numTypeToC I64 = "int64_t"
numTypeToC F32 = "float"
numTypeToC F64 = "double"

-- | Generate C type declaration for a numeric type
-- Includes necessary headers
numTypeToCDecl :: NumType -> Text
numTypeToCDecl t = case t of
  I8  -> "int8_t"   -- requires <stdint.h>
  I16 -> "int16_t"
  I32 -> "int32_t"
  I64 -> "int64_t"
  F32 -> "float"
  F64 -> "double"

-- | Check if we need stdint.h for this type
needsStdint :: NumType -> Bool
needsStdint I8  = True
needsStdint I16 = True
needsStdint I32 = True
needsStdint I64 = True
needsStdint _   = False

-- | Generate a C function that computes an arithmetic expression
--
-- Example:
-- @
-- arithToCFunction "compute" I64 [("x", I64), ("y", I64)] (AAdd (AVar "x" I64) (AVar "y" I64))
-- @
-- generates:
-- @
-- int64_t compute(int64_t x, int64_t y) {
--     return (x + y);
-- }
-- @
arithToCFunction :: Text -> NumType -> [(Text, NumType)] -> ArithIR -> Text
arithToCFunction name retTy params body = T.unlines
  [ numTypeToC retTy <> " " <> name <> "(" <> paramList <> ") {"
  , "    return " <> arithToCExpr body <> ";"
  , "}"
  ]
  where
    paramList = T.intercalate ", " $
      map (\(n, t) -> numTypeToC t <> " " <> n) params
