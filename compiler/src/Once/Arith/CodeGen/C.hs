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
--
-- Uses MAlonzo-extracted types from verified Agda proofs (OCP-0004).
module Once.Arith.CodeGen.C
  ( -- * Code generation
    arithToC
  , arithToCExpr
    -- * Type mapping
  , numTypeToC
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

-- | Generate a complete C expression from ArithIR
--
-- The result is a C expression string that can be used directly
-- in assignments, return statements, or as subexpressions.
-- Takes NumType to know how to interpret literals.
arithToC :: MT.T_NumType_6 -> MA.T_ArithIR_72 -> Text
arithToC numTy = arithToCExpr numTy

-- | Generate C expression with proper parenthesization
arithToCExpr :: MT.T_NumType_6 -> MA.T_ArithIR_72 -> Text
arithToCExpr numTy expr = case expr of
  -- Literals - extract value from AgdaAny based on type
  MA.C_Lit_76 val
    | isFloatType numTy ->
        let f = unsafeCoerce val :: Double
        in if f < 0 then "(" <> T.pack (show f) <> ")" else T.pack (show f)
    | otherwise ->
        let n = unsafeCoerce val :: Integer
        in if n < 0 then "(" <> T.pack (show n) <> ")" else T.pack (show n)

  -- Variable reference (ignore proof)
  MA.C_Var_84 name _ -> name

  -- Binary operations (ignore contexts) - parenthesize for safety
  MA.C_Add_92 _ _ e1 e2 -> parens $ arithToCExpr numTy e1 <> " + " <> arithToCExpr numTy e2
  MA.C_Sub_100 _ _ e1 e2 -> parens $ arithToCExpr numTy e1 <> " - " <> arithToCExpr numTy e2
  MA.C_Mul_108 _ _ e1 e2 -> parens $ arithToCExpr numTy e1 <> " * " <> arithToCExpr numTy e2
  MA.C_Div_116 _ _ e1 e2 -> parens $ arithToCExpr numTy e1 <> " / " <> arithToCExpr numTy e2
  MA.C_Mod_124 _ _ e1 e2 -> parens $ arithToCExpr numTy e1 <> " % " <> arithToCExpr numTy e2

  -- Unary negation
  MA.C_Neg_130 e -> parens $ "-" <> arithToCExpr numTy e

  -- Comparisons - return int (0 or 1) in C
  MA.C_Cmp_138 _ _ op e1 e2 -> parens $ arithToCExpr numTy e1 <> cmpOpToC op <> arithToCExpr numTy e2

  -- Type conversion/promotion (OCP-0002)
  MA.C_Conv_146 targetTy e -> parens $ "(" <> numTypeToC targetTy <> ")" <> arithToCExpr numTy e

-- | Wrap in parentheses
parens :: Text -> Text
parens t = "(" <> t <> ")"

-- | Check if NumType is a floating-point type
isFloatType :: MT.T_NumType_6 -> Bool
isFloatType MT.C_F32_16 = True
isFloatType MT.C_F64_18 = True
isFloatType _           = False

-- | Convert comparison operator to C
cmpOpToC :: MA.T_CmpOp_58 -> Text
cmpOpToC MA.C_CmpLt_60 = " < "
cmpOpToC MA.C_CmpLe_62 = " <= "
cmpOpToC MA.C_CmpGt_64 = " > "
cmpOpToC MA.C_CmpGe_66 = " >= "
cmpOpToC MA.C_CmpEq_68 = " == "
cmpOpToC MA.C_CmpNe_70 = " != "

-- | Convert NumType to C type name
numTypeToC :: MT.T_NumType_6 -> Text
numTypeToC MT.C_I8_8   = "int8_t"
numTypeToC MT.C_I16_10 = "int16_t"
numTypeToC MT.C_I32_12 = "int32_t"
numTypeToC MT.C_I64_14 = "int64_t"
numTypeToC MT.C_F32_16 = "float"
numTypeToC MT.C_F64_18 = "double"

-- | Generate C type declaration for a numeric type
-- Includes necessary headers
numTypeToCDecl :: MT.T_NumType_6 -> Text
numTypeToCDecl t = case t of
  MT.C_I8_8   -> "int8_t"   -- requires <stdint.h>
  MT.C_I16_10 -> "int16_t"
  MT.C_I32_12 -> "int32_t"
  MT.C_I64_14 -> "int64_t"
  MT.C_F32_16 -> "float"
  MT.C_F64_18 -> "double"

-- | Check if we need stdint.h for this type
needsStdint :: MT.T_NumType_6 -> Bool
needsStdint MT.C_I8_8   = True
needsStdint MT.C_I16_10 = True
needsStdint MT.C_I32_12 = True
needsStdint MT.C_I64_14 = True
needsStdint _           = False

-- | Generate a C function that computes an arithmetic expression
--
-- Example:
-- @
-- arithToCFunction "compute" I64 [("x", I64), ("y", I64)] (Add ...)
-- @
-- generates:
-- @
-- int64_t compute(int64_t x, int64_t y) {
--     return (x + y);
-- }
-- @
arithToCFunction :: Text -> MT.T_NumType_6 -> [(Text, MT.T_NumType_6)] -> MA.T_ArithIR_72 -> Text
arithToCFunction name retTy params body = T.unlines
  [ numTypeToC retTy <> " " <> name <> "(" <> paramList <> ") {"
  , "    return " <> arithToCExpr retTy body <> ";"
  , "}"
  ]
  where
    paramList = T.intercalate ", " $
      map (\(n, t) -> numTypeToC t <> " " <> n) params
