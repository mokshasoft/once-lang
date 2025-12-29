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
  , isArithType
    -- * Primitive mappings
  , arithPrimOp
  , ArithOp (..)
    -- * Re-exports from MAlonzo
  , MA.T_ArithIR_72
  , MT.T_NumType_6
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import MAlonzo.RTE (coe)
import Once.IR (IR (..))
import Once.Type (Type (..), Name)
import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

-- | Arithmetic operation classification
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

-- | Check if a type is arithmetic (numeric)
isArithType :: Type -> Bool
isArithType TInt   = True
isArithType TFloat = True
isArithType _      = False

-- | Attempt to recognize an IR expression as pure arithmetic
--
-- Returns @Just (numType, arithIR)@ if the expression is pure arithmetic,
-- @Nothing@ if it contains non-arithmetic operations (branching,
-- effects, closures, etc.)
--
-- Recognition criteria:
-- 1. Numeric types only (Int, Float)
-- 2. Arithmetic primitives only (+, -, *, /, %)
-- 3. No internal branching (no Case)
-- 4. No effects (no Eff types)
-- 5. No closures (no Curry/Apply)
recognizeArith :: IR -> Maybe (MT.T_NumType_6, MA.T_ArithIR_72)
recognizeArith ir = recognizeWithInput "_input" ir

-- | Recognize arithmetic with a named input variable
recognizeWithInput :: Text -> IR -> Maybe (MT.T_NumType_6, MA.T_ArithIR_72)
recognizeWithInput inputName ir = case ir of
  -- Identity on numeric type = input variable
  Id ty
    | Just numTy <- typeToNumType ty
    -> Just (numTy, MA.C_Var_84 inputName MA.C_here_40)

  -- Integer literals encoded as primitives
  Prim name _ outTy
    | Just n <- parseIntLit name
    , Just numTy <- typeToNumType outTy
    -> Just (numTy, MA.C_Lit_76 (coe n))

  -- Float literals encoded as primitives
  Prim name _ outTy
    | Just f <- parseFloatLit name
    , Just numTy <- typeToNumType outTy
    -> Just (numTy, MA.C_Lit_76 (coe f))

  -- Binary operation: op ∘ ⟨left, right⟩
  -- Pattern: Compose (Prim op _ _) (Pair left right)
  Compose (Prim opName (TProduct _ _) outTy) (Pair left right)
    | Just op <- arithPrimOp opName
    , Just numTy <- typeToNumType outTy
    -> do
        (_, leftArith) <- recognizeWithInput inputName left
        (_, rightArith) <- recognizeWithInput inputName right
        Just (numTy, makeBinaryOp op leftArith rightArith)

  -- Unary operation: op ∘ expr
  -- Pattern: Compose (Prim op inTy outTy) expr where inTy is not a product
  Compose (Prim opName inTy outTy) expr
    | Just OpNeg <- arithPrimOp opName
    , not (isProductType inTy)
    , Just numTy <- typeToNumType outTy
    -> do
        (_, exprArith) <- recognizeWithInput inputName expr
        Just (numTy, MA.C_Neg_130 exprArith)

  -- Composition of arithmetic expressions
  -- General case: f ∘ g where both are arithmetic
  Compose f g -> do
    -- If f is an arith primitive expecting product input, need Pair
    -- Otherwise, it's chained arithmetic
    case f of
      Prim opName (TProduct _ _) _
        | Just _ <- arithPrimOp opName
        -> Nothing  -- Binary ops need explicit Pair; handled above

      _ -> do
        -- g computes input for f
        _ <- recognizeWithInput inputName g
        -- But f expects gArith as input... this is complex
        -- For now, only handle simple cases
        Nothing

  -- Projections on pair input
  Fst a _
    | Just numTy <- typeToNumType a
    -> Just (numTy, MA.C_Var_84 (inputName <> ".fst") MA.C_here_40)

  Snd _ b
    | Just numTy <- typeToNumType b
    -> Just (numTy, MA.C_Var_84 (inputName <> ".snd") MA.C_here_40)

  -- Terminal (Unit) - not arithmetic
  Terminal _ -> Nothing

  -- Local variable reference
  LocalVar name
    -> Just (MT.C_I64_14, MA.C_Var_84 name MA.C_here_40)  -- Assume I64 for now

  -- Not arithmetic
  _ -> Nothing

-- | Check if a type is a product type
isProductType :: Type -> Bool
isProductType (TProduct _ _) = True
isProductType _              = False

-- | Create a binary arithmetic operation
-- Uses empty contexts (erased at runtime in MAlonzo)
makeBinaryOp :: ArithOp -> MA.T_ArithIR_72 -> MA.T_ArithIR_72 -> MA.T_ArithIR_72
makeBinaryOp op left right = case op of
  OpAdd -> MA.C_Add_92 emptyCtx emptyCtx left right
  OpSub -> MA.C_Sub_100 emptyCtx emptyCtx left right
  OpMul -> MA.C_Mul_108 emptyCtx emptyCtx left right
  OpDiv -> MA.C_Div_116 emptyCtx emptyCtx left right
  OpMod -> MA.C_Mod_124 emptyCtx emptyCtx left right
  OpNeg -> MA.C_Neg_130 left  -- Shouldn't happen for binary
  OpLt  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpLt_60 left right
  OpLe  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpLe_62 left right
  OpGt  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpGt_64 left right
  OpGe  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpGe_66 left right
  OpEq  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpEq_68 left right
  OpNe  -> MA.C_Cmp_138 emptyCtx emptyCtx MA.C_CmpNe_70 left right
  where
    emptyCtx = MA.d_'8709'_20

-- | Check if a primitive name is an arithmetic operation
isArithPrim :: Name -> Bool
isArithPrim name = case arithPrimOp name of
  Just _  -> True
  Nothing -> False

-- | Map primitive names to arithmetic operations
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

-- | Convert Once Type to MAlonzo NumType
typeToNumType :: Type -> Maybe MT.T_NumType_6
typeToNumType TInt   = Just MT.C_I64_14  -- Default Int is 64-bit
typeToNumType TFloat = Just MT.C_F64_18  -- Default Float is 64-bit
typeToNumType _      = Nothing

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
