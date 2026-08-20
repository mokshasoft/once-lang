module Once.Eval
  ( eval
  , EvalError (..)
  ) where

import Unsafe.Coerce (unsafeCoerce)

import Once.IR (IR (..))
import Once.Value (Value (..))
import qualified MAlonzo.Code.Once.Arith.IR as MA
import qualified MAlonzo.Code.Once.Arith.Type as MT

-- | Evaluation errors
data EvalError
  = TypeError String         -- ^ Type mismatch during evaluation
  | UnboundVariable String   -- ^ Variable not in scope
  | InvalidApplication       -- ^ Tried to apply non-function
  deriving (Eq, Show)

-- | Evaluate an IR expression with an input value
--
-- Each generator has a direct operational semantics:
-- - id: pass through
-- - compose: evaluate right, then left
-- - fst/snd: project from pair
-- - pair: construct pair from two morphisms
-- - inl/inr: inject into sum
-- - case: branch on sum
-- - terminal: discard input, return unit
-- - initial: impossible (Void has no values)
-- - curry: create closure
-- - apply: apply closure to argument
eval :: IR -> Value -> Either EvalError Value

-- Category
eval (Id _) v = Right v
eval (Compose g f) v = eval f v >>= eval g

-- Products
eval (Fst _ _) (VPair a _) = Right a
eval (Fst _ _) _ = Left (TypeError "fst expects a pair")

eval (Snd _ _) (VPair _ b) = Right b
eval (Snd _ _) _ = Left (TypeError "snd expects a pair")

eval (Pair f g) v = do
  a <- eval f v
  b <- eval g v
  Right (VPair a b)

-- Terminal
eval (Terminal _) _ = Right VUnit

-- Coproducts
eval (Inl _ _) v = Right (VLeft v)
eval (Inr _ _) v = Right (VRight v)

eval (Case f _) (VLeft a) = eval f a
eval (Case _ g) (VRight b) = eval g b
eval (Case _ _) _ = Left (TypeError "case expects a sum value")

-- Initial (Void elimination - this should never be called with a value)
eval (Initial _) _ = Left (TypeError "initial: Void has no values")

-- Exponentials
eval (Curry _ f) v = Right (VClosure [(f, v)] f)

eval (Apply _ _) (VPair (VClosure _ body) arg) = eval body (VPair arg arg)
eval (Apply _ _) _ = Left (TypeError "apply expects (closure, argument) pair")

-- Variables and primitives are not directly evaluable without context
eval (Var name) _ = Left (UnboundVariable (show name))
eval (LocalVar name) _ = Left (UnboundVariable ("local: " ++ show name))
eval (FunRef name) _ = Left (UnboundVariable ("funref: " ++ show name))
eval (Prim name _ _) _ = Left (UnboundVariable ("primitive: " ++ show name))

-- String literals evaluate to string values (ignoring the input)
eval (StringLit s) _ = Right (VString s)

-- Recursive types
-- fold and unfold are identity at runtime since Fix F ≅ F (Fix F)
eval (Fold _) v = Right v
eval (Unfold _) v = Right v

-- Let binding: evaluate e1, bind to name, evaluate e2
-- Note: the interpreter doesn't have an environment for local bindings,
-- so let isn't fully supported. For now, we just evaluate e2 with e1's value.
eval (Let _ e1 e2) v = do
  v1 <- eval e1 v
  eval e2 v1

-- Arithmetic expression (OCP-0001)
-- Evaluates MAlonzo ArithIR directly and returns VInt/VFloat for the result
eval (Arith numTy arithExpr) v = evalArith numTy arithExpr v

-- | Check if NumType is floating point.
--
-- `NumType` lost its WIDTHS on the 0.72/0.73 branch — they were a fossil of a
-- rejected design, and the width now comes from the target, not the type. So
-- `F32`/`F64` are gone and the two remaining cases are total: enumerate them
-- rather than keep a catch-all, which would silently absorb a future case.
isFloatType :: MT.T_NumType_6 -> Bool
isFloatType MT.C_NFloat_10 = True
isFloatType MT.C_NInt_8    = False

-- | Evaluate an arithmetic expression (MAlonzo types)
evalArith :: MT.T_NumType_6 -> MA.T_ArithIR_72 -> Value -> Either EvalError Value
evalArith numTy expr v = case expr of
  -- Literal: extract value from AgdaAny based on type
  MA.C_Lit_76 val
    | isFloatType numTy ->
        let f = unsafeCoerce val :: Double
        in Right (VFloat f)
    | otherwise ->
        let n = unsafeCoerce val :: Integer
        in Right (VInt n)

  -- Variable reference (ignore proof)
  MA.C_Var_84 name _ -> valueToArith v

  -- Binary operations (ignore contexts)
  MA.C_Add_92 _ _ e1 e2 -> binOp (+) e1 e2 v
  MA.C_Sub_100 _ _ e1 e2 -> binOp (-) e1 e2 v
  MA.C_Mul_108 _ _ e1 e2 -> binOp (*) e1 e2 v
  -- D055: `/` and `%` are TOTAL, truncated toward zero (Haskell quot/rem),
  -- with a zero divisor yielding -1 (div) / the dividend (rem). This matches
  -- the Word-level `_/ˢ_`/`_%ˢ_` (Once.Word); div/mod (round toward -∞,
  -- partial) would DISAGREE and crash constant-folding on x / 0.
  MA.C_Div_116 _ _ e1 e2 -> binOp d055div e1 e2 v
  MA.C_Mod_124 _ _ e1 e2 -> binOp d055mod e1 e2 v

  -- Unary negation
  MA.C_Neg_130 e -> do
    val <- evalArith numTy e v
    case val of
      VInt n -> Right (VInt (negate n))
      VFloat f -> Right (VFloat (negate f))
      _ -> Left (TypeError "neg expects numeric value")

  -- Comparison
  MA.C_Cmp_138 _ _ op e1 e2 -> cmpOp op e1 e2 v

  -- Type conversion
  MA.C_Conv_146 _ e -> evalArith numTy e v

  where
    -- D055 total signed div/rem over unbounded Integer (no Word wraparound
    -- to model here — this is the compile-time oracle). quot/rem truncate
    -- toward zero; a zero divisor is the total sentinel case.
    d055div :: Integer -> Integer -> Integer
    d055div a b = if b == 0 then -1 else quot a b
    d055mod :: Integer -> Integer -> Integer
    d055mod a b = if b == 0 then a  else rem a b

    binOp :: (Integer -> Integer -> Integer) -> MA.T_ArithIR_72 -> MA.T_ArithIR_72 -> Value -> Either EvalError Value
    binOp f e1 e2 input = do
      v1 <- evalArith numTy e1 input
      v2 <- evalArith numTy e2 input
      case (v1, v2) of
        (VInt n1, VInt n2) -> Right (VInt (f n1 n2))
        _ -> Left (TypeError "binary op expects integer values")

    cmpOp :: MA.T_CmpOp_58 -> MA.T_ArithIR_72 -> MA.T_ArithIR_72 -> Value -> Either EvalError Value
    cmpOp op e1 e2 input = do
      v1 <- evalArith numTy e1 input
      v2 <- evalArith numTy e2 input
      case (v1, v2) of
        (VInt n1, VInt n2) ->
          let cmpFn = case op of
                MA.C_CmpLt_60 -> (<)
                MA.C_CmpLe_62 -> (<=)
                MA.C_CmpGt_64 -> (>)
                MA.C_CmpGe_66 -> (>=)
                MA.C_CmpEq_68 -> (==)
                MA.C_CmpNe_70 -> (/=)
          in Right (VInt (if cmpFn n1 n2 then 1 else 0))
        _ -> Left (TypeError "comparison expects integer values")

    valueToArith :: Value -> Either EvalError Value
    valueToArith (VInt n) = Right (VInt n)
    valueToArith (VFloat f) = Right (VFloat f)
    valueToArith _ = Left (TypeError "expected numeric value")
