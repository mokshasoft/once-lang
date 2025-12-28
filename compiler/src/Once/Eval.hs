module Once.Eval
  ( eval
  , EvalError (..)
  ) where

import Once.IR (IR (..))
import Once.Value (Value (..))
import Once.Arith.IR (ArithIR (..), NumType (..), CmpOp (..))

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
-- Evaluates ArithIR directly and returns VInt for the result
eval (Arith arithExpr) v = evalArith arithExpr v

-- | Evaluate an arithmetic expression
evalArith :: ArithIR -> Value -> Either EvalError Value
evalArith expr v = case expr of
  ALitInt _ n -> Right (VInt n)
  ALitFloat _ f -> Right (VFloat f)
  AVar "_input" _ -> valueToInt v
  AVar name _ -> Left (UnboundVariable ("arith var: " ++ show name))
  AAdd e1 e2 -> binOp (+) e1 e2 v
  ASub e1 e2 -> binOp (-) e1 e2 v
  AMul e1 e2 -> binOp (*) e1 e2 v
  ADiv e1 e2 -> binOp div e1 e2 v
  AMod e1 e2 -> binOp mod e1 e2 v
  ANeg e -> do
    val <- evalArith e v
    case val of
      VInt n -> Right (VInt (negate n))
      VFloat f -> Right (VFloat (negate f))
      _ -> Left (TypeError "neg expects numeric value")
  ACmp op e1 e2 -> cmpOp op e1 e2 v
  where
    binOp :: (Integer -> Integer -> Integer) -> ArithIR -> ArithIR -> Value -> Either EvalError Value
    binOp f e1 e2 input = do
      v1 <- evalArith e1 input
      v2 <- evalArith e2 input
      case (v1, v2) of
        (VInt n1, VInt n2) -> Right (VInt (f n1 n2))
        _ -> Left (TypeError "binary op expects integer values")

    cmpOp :: CmpOp -> ArithIR -> ArithIR -> Value -> Either EvalError Value
    cmpOp op e1 e2 input = do
      v1 <- evalArith e1 input
      v2 <- evalArith e2 input
      case (v1, v2) of
        (VInt n1, VInt n2) ->
          let cmpFn = case op of
                CmpLt -> (<)
                CmpLe -> (<=)
                CmpGt -> (>)
                CmpGe -> (>=)
                CmpEq -> (==)
                CmpNe -> (/=)
          in Right (VInt (if cmpFn n1 n2 then 1 else 0))
        _ -> Left (TypeError "comparison expects integer values")

    valueToInt :: Value -> Either EvalError Value
    valueToInt (VInt n) = Right (VInt n)
    valueToInt _ = Left (TypeError "expected integer value")
