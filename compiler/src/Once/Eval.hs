module Once.Eval
  ( eval
  , EvalError (..)
  ) where

import Once.IR (IR (..))
import Once.Value (Value (..))

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
eval (Curry f) v = Right (VClosure [(f, v)] f)

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
