module Once.Optimize
  ( optimize
  , optimizeOnce
  , optimizeWithMAlonzo
  , OptimizerBackend (..)
  , optimizeWith
  ) where

import Once.IR (IR (..))
import Once.Type (Type (..))
import qualified Once.MAlonzo as M

-- | Which optimizer backend to use
data OptimizerBackend
  = HaskellOptimizer   -- ^ Use the Haskell optimizer (default)
  | MAlonzoOptimizer   -- ^ Use the verified MAlonzo optimizer (when possible)
  deriving (Eq, Show)

-- | Optimize with the specified backend
optimizeWith :: OptimizerBackend -> IR -> IR
optimizeWith HaskellOptimizer = optimize
optimizeWith MAlonzoOptimizer = optimizeWithMAlonzo

-- | Optimize using MAlonzo (verified) if possible, fallback to Haskell
--
-- The MAlonzo optimizer is generated from verified Agda code.
-- It can only optimize IR that:
-- - Uses only categorical types (Unit, Void, Product, Sum, Arrow, Eff, Fix)
-- - Does not contain Var, LocalVar, FunRef, or StringLit
--
-- For IR that cannot be converted, falls back to the Haskell optimizer.
optimizeWithMAlonzo :: IR -> IR
optimizeWithMAlonzo ir
  | M.canConvertIR ir = M.optimizeMAlonzo ir
  | otherwise = optimize ir  -- Fallback to Haskell

-- | Optimize IR by applying categorical rewrite rules until fixed point
optimize :: IR -> IR
optimize ir =
  let ir' = optimizeOnce ir
  in if ir' == ir then ir else optimize ir'

-- | Apply one pass of optimization rules
optimizeOnce :: IR -> IR
optimizeOnce ir = case ir of
  -- Recursively optimize subterms first
  Compose g f -> simplifyCompose (optimizeOnce g) (optimizeOnce f)
  Pair f g -> simplifyPair (optimizeOnce f) (optimizeOnce g)
  Case f g -> simplifyCase (optimizeOnce f) (optimizeOnce g)
  Curry f -> Curry (optimizeOnce f)
  -- Leaves: no subterms to optimize
  _ -> ir

-- | Simplify composition using categorical laws
simplifyCompose :: IR -> IR -> IR
simplifyCompose g f = case (g, f) of
  -- Identity laws: f ∘ id = f, id ∘ f = f
  (_, Id _) -> g
  (Id _, _) -> f

  -- Product laws
  -- fst ∘ pair f g = f
  (Fst _ _, Pair h _) -> h
  -- snd ∘ pair f g = g
  (Snd _ _, Pair _ k) -> k

  -- Coproduct laws
  -- case f g ∘ inl = f
  (Case h _, Inl _ _) -> h
  -- case f g ∘ inr = g
  (Case _ k, Inr _ _) -> k

  -- Recursive type laws (Fix isomorphism)
  -- fold ∘ unfold = id : Fix F -> Fix F
  (Fold t, Unfold t') | t == t' -> Id (TFix t)
  -- unfold ∘ fold = id : F (Fix F) -> F (Fix F)
  (Unfold t, Fold t') | t == t' -> Id t

  -- Composition associativity: normalize to right-associative
  -- (h ∘ g) ∘ f = h ∘ (g ∘ f)
  -- This helps expose more optimization opportunities
  (Compose h g', f') -> simplifyCompose h (simplifyCompose g' f')

  -- No simplification applies
  _ -> Compose g f

-- | Simplify pair using categorical laws
simplifyPair :: IR -> IR -> IR
simplifyPair f g = case (f, g) of
  -- pair fst snd = id (on products)
  -- fst : A * B -> A, snd : A * B -> B
  -- pair fst snd : A * B -> A * B = id
  (Fst a b, Snd a' b') | a == a' && b == b' -> Id (TProduct a b)
  -- No simplification applies
  _ -> Pair f g

-- | Simplify case using categorical laws
simplifyCase :: IR -> IR -> IR
simplifyCase f g = case (f, g) of
  -- case inl inr = id (on sums)
  -- inl : A -> A + B, inr : B -> A + B
  -- case inl inr : A + B -> A + B = id
  (Inl a b, Inr a' b') | a == a' && b == b' -> Id (TSum a b)
  -- No simplification applies
  _ -> Case f g

-- Note: fold and unfold optimizations
-- fold ∘ unfold = id : Fix F -> Fix F
-- unfold ∘ fold = id : F (Fix F) -> F (Fix F)
-- These are added in simplifyCompose when needed for recursion scheme fusion
