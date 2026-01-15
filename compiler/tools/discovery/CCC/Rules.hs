{-# LANGUAGE LambdaCase #-}
-- | CCC optimization rule discovery
--
-- This module discovers optimization rules by:
-- 1. Enumerating well-typed IR terms
-- 2. Finding pairs where one is cheaper than the other
-- 3. Testing semantic equivalence via evaluation
module CCC.Rules
  ( DiscoveredRule(..)
  , discoverRules
  , showRule
  , showIR
  ) where

import Control.Monad (filterM)
import Data.List (sortBy)
import Data.Ord (comparing, Down(..))

import Once.IR (IR(..))
import Once.Type (Type(..))

import Common.Enumerate (enumerate, TypeSig(..))
import Common.Equivalence (testEquivalent)
import CCC.Cost (cost, totalCost, cheaper)

-- | A discovered optimization rule
data DiscoveredRule = DiscoveredRule
  { ruleSource :: IR          -- ^ Original (more expensive) term
  , ruleTarget :: IR          -- ^ Optimized (cheaper) term
  , ruleSig :: TypeSig        -- ^ Type signature
  , ruleCostSaved :: Int      -- ^ Cost reduction
  }

instance Show DiscoveredRule where
  show r = "DiscoveredRule { " ++ showIR (ruleSource r) ++ " -> " ++ showIR (ruleTarget r) ++ " }"

-- | Discover optimization rules for a given type signature
--
-- 1. Enumerate all terms up to maxDepth
-- 2. For each pair where t2 is cheaper than t1
-- 3. Test if they're semantically equivalent
-- 4. Return as optimization rules
discoverRules :: TypeSig -> Int -> Int -> IO [DiscoveredRule]
discoverRules sig maxDepth numTests = do
  let terms = enumerate (sigSource sig) (sigTarget sig) maxDepth
  putStrLn $ "Enumerated " ++ show (length terms) ++ " terms"

  -- Generate all pairs where target is cheaper
  let candidates =
        [ (t1, t2)
        | t1 <- terms
        , t2 <- terms
        , cheaper t2 t1  -- t2 is cheaper than t1
        ]
  putStrLn $ "Found " ++ show (length candidates) ++ " candidate pairs"

  -- Test equivalence for each candidate
  rules <- filterM (testPair sig numTests) candidates

  -- Create rule records and sort by cost saved
  let ruleRecords =
        [ DiscoveredRule
          { ruleSource = expensive
          , ruleTarget = cheap
          , ruleSig = sig
          , ruleCostSaved = totalCost (cost expensive) - totalCost (cost cheap)
          }
        | (expensive, cheap) <- rules
        ]

  pure $ sortBy (comparing (Down . ruleCostSaved)) ruleRecords

-- | Test if a candidate pair is equivalent
testPair :: TypeSig -> Int -> (IR, IR) -> IO Bool
testPair sig numTests (t1, t2) =
  testEquivalent t1 t2 (sigSource sig) numTests

-- | Pretty-print an IR term in a readable format
showIR :: IR -> String
showIR = \case
  Id _ -> "id"
  Compose g f -> showIR g ++ " . " ++ showIR f
  Fst _ _ -> "fst"
  Snd _ _ -> "snd"
  Pair f g -> "⟨" ++ showIR f ++ ", " ++ showIR g ++ "⟩"
  Terminal _ -> "terminal"
  Initial _ -> "initial"
  Inl _ _ -> "inl"
  Inr _ _ -> "inr"
  Case f g -> "[" ++ showIR f ++ ", " ++ showIR g ++ "]"
  Curry _ f -> "curry(" ++ showIR f ++ ")"
  Apply _ _ -> "apply"
  Fold _ -> "fold"
  Unfold _ -> "unfold"
  Var n -> "var(" ++ show n ++ ")"
  LocalVar n -> "local(" ++ show n ++ ")"
  FunRef n -> "ref(" ++ show n ++ ")"
  Prim n _ _ -> "prim(" ++ show n ++ ")"
  StringLit s -> show s
  Let n e1 e2 -> "let " ++ show n ++ " = " ++ showIR e1 ++ " in " ++ showIR e2
  Arith _ _ -> "arith(...)"

-- | Pretty-print a discovered rule
showRule :: DiscoveredRule -> String
showRule rule = concat
  [ showIR (ruleSource rule)
  , "  -->  "
  , showIR (ruleTarget rule)
  , "  (saves "
  , show (ruleCostSaved rule)
  , " cost)"
  ]

-- | Pretty-print a type
showType :: Type -> String
showType = \case
  TUnit -> "Unit"
  TVoid -> "Void"
  TVar n -> show n
  TInt -> "Int"
  TFloat -> "Float"
  TProduct a b -> showType a ++ " * " ++ showType b
  TSum a b -> showType a ++ " + " ++ showType b
  TArrow a b -> showType a ++ " -> " ++ showType b
  _ -> "?"
