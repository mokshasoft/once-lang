{-# LANGUAGE LambdaCase #-}
-- | CCC optimization rule discovery
--
-- This module discovers optimization rules by:
-- 1. Enumerating well-typed IR terms
-- 2. Finding pairs where one is cheaper than the other
-- 3. Testing semantic equivalence via evaluation
-- 4. Shrinking to remove redundant/derived rules
module CCC.Rules
  ( DiscoveredRule(..)
  , discoverRules
  , showRule
  , showIR
  , irStructEq
  ) where

import Control.Monad (filterM)
import Data.List (sortBy, minimumBy, nubBy)
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
-- 2. Group terms into equivalence classes
-- 3. For each class, rules map to the cheapest (normal form)
-- 4. Shrink to remove redundant rules
discoverRules :: TypeSig -> Int -> Int -> IO [DiscoveredRule]
discoverRules sig maxDepth numTests = do
  let terms = enumerate (sigSource sig) (sigTarget sig) maxDepth
  putStrLn $ "Enumerated " ++ show (length terms) ++ " terms"

  -- Build equivalence classes
  classes <- buildEquivClasses terms (sigSource sig) numTests
  putStrLn $ "Found " ++ show (length classes) ++ " equivalence classes"

  -- For each class, find the normal form (cheapest) and create rules
  let rules = concatMap classToRules classes

  -- Shrink: remove rules with identity noise in source
  let shrunkRules = filter (not . hasIdentityNoise . ruleSource) rules

  -- Deduplicate by normalized form
  let dedupedRules = nubBy sameRule shrunkRules

  -- Create rule records and sort by cost saved
  let ruleRecords =
        [ DiscoveredRule
          { ruleSource = src
          , ruleTarget = tgt
          , ruleSig = sig
          , ruleCostSaved = totalCost (cost src) - totalCost (cost tgt)
          }
        | DiscoveredRule src tgt _ _ <- dedupedRules
        ]

  pure $ sortBy (comparing (Down . ruleCostSaved)) ruleRecords

-- | Build equivalence classes from a list of terms
buildEquivClasses :: [IR] -> Type -> Int -> IO [[IR]]
buildEquivClasses [] _ _ = pure []
buildEquivClasses (t:ts) srcType numTests = do
  -- Find all terms equivalent to t
  equivs <- filterM (\t' -> testEquivalent t t' srcType numTests) ts
  let thisClass = t : equivs
  -- Continue with remaining terms (those not in equivs)
  let remaining = filter (\x -> not $ any (irStructEq x) equivs) ts
  rest <- buildEquivClasses remaining srcType numTests
  pure (thisClass : rest)

-- | Convert an equivalence class to rules (all terms -> cheapest)
classToRules :: [IR] -> [DiscoveredRule]
classToRules [] = []
classToRules terms =
  let normalForm = minimumBy (comparing (totalCost . cost)) terms
      normalCost = totalCost (cost normalForm)
      -- Filter out the normal form itself using structural equality
      others = filter (not . irStructEq normalForm) terms
  in [ DiscoveredRule src normalForm (TypeSig TUnit TUnit) 0
     | src <- others
     , totalCost (cost src) > normalCost
     ]

-- | Check if two rules are essentially the same
sameRule :: DiscoveredRule -> DiscoveredRule -> Bool
sameRule r1 r2 =
  irStructEq (ruleSource r1) (ruleSource r2) &&
  irStructEq (ruleTarget r1) (ruleTarget r2)

-- | Structural equality for IR (ignoring type annotations)
irStructEq :: IR -> IR -> Bool
irStructEq (Id _) (Id _) = True
irStructEq (Compose g1 f1) (Compose g2 f2) = irStructEq g1 g2 && irStructEq f1 f2
irStructEq (Fst _ _) (Fst _ _) = True
irStructEq (Snd _ _) (Snd _ _) = True
irStructEq (Pair f1 g1) (Pair f2 g2) = irStructEq f1 f2 && irStructEq g1 g2
irStructEq (Terminal _) (Terminal _) = True
irStructEq (Initial _) (Initial _) = True
irStructEq (Inl _ _) (Inl _ _) = True
irStructEq (Inr _ _) (Inr _ _) = True
irStructEq (Case f1 g1) (Case f2 g2) = irStructEq f1 f2 && irStructEq g1 g2
irStructEq (Curry _ f1) (Curry _ f2) = irStructEq f1 f2
irStructEq (Apply _ _) (Apply _ _) = True
irStructEq (Fold _) (Fold _) = True
irStructEq (Unfold _) (Unfold _) = True
irStructEq _ _ = False

-- | Check if a term has unnecessary identity compositions
-- e.g., "id . f" or "f . id" where we could just have "f"
hasIdentityNoise :: IR -> Bool
hasIdentityNoise = \case
  Compose (Id _) _ -> True           -- id . f
  Compose _ (Id _) -> True           -- f . id
  Compose g f -> hasIdentityNoise g || hasIdentityNoise f
  Pair f g -> hasIdentityNoise f || hasIdentityNoise g
  Case f g -> hasIdentityNoise f || hasIdentityNoise g
  Curry _ f -> hasIdentityNoise f
  _ -> False

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
