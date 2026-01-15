{-# LANGUAGE LambdaCase #-}
-- | Completeness checking for the CCC optimizer
--
-- Verifies that the optimizer can normalize all equivalent terms
-- to the same canonical form.
module CCC.Completeness
  ( CompletenessResult(..)
  , checkCompleteness
  , checkCompletenessForSig
  ) where

import Control.Monad (filterM)
import Data.List (sortBy, groupBy, nubBy)
import Data.Ord (comparing)

import Once.IR (IR(..))
import Once.Type (Type(..))
import Once.Optimize (optimize)

import Common.Enumerate (enumerate, TypeSig(..))
import Common.Equivalence (testEquivalent)
import CCC.Cost (cost, totalCost)
import CCC.Rules (irStructEq, showIR)

-- | Result of completeness check
data CompletenessResult = CompletenessResult
  { crSignature :: TypeSig
  , crTotalClasses :: Int           -- ^ Number of equivalence classes
  , crIncompleteClasses :: Int      -- ^ Classes where optimizer failed
  , crMissingRules :: [(IR, IR)]    -- ^ Pairs (term, expected) that optimizer misses
  }

instance Show CompletenessResult where
  show r = "CompletenessResult { classes=" ++ show (crTotalClasses r)
         ++ ", incomplete=" ++ show (crIncompleteClasses r)
         ++ ", missing=" ++ show (length (crMissingRules r)) ++ " }"

-- | Check completeness for a type signature
--
-- 1. Enumerate all terms up to maxDepth
-- 2. Build equivalence classes via evaluation
-- 3. For each class, optimize all terms and check they're equal
checkCompletenessForSig :: TypeSig -> Int -> Int -> IO CompletenessResult
checkCompletenessForSig sig maxDepth numTests = do
  let terms = enumerate (sigSource sig) (sigTarget sig) maxDepth
  putStrLn $ "Checking completeness for " ++ show (length terms) ++ " terms"

  -- Build equivalence classes
  classes <- buildEquivClasses terms (sigSource sig) numTests
  putStrLn $ "Found " ++ show (length classes) ++ " equivalence classes"

  -- Check each class
  let results = map checkClass classes
      incomplete = filter (not . null . snd) results
      missing = concatMap snd incomplete

  pure CompletenessResult
    { crSignature = sig
    , crTotalClasses = length classes
    , crIncompleteClasses = length incomplete
    , crMissingRules = missing
    }

-- | Check if optimizer normalizes all terms in a class to the same form
--
-- Returns (canonical, [(term, expected) | optimizer fails])
checkClass :: [IR] -> (IR, [(IR, IR)])
checkClass [] = error "Empty equivalence class"
checkClass terms =
  -- Find canonical form (cheapest after optimization)
  let optimized = map (\t -> (t, optimize t)) terms
      canonical = snd $ head $ sortBy (comparing (totalCost . cost . snd)) optimized
      -- Find terms that don't optimize to canonical
      failures = [ (orig, canonical)
                 | (orig, opt) <- optimized
                 , not (irStructEq opt canonical)
                 ]
  in (canonical, failures)

-- | Build equivalence classes (same as in Rules.hs)
buildEquivClasses :: [IR] -> Type -> Int -> IO [[IR]]
buildEquivClasses [] _ _ = pure []
buildEquivClasses (t:ts) srcType numTests = do
  equivs <- filterM (\t' -> testEquivalent t t' srcType numTests) ts
  let thisClass = t : equivs
  let remaining = filter (\x -> not $ any (irStructEq x) equivs) ts
  rest <- buildEquivClasses remaining srcType numTests
  pure (thisClass : rest)

-- | Run completeness check for multiple signatures
checkCompleteness :: [TypeSig] -> Int -> Int -> IO [CompletenessResult]
checkCompleteness sigs maxDepth numTests =
  mapM (\sig -> checkCompletenessForSig sig maxDepth numTests) sigs
