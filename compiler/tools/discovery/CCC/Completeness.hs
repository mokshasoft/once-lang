{-# LANGUAGE LambdaCase #-}
-- | Completeness checking for the CCC optimizer
--
-- Verifies that the optimizer can normalize all equivalent terms
-- to the same canonical form.
--
-- Key optimization: We optimize terms during enumeration, not after.
-- This collapses many equivalent terms to the same normal form early,
-- dramatically reducing the number of equivalence tests needed.
module CCC.Completeness
  ( CompletenessResult(..)
  , checkCompleteness
  , checkCompletenessForSig
  ) where

import Control.Monad (filterM, foldM, when)
import System.IO (hFlush, stdout)

import Once.IR (IR(..))
import Once.Type (Type(..))
import Once.Optimize (optimize)

import Common.Enumerate (enumerate, TypeSig(..), irStructEq)
import Common.Equivalence (testEquivalent)
import CCC.Rules (showIR)

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
-- Optimized algorithm using enumerateNormalized:
-- 1. Enumerate terms, optimizing and deduping during generation
-- 2. Build equivalence classes on the unique normal forms
-- 3. Check that each equivalence class has exactly one normal form
checkCompletenessForSig :: TypeSig -> Int -> Int -> IO CompletenessResult
checkCompletenessForSig sig maxDepth numTests = do
  -- enumerateNormalized optimizes during enumeration and dedupes by normal form
  putStrLn "Enumerating and normalizing terms..."
  normalForms <- enumerateNormalizedWithProgress (sigSource sig) (sigTarget sig) maxDepth
  putStrLn $ "Found " ++ show (length normalForms) ++ " unique normal forms"
  -- Show the normal forms if there are few enough
  when (length normalForms <= 20 && length normalForms > 1) $ do
    putStrLn "Normal forms:"
    mapM_ (putStrLn . ("  " ++) . showIR) normalForms

  -- Build equivalence classes on the normal forms
  classes <- buildEquivClasses normalForms (sigSource sig) numTests
  putStrLn $ "Found " ++ show (length classes) ++ " equivalence classes"

  -- Check each equivalence class - all forms should be structurally equal
  let results = map checkClass classes
      incomplete = filter (not . null . snd) results
      missing = concatMap snd incomplete

  pure CompletenessResult
    { crSignature = sig
    , crTotalClasses = length classes
    , crIncompleteClasses = length incomplete
    , crMissingRules = missing
    }

-- | Enumerate and normalize with progress logging
--
-- Processes terms one by one, optimizing and deduping, with periodic progress updates.
-- Does NOT compute total upfront (which would force full evaluation).
enumerateNormalizedWithProgress :: Type -> Type -> Int -> IO [IR]
enumerateNormalizedWithProgress src tgt maxDepth = do
  let terms = enumerate src tgt maxDepth
  -- Process lazily with progress (don't compute length - that forces evaluation!)
  (count, normalForms) <- foldM processWithProgress (0, []) terms
  putStrLn $ "\nProcessed " ++ show count ++ " terms total"
  pure (reverse normalForms)
  where
    processWithProgress (count, seen) term = do
      let count' = count + 1
          opt = optimize term
      -- Log progress every 500 terms
      when (count' `mod` 500 == 0) $ do
        putStr $ "\rProcessed " ++ show count' ++ " terms, " ++ show (length seen) ++ " unique normal forms"
        hFlush stdout
      -- Add if not seen
      let seen' = if any (irStructEq opt) seen then seen else opt : seen
      pure (count', seen')

-- | Check if all terms in an equivalence class normalize to the same form
--
-- If optimizer is complete, each equivalence class should have exactly
-- one normal form (all terms in the class are structurally equal).
checkClass :: [IR] -> (IR, [(IR, IR)])
checkClass [] = error "Empty equivalence class"
checkClass (canonical:rest) =
  -- All terms should be structurally equal to canonical
  let failures = [ (t, canonical) | t <- rest, not (irStructEq t canonical) ]
  in (canonical, failures)

-- | Build equivalence classes on optimized forms
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
