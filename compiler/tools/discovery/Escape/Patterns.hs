{-# LANGUAGE LambdaCase #-}
-- | Escape analysis pattern discovery (STUB)
--
-- Discovers patterns where escape analysis could optimize Heap → Stack
-- but currently doesn't.
--
-- NOTE: This is a stub. Full implementation requires AllocMode in the
-- Haskell IR (Pair, Inl, Inr, Curry need AllocMode parameter).
-- The IR changes are in a separate branch.
--
-- When implemented, this will:
-- 1. Enumerate IR terms with Heap allocations
-- 2. Run escape analysis
-- 3. Check if allocations that *could* be Stack are correctly identified
-- 4. Report missing patterns
module Escape.Patterns
  ( EscapeResult(..)
  , checkEscapeCompleteness
  , checkEscapeForSig
  ) where

import Common.Enumerate (TypeSig(..))

-- | Result of escape completeness check
data EscapeResult = EscapeResult
  { erSignature :: TypeSig
  , erTotalTerms :: Int
  , erHeapRemaining :: Int      -- ^ Terms with Heap allocs after escape analysis
  , erMissedPatterns :: Int     -- ^ Count of potentially missed optimizations
  } deriving (Show)

-- | Check escape analysis completeness for a type signature (STUB)
checkEscapeForSig :: TypeSig -> Int -> Int -> IO EscapeResult
checkEscapeForSig sig _maxDepth _numTests = do
  putStrLn "Escape analysis discovery not yet implemented."
  putStrLn "Requires AllocMode in Haskell IR (see escape branch)."
  pure EscapeResult
    { erSignature = sig
    , erTotalTerms = 0
    , erHeapRemaining = 0
    , erMissedPatterns = 0
    }

-- | Run escape check for multiple signatures (STUB)
checkEscapeCompleteness :: [TypeSig] -> Int -> Int -> IO [EscapeResult]
checkEscapeCompleteness sigs maxDepth numTests =
  mapM (\sig -> checkEscapeForSig sig maxDepth numTests) sigs
