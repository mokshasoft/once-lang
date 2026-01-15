{-# LANGUAGE LambdaCase #-}
-- | CCC Optimization Rule Discovery Tool
--
-- Usage:
--   once-discover ccc --depth 3 --tests 100
--
-- This tool automatically discovers optimization rules by:
-- 1. Enumerating well-typed CCC terms
-- 2. Finding cheaper equivalents via evaluation testing
-- 3. Reporting discovered rules
module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import Control.Monad (forM_)

import Once.Type (Type(..))
import Common.Enumerate (TypeSig(..))
import CCC.Rules (DiscoveredRule, discoverRules, showRule, showIR)
import CCC.Completeness (CompletenessResult(..), checkCompletenessForSig)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("ccc" : rest) -> runCCCDiscovery rest
    ("completeness" : rest) -> runCompletenessCheck rest
    _ -> usage

usage :: IO ()
usage = do
  putStrLn "Usage: once-discover <command> [options]"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  ccc           Discover CCC optimization rules"
  putStrLn "  completeness  Check optimizer completeness"
  putStrLn ""
  putStrLn "Options:"
  putStrLn "  --depth N   Maximum term depth (default: 3)"
  putStrLn "  --tests N   Number of test values (default: 100)"
  exitFailure

-- | Parse command-line options
parseOpts :: [String] -> (Int, Int)
parseOpts = go (3, 100)
  where
    go acc [] = acc
    go (_, t) ("--depth" : n : rest) = go (read n, t) rest
    go (d, _) ("--tests" : n : rest) = go (d, read n) rest
    go acc (_ : rest) = go acc rest

-- | Run CCC optimization discovery
runCCCDiscovery :: [String] -> IO ()
runCCCDiscovery args = do
  let (maxDepth, numTests) = parseOpts args

  putStrLn "=== CCC Optimization Rule Discovery ==="
  putStrLn $ "Depth: " ++ show maxDepth
  putStrLn $ "Tests: " ++ show numTests
  putStrLn ""

  -- Define type signatures to explore
  let tA = TVar "A"
      tB = TVar "B"
      -- Focused signatures for exponential beta/eta discovery
      expSignatures =
        [ -- Key type for exponential beta: apply . ⟨curry(f) . fst, snd⟩ = f
          TypeSig (TProduct tA tB) tB                           -- (A * B) -> B
        , TypeSig (TProduct (TArrow tA tB) tA) tB                -- (A -> B) * A -> B (apply)
        , TypeSig tA (TArrow tA tA)                              -- A -> (A -> A) for eta
        ]
      -- Standard product/sum signatures
      basicSignatures =
        [ TypeSig (TProduct tA tB) tA           -- A * B -> A
        , TypeSig (TProduct tA tB) tB           -- A * B -> B
        , TypeSig tA (TProduct tA tA)           -- A -> A * A
        , TypeSig (TProduct tA tB) (TProduct tA tB)  -- A * B -> A * B
        , TypeSig tA tA                         -- A -> A (identity)
        , TypeSig (TSum tA tB) tA               -- A + B -> A (partial)
        , TypeSig tA (TSum tA tB)               -- A -> A + B
        ]
      signatures = expSignatures ++ basicSignatures

  -- Discover rules for each signature
  allRules <- concat <$> mapM (discoverForSig maxDepth numTests) signatures

  -- Report results
  putStrLn ""
  putStrLn $ "=== Discovered " ++ show (length allRules) ++ " rules ==="
  putStrLn ""
  forM_ allRules $ \rule -> do
    putStrLn $ "  " ++ showRule rule

-- | Discover rules for a single type signature
discoverForSig :: Int -> Int -> TypeSig -> IO [DiscoveredRule]
discoverForSig maxDepth numTests sig = do
  putStrLn $ "Exploring: " ++ showSig sig
  rules <- discoverRules sig maxDepth numTests
  putStrLn $ "  Found " ++ show (length rules) ++ " rules"
  pure rules

-- | Show a type signature
showSig :: TypeSig -> String
showSig (TypeSig src tgt) = showType src ++ " -> " ++ showType tgt

-- | Show a type
showType :: Type -> String
showType = \case
  TUnit -> "Unit"
  TVoid -> "Void"
  TVar n -> show n
  TInt -> "Int"
  TFloat -> "Float"
  TProduct a b -> "(" ++ showType a ++ " * " ++ showType b ++ ")"
  TSum a b -> "(" ++ showType a ++ " + " ++ showType b ++ ")"
  TArrow a b -> "(" ++ showType a ++ " → " ++ showType b ++ ")"
  _ -> "?"

-- | Run completeness check
runCompletenessCheck :: [String] -> IO ()
runCompletenessCheck args = do
  let (maxDepth, numTests) = parseOpts args

  putStrLn "=== Optimizer Completeness Check ==="
  putStrLn $ "Depth: " ++ show maxDepth
  putStrLn $ "Tests: " ++ show numTests
  putStrLn ""

  -- Type signatures to check
  let tA = TVar "A"
      tB = TVar "B"
      signatures =
        [ TypeSig tA tA                                -- A -> A
        , TypeSig (TProduct tA tB) tA                  -- A * B -> A
        , TypeSig (TProduct tA tB) tB                  -- A * B -> B
        , TypeSig (TProduct tA tB) (TProduct tA tB)    -- A * B -> A * B
        , TypeSig tA (TProduct tA tA)                  -- A -> A * A
        ]

  -- Check each signature
  results <- mapM (checkSig maxDepth numTests) signatures

  -- Summary
  putStrLn ""
  putStrLn "=== Summary ==="
  let totalMissing = sum $ map (length . crMissingRules) results
  if totalMissing == 0
    then putStrLn "✓ Optimizer is complete for all tested signatures!"
    else do
      putStrLn $ "✗ Found " ++ show totalMissing ++ " missing optimizations:"
      forM_ results $ \r ->
        forM_ (crMissingRules r) $ \(term, expected) ->
          putStrLn $ "  " ++ showIR term ++ "  should optimize to  " ++ showIR expected

-- | Check completeness for a single signature
checkSig :: Int -> Int -> TypeSig -> IO CompletenessResult
checkSig maxDepth numTests sig = do
  putStrLn $ "Checking: " ++ showSig sig
  result <- checkCompletenessForSig sig maxDepth numTests
  putStrLn $ "  Classes: " ++ show (crTotalClasses result)
           ++ ", Incomplete: " ++ show (crIncompleteClasses result)
  pure result
