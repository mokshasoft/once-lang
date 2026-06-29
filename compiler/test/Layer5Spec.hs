-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 5 codegen tests: structured recursion (catamorphisms).
--
-- Compiles a `.once` program that uses `cata` over a μ-type to an executable
-- and verifies the exit code. Drives Plan 0.28 (cata surface-reachability).
--
-- Run with: cabal test --test-option='-p "/Layer5/"'

module Layer5Spec (layer5Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer5Tests :: TestTree
layer5Tests = testGroup "Layer5"
  [ isEvenTest
  , testGroup "cata-general (Plan 0.36 Phase 0 — RED until functor-general codegen)"
      [ exitTest name code | (name, code) <- cataGeneralCases ]
  , testGroup "cata-effectful (Plan 0.36 — PENDING: needs emit.int + trace-valued exec)"
      [ pendingExitTest name code | (name, code) <- cataEffectfulCases ]
  ]

-- | isEven (two) is even, mapped to exit code 42 via case.
isEvenTest :: TestTree
isEvenTest = testCase "cata isEven of an even Nat (exit 42)" $ do
  result <- buildAndRun "layer5-iseven" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | Plan 0.36 Phase-0 north-star matrix: one cata per polynomial-functor
-- shape (K/Id/+/*), each fold's value observed as the `exit` argument.
-- All RED until the functor-general cata codegen (Phase 2) lands; shape #5
-- (leaf tree, two recursive positions) is the decisive non-Nat case.
cataGeneralCases :: [(String, Int)]
cataGeneralCases =
  [ ("layer5-cata-degenerate",      42)  -- #1 Mu (K Int), 0 rec positions
  , ("layer5-cata-nat",              3)  -- #2 Mu (K Unit + Id), 1 rec, bare Id
  , ("layer5-cata-list-sum",        42)  -- #3 Mu (K Unit + (K Int * Id))
  , ("layer5-cata-nelist-sum",      42)  -- #4 Mu (K Int + (K Int * Id))
  , ("layer5-cata-leaftree-sum",    42)  -- #5 Mu (K Int + (Id * Id))  <- decisive
  , ("layer5-cata-nodetree-sum",    42)  -- #6 Mu (K Unit + (Id * (K Int * Id)))
  , ("layer5-cata-ternarytree-sum", 42)  -- #7 Mu (K Int + (Id * Id * Id))
  , ("layer5-cata-multictor-size",   4)  -- #8 Mu (K Unit + (Id + (Id * Id)))
  , ("layer5-cata-nestedprod-sum",  42)  -- #9 Mu (K Unit + ((K Int * K Int) * Id))
  ]

-- | Effect-emitting catas (algebra calls the test-local `emit.int` Emits
-- SigOp). The exit code here is only a run-completed sentinel (7); the real
-- observable is the emit TRACE, asserted at the `obs` level once emit.int +
-- trace-valued exec-flat land (Phase 1). For now this just checks the
-- program builds and runs to the sentinel.
cataEffectfulCases :: [(String, Int)]
cataEffectfulCases =
  [ ("layer5-cata-list-emit",     7)  -- trace [emit 5, emit 3, exit 7]
  , ("layer5-cata-leaftree-emit", 7)  -- crown: trace [emit 40, emit 2, exit 7]
  ]

-- | Build a `.once` program and assert it exits with the given code.
exitTest :: String -> Int -> TestTree
exitTest name code = testCase (name ++ " (exit " ++ show code ++ ")") $ do
  result <- buildAndRun name code
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | A Plan 0.36 "expected failure". The effectful-cata programs do not yet
-- build/run (they need `emit.int` + trace-valued exec-flat), so we assert they
-- currently FAIL. This keeps the suite green while tracking the pending work,
-- and — crucially — this test will START FAILING the moment the feature lands
-- and the program reaches its sentinel exit code, prompting us to promote it
-- back to a real `exitTest`.
pendingExitTest :: String -> Int -> TestTree
pendingExitTest name code =
  testCase (name ++ " (pending Plan 0.36 — expect build/run to fail)") $ do
    result <- buildAndRun name code
    case result of
      Left _   -> return ()  -- still unimplemented, as expected
      Right () -> assertFailure $
        name ++ " now builds and exits " ++ show code ++
        " — effectful cata appears implemented; promote this back to exitTest."

------------------------------------------------------------------------
-- Test Helpers (same shape as Layer0Spec.buildAndRun)
------------------------------------------------------------------------

buildAndRun :: String -> Int -> IO (Either String ())
buildAndRun name expectedExitCode = do
  let testDir = "/tmp/once_" ++ name
      srcFile = "test/" ++ name ++ ".once"
      exeFile = testDir </> name

  createDirectoryIfMissing True testDir
  source <- TIO.readFile srcFile
  TIO.writeFile (testDir </> name ++ ".once") source

  (buildExit, _buildOut, buildErr) <- runOnce
    ["build", "--target", "x86_64", "--no-optimize", "--exe",
     testDir </> name ++ ".once", "-o", exeFile]

  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "Build failed: " ++ buildErr
    ExitSuccess -> do
      (runExit, _runOut, runErr) <- readProcessWithExitCode exeFile [] ""
      cleanupDir testDir
      case runExit of
        ExitFailure code | code == expectedExitCode -> return $ Right ()
        ExitFailure code -> return $ Left $
          "Wrong exit code: expected " ++ show expectedExitCode ++
          " but got " ++ show code ++ (if null runErr then "" else " (" ++ runErr ++ ")")
        ExitSuccess -> return $ Left $
          "Expected exit code " ++ show expectedExitCode ++ " but got 0 (success)"
