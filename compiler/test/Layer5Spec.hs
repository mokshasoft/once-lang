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
  ]

-- | isEven (two) is even, mapped to exit code 42 via case.
isEvenTest :: TestTree
isEvenTest = testCase "cata isEven of an even Nat (exit 42)" $ do
  result <- buildAndRun "layer5-iseven" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

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
