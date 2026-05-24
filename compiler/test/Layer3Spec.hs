-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 3 codegen tests — nested combinations of Layer 1 (products)
-- and Layer 2 (sums).
--
-- These exercise the cumulative behaviour with `--alloc heap`:
-- pairs containing sums, sums containing pairs, deeper nestings.
-- All currently pass on the heap-only-pivot branch.
--
-- Run with: cabal test --test-option='-p "/Layer3/"'

module Layer3Spec (layer3Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer3Tests :: TestTree
layer3Tests = testGroup "Layer3"
  [ testCase "pair nested inside a sum (exit 42)" $
      buildAndRun "layer3-pair-in-sum" 42 >>= either assertFailure return
  , testCase "sum nested inside a pair (exit 42)" $
      buildAndRun "layer3-sum-in-pair" 42 >>= either assertFailure return
  , testCase "nested-mix: pair / sum / pair (exit 42)" $
      buildAndRun "layer3-nested-mix" 42 >>= either assertFailure return
  ]

------------------------------------------------------------------------
-- Test Helpers (mirrors Layer4Spec, --alloc heap)
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
     "--alloc", "heap",
     testDir </> name ++ ".once", "-o", exeFile]

  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "Build failed: " ++ buildErr
    ExitSuccess -> do
      (runExit, _runOut, _runErr) <- readProcessWithExitCode exeFile [] ""

      cleanupDir testDir

      case runExit of
        ExitFailure code | code == expectedExitCode -> return $ Right ()
        ExitFailure code -> return $ Left $
          "Wrong exit code: expected " ++ show expectedExitCode ++
          " but got " ++ show code
        ExitSuccess -> return $ Left $
          "Expected exit code " ++ show expectedExitCode ++
          " but got 0 (success)"
