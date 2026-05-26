-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 2 codegen tests — Sums: inl, inr, destruct
--
-- Layer 2 adds sum construction (inl/inr) and elimination (destruct)
-- on top of Layer 1.
--
-- These tests use direct type annotations `(inl x : Int + Int)` for
-- sum construction. Sums returned from user-defined functions
-- (e.g. `mkSum x = inl x : Int + Int`) currently don't round-trip
-- through the destruct dispatch correctly — the function call wraps
-- the result through `apply`, which breaks the tag-at-offset-0 layout
-- the destruct dispatch expects. That's a separate (layer 4+) issue.
--
-- Plan 0.13.1 Phase 6 + 7. Validates that:
--   - inl/inr construct (tag, payload) pairs in the right layout
--     (IRToTrace 5-instr lowering).
--   - destruct dispatches via `cmpq $0, (%rdi); je` based on tag
--     (x86-64 case-on-tag codegen).
--
-- Run with: cabal test --test-option='-p "/Layer2/"'

module Layer2Spec (layer2Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer2Tests :: TestTree
layer2Tests = testGroup "Layer2"
  [ caseInlTest
  , caseInrTest
  , initialTest
  ]

-- | destruct ((inl 42) : Int + Int) of { Left x -> x ; Right y -> 99 }
-- should exit with code 42 (the Left branch fires; payload = 42)
caseInlTest :: TestTree
caseInlTest = testCase "destruct on inl selects Left branch (exit 42)" $ do
  result <- buildAndRun "layer2-case-inl-direct" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | destruct ((inr 99) : Int + Int) of { Left x -> 42 ; Right y -> y }
-- should exit with code 99 (the Right branch fires; payload = 99)
caseInrTest :: TestTree
caseInrTest = testCase "destruct on inr selects Right branch (exit 99)" $ do
  result <- buildAndRun "layer2-case-inr-direct" 99
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | `initial : Void -> A` (ex falso quodlibet), the dual of `terminal`.
-- Encoded as the Right branch of an `Int + Void` sum so it type-checks;
-- the Left branch fires at runtime so initial is never called
-- dynamically (Void has no values). Guards that initial keeps linking
-- as a CCT2 primitive.
initialTest :: TestTree
initialTest = testCase "initial typechecks/links as Void -> A (exit 42)" $ do
  result <- buildAndRun "layer2-initial" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

------------------------------------------------------------------------
-- Test Helpers (mirrors Layer1Spec)
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
