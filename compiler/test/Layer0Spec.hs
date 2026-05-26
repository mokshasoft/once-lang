-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 0 codegen tests
--
-- Tests that compile to executables and verify output via exit codes.
-- Uses only Layer 0 constructs: id, composition, primitives.
--
-- Run with: make test-x86-level0
-- Or: cabal test --test-option='-p "/Layer0/"'

module Layer0Spec (layer0Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer0Tests :: TestTree
layer0Tests = testGroup "Layer0"
  [ idTest
  , composeTest
  , constantTest
  , terminalTest
  ]

-- | Test: id function returns its input
-- exit (id 42) should exit with code 42
idTest :: TestTree
idTest = testCase "id returns input (exit 42)" $ do
  result <- buildAndRun "layer0-id" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | Test: composed identities
-- exit ((id . id . id) 42) should exit with code 42
composeTest :: TestTree
composeTest = testCase "composition of ids (exit 42)" $ do
  result <- buildAndRun "layer0-compose" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | Test: constant function
-- exit seven where seven = 7 should exit with code 7
constantTest :: TestTree
constantTest = testCase "constant function (exit 7)" $ do
  result <- buildAndRun "layer0-neg" 7
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | Test: explicit `terminal : A -> Unit`
-- discard 99 yields Unit, fed into a Unit -> Int returning 42.
-- Pins down terminal as a first-class user-facing primitive
-- (previously only exercised implicitly via closure ABI).
terminalTest :: TestTree
terminalTest = testCase "terminal collapses Int to Unit (exit 42)" $ do
  result <- buildAndRun "layer0-terminal" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

------------------------------------------------------------------------
-- Test Helpers
------------------------------------------------------------------------

-- | Build a test program and run it, checking the exit code
buildAndRun :: String -> Int -> IO (Either String ())
buildAndRun name expectedExitCode = do
  let testDir = "/tmp/once_" ++ name
      srcFile = "test/" ++ name ++ ".once"
      exeFile = testDir </> name

  createDirectoryIfMissing True testDir

  -- Copy source to test directory
  source <- TIO.readFile srcFile
  TIO.writeFile (testDir </> name ++ ".once") source

  -- Build with x86_64 target.
  -- --no-optimize: the optimizer currently elides effApp closure
  -- bodies, which collapses `exit 42` to a no-op (Plan 0.2.4.2
  -- known limitation; tracked separately).
  (buildExit, _buildOut, buildErr) <- runOnce
    ["build", "--target", "x86_64", "--no-optimize", "--exe",
     testDir </> name ++ ".once", "-o", exeFile]

  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "Build failed: " ++ buildErr
    ExitSuccess -> do
      -- Run the executable
      (runExit, _runOut, runErr) <- readProcessWithExitCode exeFile [] ""

      cleanupDir testDir

      case runExit of
        ExitFailure code | code == expectedExitCode -> return $ Right ()
        ExitFailure code -> return $ Left $
          "Wrong exit code: expected " ++ show expectedExitCode ++
          " but got " ++ show code
        ExitSuccess -> return $ Left $
          "Expected exit code " ++ show expectedExitCode ++
          " but got 0 (success)"
