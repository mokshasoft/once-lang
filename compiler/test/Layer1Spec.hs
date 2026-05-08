-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 1 codegen tests — Products: ⟨_,_⟩, fst, snd
--
-- Tests that compile to executables and verify output via exit codes.
-- Layer 1 adds pair construction and projection on top of Layer 0.
--
-- The current tests cover ground pair expressions in `main`'s body:
-- bare projections (`fst (a, b)`), nested pairs, and compose chains
-- of `snd` morphisms (which collapse through the morphism-realm
-- bypass, Plan 0.2.4.5 D2, to pure CCC compose).
--
-- User-defined Layer 1 functions (`swap p = (snd p, fst p)`) compile
-- without the thunk-label collision (Plan 0.12 fix) but still hit
-- the closure-realm dangling-pointer bug at runtime — tracked as the
-- open closure-ABI fix in `plans/0.2.4.5-morphism-realm-split.md`.
-- See `test/layer1-swap.once` for the demonstrating source.
--
-- Run with: cabal test --test-option='-p "/Layer1/"'

module Layer1Spec (layer1Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer1Tests :: TestTree
layer1Tests = testGroup "Layer1"
  [ fstTest
  , sndDeepTest
  , composeSndTest
  ]

-- | exit (fst (42, 99)) should exit with code 42
fstTest :: TestTree
fstTest = testCase "fst projects first component (exit 42)" $ do
  result <- buildAndRun "layer1-fst" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | exit (snd (snd (snd (1, (2, (3, 42)))))) should exit with code 42
sndDeepTest :: TestTree
sndDeepTest = testCase "deeply-nested snd (exit 42)" $ do
  result <- buildAndRun "layer1-snd-deep" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

-- | exit ((snd . snd . snd) (1, (2, (3, 42)))) should exit with code 42
-- Exercises the morphism-realm compose bypass for non-id morphisms.
composeSndTest :: TestTree
composeSndTest = testCase "compose chain of snd morphisms (exit 42)" $ do
  result <- buildAndRun "layer1-compose-snd" 42
  case result of
    Left err -> assertFailure err
    Right () -> return ()

------------------------------------------------------------------------
-- Test Helpers (mirrors Layer0Spec)
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
