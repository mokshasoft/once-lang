-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Optimizer trace-preservation tests (Plan 0.44 / 0.46).
--
-- The observable of a Once program is its ordered SigOp trace; the grand
-- theorem (Once.Adequacy.Compile.correct) says the compiled bytes emit the
-- same trace as the source. For the OPTIMIZED pipeline that correctness is
-- currently POSTULATED (the `opt-trace` postulate), and tests/run-exit-tests.sh
-- warns the optimizer's `terminal ∘ f = terminal` rule could silently drop
-- effectful SigOps. Yet every other codegen test in this suite builds with
-- `--no-optimize`, so the optimized path's observable behaviour was untested.
--
-- These tests build representative Layer 0-5 + arith programs BOTH with the
-- optimizer (the default) and with `--no-optimize`, and assert the two runs
-- produce the SAME exit code — i.e. the optimizer preserves the (Layer-0)
-- observable. For Layer 0 the trace is exactly `[(exit, N)]`, so the exit code
-- IS the observable; a richer multi-SigOp/stdout trace test is not yet possible
-- because the only working observable effect on the x86_64 backend is the exit
-- syscall (the File/println interpretation does not parse and `emit` is pending).
module OptimizeSpec (optimizeTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

optimizeTests :: TestTree
optimizeTests = testGroup "Optimizer trace preservation"
  [ testGroup "optimized exit code matches --no-optimize"
      [ differentialTest name alloc | (name, alloc) <- fixtures ]
  , testGroup "optimized build still produces the correct exit code"
      [ optimizedExitTest name code alloc | (name, code, alloc) <- correctnessFixtures ]
  ]

-- | (fixture, allocation strategy). Spread across the categorical layers and
-- the arith lowering so the differential covers projections, sums, closures,
-- catamorphisms and arith blocks.
fixtures :: [(String, String)]
fixtures =
  [ ("layer0-id",              "stack")
  , ("layer0-terminal",        "stack")
  , ("layer1-fst",             "stack")
  , ("layer1-snd-deep",        "stack")
  , ("layer2-case-inl-direct", "stack")
  , ("layer3-pair-in-sum",     "stack")
  , ("layer3-sum-in-pair",     "stack")
  , ("layer4-keep-fst",        "heap")
  , ("layer4-twice",           "heap")
  , ("layer4-closure-in-pair", "heap")
  , ("layer5-iseven",          "stack")
  , ("arith-simple",           "heap")
  , ("arith-lambda-1",         "heap")
  ]

-- | A few fixtures whose exact exit code we also pin on the OPTIMIZED path
-- (the un-optimized values are already pinned by the Layer*/Arith specs).
correctnessFixtures :: [(String, Int, String)]
correctnessFixtures =
  [ ("layer2-case-inl-direct", 42, "stack")
  , ("arith-simple",           13, "heap")
  , ("layer4-keep-fst",        42, "heap")
  ]

-- | Build `name` both optimized and unoptimized and assert the exit codes agree.
differentialTest :: String -> String -> TestTree
differentialTest name alloc =
  testCase (name ++ " (opt == no-opt)") $ do
    optE   <- buildAndExit name alloc Optimized
    noOptE <- buildAndExit name alloc NoOptimize
    case (optE, noOptE) of
      (Right o, Right n)
        | o == n    -> return ()
        | otherwise -> assertFailure $
            name ++ ": optimizer changed the observable — optimized exit " ++
            show o ++ " /= --no-optimize exit " ++ show n
      (Left e, _) -> assertFailure $ "optimized build/run failed: " ++ e
      (_, Left e) -> assertFailure $ "--no-optimize build/run failed: " ++ e

-- | Build `name` optimized and assert it exits with the expected code.
optimizedExitTest :: String -> Int -> String -> TestTree
optimizedExitTest name code alloc =
  testCase (name ++ " optimized (exit " ++ show code ++ ")") $ do
    e <- buildAndExit name alloc Optimized
    case e of
      Right got
        | got == code -> return ()
        | otherwise   -> assertFailure $
            "optimized " ++ name ++ ": expected exit " ++ show code ++
            " but got " ++ show got
      Left err -> assertFailure err

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

data OptMode = Optimized | NoOptimize

-- | Build a fixture and return its process exit code (Right) or an error.
buildAndExit :: String -> String -> OptMode -> IO (Either String Int)
buildAndExit name alloc mode = do
  let tag = case mode of Optimized -> "opt"; NoOptimize -> "noopt"
      testDir = "/tmp/once_opt_" ++ name ++ "_" ++ tag
      exeFile = testDir </> name
  createDirectoryIfMissing True testDir
  source <- TIO.readFile ("test/" ++ name ++ ".once")
  TIO.writeFile (testDir </> name ++ ".once") source

  let optArgs = case mode of Optimized -> []; NoOptimize -> ["--no-optimize"]
  (buildExit, _out, buildErr) <- runOnce $
    ["build", "--target", "x86_64", "--exe", "--alloc", alloc] ++ optArgs ++
    [testDir </> name ++ ".once", "-o", exeFile]

  case buildExit of
    ExitFailure _ -> cleanupDir testDir >> return (Left ("build failed: " ++ buildErr))
    ExitSuccess -> do
      (runExit, _, _) <- readProcessWithExitCode exeFile [] ""
      cleanupDir testDir
      return $ Right $ case runExit of
        ExitSuccess   -> 0
        ExitFailure c -> c
