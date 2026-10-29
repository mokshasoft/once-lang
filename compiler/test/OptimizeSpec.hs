-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Optimizer tests (Plan 0.44 / 0.46 / 0.39).
--
-- The observable of a Once program is its ordered SigOp trace, and the
-- optimizer keeps it (D347: `opt-trace` is a theorem, from
-- `Once.Adequacy.OptimizePreserves`). These tests check the compiled side:
--
--   * the optimizer's rules FIRE on elaborated code: `opt-rules.once` holds a
--     redex per rule that elaborated code reaches, and its IR is checked
--     before (`once elaborate`) and after (`once optimize`). The rules only
--     hand-built IR reaches are shown in `Once.Optimize.Examples`;
--   * that program's trace, with and without the optimizer (`traceCases`);
--   * representative Layer 0-5 + arith programs exit alike built both ways
--     (the exit suites in `tests/` do the same for every program).
module OptimizeSpec (optimizeTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.List (isInfixOf, stripPrefix)
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir, traceCases)

optimizeTests :: TestTree
optimizeTests = testGroup "Optimizer"
  [ testGroup "rules fire on elaborated code (opt-rules.once)"
      [ ruleTest fn rule before after | (fn, rule, before, after) <- ruleFixtures ]
  , traceCases "opt-rules.once keeps its trace" "opt-rules" [5, 6] 7
  , testGroup "optimized exit code matches --no-optimize"
      [ differentialTest name alloc | (name, alloc) <- fixtures ]
  , testGroup "optimized build still produces the correct exit code"
      [ optimizedExitTest name code alloc | (name, code, alloc) <- correctnessFixtures ]
  ]

-- | (definition in `opt-rules.once`, rule, a redex in its elaborated IR, its
-- whole optimized IR).
ruleFixtures :: [(String, String, String, String)]
ruleFixtures =
  [ ( "unitOf", "a quiet morphism into Unit is terminal"
    , "fst . (snd . <id . fst, snd>)"
    , "curry(terminal) . terminal" )
  , ( "vinl", "a morphism out of Void is initial"
    , "inl . (snd . <id . fst, snd>)"
    , "curry(initial . snd) . terminal" )
  , ( "left", "id . f = f, snd . <g, h> = h"
    , "[snd . (id . <id . fst, snd>), "
    , "curry([snd, 0 . terminal] . (apply . (<[curry(inl . <terminal, fst>), curry(inr . <terminal, fst>)] . fst, terminal> . (<snd, terminal> . <terminal, inl . snd>)))) . terminal" )
  , ( "outer", "fst . <g, h> = g"
    , "[snd . (fst . <<id . fst, snd> . fst, snd>), "
    , "curry([snd . fst, snd] . (apply . (<[curry(inl . <snd, fst>), curry(inr . <snd, fst>)] . fst, snd> . (<snd, fst> . <id, inl . (0 . terminal)>)))) . terminal" )
  ]

-- | The rule's redex is in the elaborated IR of `fn`, and the optimized IR is
-- the expected one.
ruleTest :: String -> String -> String -> String -> TestTree
ruleTest fn rule before after =
  testCase (fn ++ ": " ++ rule) $ do
    elab <- dumpIR "elaborate"
    opt  <- dumpIR "optimize"
    case (lookup fn elab, lookup fn opt) of
      (Just e, Just o) -> do
        assertBool ("elaborated " ++ fn ++ " lacks the redex " ++ show before ++ ":\n" ++ e)
                   (before `isInfixOf` e)
        assertEqual ("optimized " ++ fn) after o
      _ -> assertFailure (fn ++ " is not among the compiled functions")

-- | `once <stage> test/opt-rules.once`, as (name, IR) pairs.
dumpIR :: String -> IO [(String, String)]
dumpIR stage = do
  (code, out, err) <- runOnce [stage, "test/opt-rules.once"]
  case code of
    ExitFailure _ -> assertFailure ("once " ++ stage ++ " failed: " ++ out ++ err) >> pure []
    ExitSuccess   -> pure (defs (lines out))
  where
    defs (sig : body : rest)
      | Just ir <- stripPrefix "  = " body = (takeWhile (/= ' ') sig, ir) : defs rest
    defs _ = []

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
