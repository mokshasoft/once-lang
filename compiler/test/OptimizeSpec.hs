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
--   * representative Layer 0-5 + arith programs emit their value built both
--     ways, on every arch (the exit suites in `tests/` do the same for every
--     program).
module OptimizeSpec (optimizeTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.List (isInfixOf, stripPrefix)
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))

import Backend.Common (End (..), runOnce, traceCases)

optimizeTests :: TestTree
optimizeTests = testGroup "Optimizer"
  [ testGroup "rules fire on elaborated code (opt-rules.once)"
      [ ruleTest fn rule before after | (fn, rule, before, after) <- ruleFixtures ]
  , traceCases "opt-rules.once keeps its trace" "opt-rules" [5, 6, 7] Returned
  , testGroup "optimized and --no-optimize builds emit the same value"
      [ traceCases name name [v] Returned | (name, v) <- fixtures ]
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
  , ( "applied", "apply . <curry f . k, x> = f . <k, x>"
    , "apply . <curry(snd) . (id . fst), "
    , "curry(snd) . terminal" )
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

-- | Fixtures spread across the categorical layers and the arith lowering, so
-- the comparison covers projections, sums, closures, catamorphisms and arith
-- blocks, each with the value it emits.
fixtures :: [(String, Integer)]
fixtures =
  [ ("layer0-id", 42)
  , ("layer0-terminal", 42)
  , ("layer1-fst", 42)
  , ("layer1-snd-deep", 42)
  , ("layer2-case-inl-direct", 42)
  , ("layer3-pair-in-sum", 42)
  , ("layer3-sum-in-pair", 42)
  , ("layer4-keep-fst", 42)
  , ("layer4-twice", 42)
  , ("layer4-closure-in-pair", 42)
  , ("layer5-iseven", 42)
  , ("arith-simple", 13)
  , ("arith-lambda-1", 10)
  ]
