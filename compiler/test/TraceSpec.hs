-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Observable effect-trace tests (Plan 0.44 / 0.46).
--
-- The observable of a Once program is its ordered sequence of SigOp
-- invocations (Once.Denotation.Behavior); every other codegen test only sees
-- the final `exit` argument. These tests observe a MULTI-SigOp trace — effect
-- ordering AND arguments.
--
-- Each program declares the SigOps locally:
--     signature emit : Eff Int Unit
--     signature exit : Eff Int Unit
-- and is linked against the trace runtime (test/trace-runtime.s), whose `emit`
-- writes its argument's low byte to stdout. So the captured stdout is exactly
-- the emitted byte sequence and the exit code is the final `exit` argument.
-- Declaring the SigOps locally means the codegen calls them by their own name
-- (`once_4emit`/`once_4exit`) — no strata/module-path symbol mangling involved.
module TraceSpec (traceTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T

import Backend.Common (buildAndRunTrace)

traceTests :: TestTree
traceTests = testGroup "Effect traces (observable)"
  [ traceTest "exit only is an empty emit trace"
      [ "c5 : Unit -> Int", "c5 u = 5" ]
      [ "main = compose exit (arr c5)" ]
      [] 5

  , traceTest "single emit then exit"
      [ "c42 : Unit -> Int", "c42 u = 42"
      , "c0 : Unit -> Int",  "c0 u = 0"
      ]
      [ "main = compose exit (compose (arr c0) (compose emit (arr c42)))" ]
      [42] 0

  , traceTest "two emits preserve order (emit 5 before emit 3)"
      [ "c5 : Unit -> Int", "c5 u = 5"
      , "c3 : Unit -> Int", "c3 u = 3"
      , "c7 : Unit -> Int", "c7 u = 7"
      ]
      [ "main = compose exit"
      , "         (compose (arr c7)"
      , "           (compose emit"
      , "             (compose (arr c3)"
      , "               (compose emit (arr c5)))))"
      ]
      [5, 3] 7

  , traceTest "three emits preserve order and arguments"
      [ "c1 : Unit -> Int", "c1 u = 1"
      , "c2 : Unit -> Int", "c2 u = 2"
      , "c3 : Unit -> Int", "c3 u = 3"
      , "c9 : Unit -> Int", "c9 u = 9"
      ]
      [ "main = compose exit"
      , "         (compose (arr c9)"
      , "           (compose emit"
      , "             (compose (arr c3)"
      , "               (compose emit"
      , "                 (compose (arr c2)"
      , "                   (compose emit (arr c1)))))))"
      ]
      [1, 2, 3] 9
  ]

-- | Build a trace program (helper definitions + a `main`), link it against the
-- trace runtime, run it, and assert the emitted byte sequence and exit code.
-- @emitted@ is the expected list of bytes written by `emit`.
traceTest :: TestName -> [T.Text] -> [T.Text] -> [Int] -> Int -> TestTree
traceTest name helpers mainLines emitted exitCode =
  testCase name $ do
    let source = T.unlines $
          [ "signature emit : Eff Int Unit"
          , "signature exit : Eff Int Unit"
          , ""
          ] ++ helpers ++ [ "", "main : IO Unit" ] ++ mainLines
    result <- buildAndRunTrace (slug name) source
    case result of
      Left err -> assertFailure err
      Right (out, code) -> do
        assertEqual "emitted byte sequence (effect order + arguments)"
                    emitted (map fromEnum out)
        assertEqual "exit code (final exit SigOp argument)" exitCode code

-- | A filesystem-safe name for the per-test build directory.
slug :: TestName -> String
slug = map (\c -> if c `elem` (" /()" :: String) then '_' else c)
