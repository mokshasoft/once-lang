-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Observable effect-trace tests (Plan 0.44 / 0.46).
--
-- The observable of a Once program is its ordered sequence of SigOp
-- invocations (Once.Denotation.Behavior); every other codegen test only sees
-- the final `exit` argument. These tests observe a MULTI-SigOp trace — effect
-- ordering AND arguments.
--
-- Each program imports the observable test interpretation `I.Test.Emit` (whose
-- `emit : Eff Int Unit` writes its argument's low byte to stdout) and takes
-- `exit` from the real `I.Linux.Syscalls`. Both resolve under the single test
-- strata root (Backend.Common.testStrataDir), and the compiler links their
-- implementations. So the captured stdout is exactly the emitted byte sequence
-- and the exit code is the final `exit` argument.
module TraceSpec (traceTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T

import Backend.Common (buildAndRunTrace)

traceTests :: TestTree
-- Plan 0.52 retired `arr`; the const morphisms are written as integer
-- literals directly (global elements — the same denotation as `arr cN`).
-- Effect ordering + exit code are unchanged; the compose chains are identical.
traceTests = testGroup "Effect traces (observable)"
  [ traceTest "exit only is an empty emit trace"
      []
      [ "main = compose exit@S 5" ]
      [] 5

  , traceTest "single emit then exit"
      []
      [ "main = compose exit@S (compose 0 (compose emit@E 42))" ]
      [42] 0

  , traceTest "two emits preserve order (emit 5 before emit 3)"
      []
      [ "main = compose exit@S"
      , "         (compose 7"
      , "           (compose emit@E"
      , "             (compose 3"
      , "               (compose emit@E 5))))"
      ]
      [5, 3] 7

  , traceTest "three emits preserve order and arguments"
      []
      [ "main = compose exit@S"
      , "         (compose 9"
      , "           (compose emit@E"
      , "             (compose 3"
      , "               (compose emit@E"
      , "                 (compose 2"
      , "                   (compose emit@E 1))))))"
      ]
      [1, 2, 3] 9
  ]

-- | Build a trace program (helper definitions + a `main`), run it, and assert
-- the emitted byte sequence and exit code. @emitted@ is the expected list of
-- bytes written by `emit`.
traceTest :: TestName -> [T.Text] -> [T.Text] -> [Int] -> Int -> TestTree
traceTest name helpers mainLines emitted exitCode =
  testCase name $ do
    let source = T.unlines $
          [ "import I.Linux.Syscalls as S"
          , "import I.Test.Emit as E"
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
