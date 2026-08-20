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
-- `emit : Eff Int Unit` writes its argument's WHOLE MACHINE WORD to stdout)
-- and takes `exit` from the real `I.Linux.Syscalls`. Both resolve under the
-- single test strata root (Backend.Common.testStrataDir), and the compiler
-- links their implementations.
--
-- The captured stdout is therefore a sequence of little-endian machine words,
-- one per `emit`, which `decodeTrace` reads back as the ARGUMENTS themselves.
-- Expectations below are plain values for that reason — an `Int`'s value is
-- width-free, so `[42]` is the right assertion at every target width, and the
-- word size lives in `decodeTrace` rather than in every test.
--
-- `emit` used to write only the argument's LOW BYTE, which made `emit 42` and
-- `emit 298` the same trace: a bug corrupting an argument's high bits would
-- have passed all of these. Widening it is the same correction D114 made to
-- the spec's observable, one layer down in the harness.
module TraceSpec (traceTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T

import Backend.Common (BackendArch (X86_64), buildAndRunTrace, decodeTrace)

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
-- the emitted ARGUMENT sequence and exit code. @emitted@ is the expected list
-- of values passed to `emit`, in order — full values, not projections.
traceTest :: TestName -> [T.Text] -> [T.Text] -> [Integer] -> Int -> TestTree
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
      Right (out, code) -> case decodeTrace X86_64 out of
        Left err   -> assertFailure err
        Right args -> do
          assertEqual "emitted arguments (effect order + full values)"
                      emitted args
          assertEqual "exit code (final exit SigOp argument)" exitCode code

-- | A filesystem-safe name for the per-test build directory.
slug :: TestName -> String
slug = map (\c -> if c `elem` (" /()" :: String) then '_' else c)
