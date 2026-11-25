-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Observable effect-trace tests (Plan 0.44 / 0.46).
--
-- The observable of a Once program is its ordered sequence of SigOp
-- invocations (Once.Denotation.Behavior), and its end. These tests observe a
-- MULTI-SigOp trace — effect ordering AND arguments.
--
-- Each program imports the observable test interpretation `I.Test.Emit` (whose
-- `emit : Eff Int Unit` writes its argument's WHOLE MACHINE WORD to stdout)
-- and the portable `I.Halt`; the compiler links their implementations. A
-- program's last value is emitted too, and `main` returns (plan 0.140 §3.5:
-- the end carries no value).
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

import Backend.Common (BackendArch (X86_64), End (..), assertEnd, buildAndRunTrace, decodeTrace, signedAt)

traceTests :: TestTree
-- Plan 0.52 retired `arr`. D127 then retired the implicit value-lift that had
-- replaced it, so a const morphism in a `compose` arm is WRITTEN as one:
-- `\\_ -> 7`, not the bare literal `7`.
traceTests = testGroup "Effect traces (observable)"
  [ traceTest "a halt alone is an empty trace, ended halted"
      []
      [ "main = halt@H" ]
      [] Halted

  , traceTest "two emits, the second after the first's result"
      []
      [ "main = compose emit@E (compose (\\_ -> 0) (compose emit@E (\\_ -> 42)))" ]
      [42, 0] Returned

  -- NEGATIVE ARGUMENTS. Once's integers are SIGNED, so these pin down that a
  -- negative argument reaches the SigOp as itself. They are not idle: the
  -- source-level DENOTATION of these very programs is currently wrong in two
  -- separate ways — `⟦ int n ⟧ˢ = absℤ n` (absolute value, so −5 would mean 5)
  -- and `sub-semM (a , b) = a ℕ.∸ b` (monus, so `0 - 5` would mean 0). The
  -- machine is right and the spec is not; these tests are what will keep the
  -- machine right while the denotation is corrected to match it.
  , traceTest "a negated literal emits its negative, not its magnitude"
      [ "emitNeg : Act Unit Unit"
      , "emitNeg = emit@E (-5)"
      ]
      [ "main = compose emit@E (compose (\\_ -> 7) emitNeg)" ]
      [-5, 7] Returned

  , traceTest "subtraction below zero emits a negative, not zero"
      [ "emitNeg : Act Unit Unit"
      , "emitNeg = emit@E (3 - 8)"
      ]
      [ "main = compose emit@E (compose (\\_ -> 7) emitNeg)" ]
      [-5, 7] Returned

  , traceTest "negative and positive arguments keep their order and signs"
      [ "emitA : Act Unit Unit"
      , "emitA = emit@E (0 - 1)"
      , ""
      , "emitB : Act Unit Unit"
      , "emitB = emit@E 2"
      ]
      [ "main = compose emit@E (compose (\\_ -> 7) (compose emitB emitA))" ]
      [-1, 2, 7] Returned

  , traceTest "two emits preserve order (emit 5 before emit 3)"
      []
      [ "main = compose emit@E"
      , "         (compose (\\_ -> 7)"
      , "           (compose emit@E"
      , "             (compose (\\_ -> 3)"
      , "               (compose emit@E (\\_ -> 5)))))"
      ]
      [5, 3, 7] Returned

  , traceTest "three emits preserve order and arguments"
      []
      [ "main = compose emit@E"
      , "         (compose (\\_ -> 9)"
      , "           (compose emit@E"
      , "             (compose (\\_ -> 3)"
      , "               (compose emit@E"
      , "                 (compose (\\_ -> 2)"
      , "                   (compose emit@E (\\_ -> 1)))))))"
      ]
      [1, 2, 3, 9] Returned

  -- THE TEST PLAN 0.76 / D127 EXISTS FOR. The `compose` arm `\_ -> x` mentions
  -- the ENCLOSING binder `x`. Under D126 a combinator arm was CLOSED BY
  -- CONSTRUCTION — that closedness is what made `realize-morph` total and what
  -- forced the categorical laws — so this program had no typing at all, in any
  -- spelling. Context-indexed composition is precisely the change that admits
  -- it.
  --
  -- The TRACE is what makes the test load-bearing rather than a compile check:
  -- the emitted word is the ARGUMENT `5`, so the arm genuinely read the binder
  -- rather than closing over a constant baked in at the arm.
  , traceTest "a compose arm captures an enclosing binder (D127)"
      [ "emitCaptured : Int -> Act Unit Unit"
      , "emitCaptured = \\x -> compose emit@E (\\_ -> x)"
      , ""
      , "emitFive : Act Unit Unit"
      , "emitFive = emitCaptured 5"
      ]
      [ "main = compose emit@E (compose (\\_ -> 7) emitFive)" ]
      [5, 7] Returned
  ]

-- | Build a trace program (helper definitions + a `main`), run it, and assert
-- the emitted ARGUMENT sequence and the end. @emitted@ is the expected list
-- of values passed to `emit`, in order — full values, not projections.
traceTest :: TestName -> [T.Text] -> [T.Text] -> [Integer] -> End -> TestTree
traceTest name helpers mainLines emitted end =
  testCase name $ do
    let source = T.unlines $
          [ "import I.Halt as H"
          , "import I.Test.Emit as E"
          , ""
          ] ++ helpers ++ [ "", mainSig ] ++ mainLines
        mainSig = if end == Halted then "main : Act Unit Void" else "main : Act Unit Unit"
    result <- buildAndRunTrace (slug name) source
    case result of
      Left err -> assertFailure err
      Right (out, code) -> case decodeTrace X86_64 out of
        Left err   -> assertFailure err
        Right ws   -> do
          -- Read each word as the SIGNED value it represents: Once has only
          -- signed integers, so this is what `emit`'s `Int` argument MEANS.
          assertEqual "emitted arguments (effect order + full signed values)"
                      emitted (map (signedAt X86_64) ws)
          assertEnd "" end code

-- | A filesystem-safe name for the per-test build directory.
slug :: TestName -> String
slug = map (\c -> if c `elem` (" /()" :: String) then '_' else c)
