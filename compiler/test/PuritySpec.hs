-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Purity is a semantic claim: a `pure` arrow emits nothing (D231, plan
-- 0.102). A term typed pure must not be able to hide a SigOp event, or the
-- correctness statement — which is about exactly those events — could not
-- hold. Each rejection below is a hole the core calculus (Once.Spec.Core)
-- exposed; each has an accepted twin that does the same thing honestly, at an
-- effectful arrow.
module PuritySpec (purityTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce, testStrataDir)

purityTests :: TestTree
purityTests = testGroup "Purity (pure emits nothing)"
  [ testCase "pure FFI arrow into Unit is rejected (a Unit-returning SigOp emits)" $ do
      r <- checkLib [ "signature beep : Int -> Unit" ]
      assertBool "Should reject a pure signature that emits" (isLeft r)

  , testCase "effectful FFI arrow into Unit is accepted" $ do
      r <- checkLib [ "signature beep : Eff Int Unit" ]
      r @?= Right ()

  , testCase "pure FFI arrow into Void is rejected (a Void-returning SigOp halts)" $ do
      r <- checkLib [ "signature stop : Int -> Void" ]
      assertBool "Should reject a pure signature that halts" (isLeft r)

  , testCase "base-typed FFI constant of type Unit is rejected (its reference is a call)" $ do
      -- `tick` is a nullary SigOp: referencing it emits. Effects live on
      -- arrows (D032), so the honest declaration is `Eff Unit Unit`.
      r <- checkLib
        [ "signature tick : Unit"
        , ""
        , "f : Int -> Unit"
        , "f x = tick"
        ]
      assertBool "Should reject an emitting constant hidden in a pure function" (isLeft r)

  , testCase "pure function forcing an effectful ν is rejected" $ do
      -- Forcing a layer runs the coalgebra, which emits. `peek` is typed pure.
      -- (Also rejected today, but for an unrelated reason: see the twin below.)
      r <- checkLib
        [ "import I.Test.Emit as E"
        , ""
        , "mkNu : Eff Int (Nu (K Int))"
        , "mkNu = ana (compose (\\_ -> 7) emit@E)"
        , ""
        , "peek : Nu (K Int) -> Int"
        , "peek v = Out v"
        , ""
        , "run : Eff Int Int"
        , "run = compose peek mkNu"
        ]
      assertBool "Should reject forcing an effectful ν inside a pure function" (isLeft r)

  , testCase "effectful function forcing an effectful ν is accepted" $ do
      -- The honest twin: the forcing happens at an effectful arrow.
      r <- checkLib
        [ "import I.Test.Emit as E"
        , ""
        , "mkNu : Eff Int (Nu (K Int))"
        , "mkNu = ana (compose (\\_ -> 7) emit@E)"
        , ""
        , "run : Eff Int Int"
        , "run = compose (\\v -> Out v) mkNu"
        ]
      r @?= Right ()
  ]

------------------------------------------------------------------------
-- Helpers. `once check` does not resolve imports, so type-check through a
-- library build against the test strata.
------------------------------------------------------------------------

checkLib :: [T.Text] -> IO (Either String ())
checkLib sourceLines = withSystemTempFile "purity.once" $ \path handle -> do
  TIO.hPutStr handle (T.unlines sourceLines)
  hClose handle
  withSystemTempFile "purity-out" $ \out outH -> do
    hClose outH
    (exitCode, stdout, stderr) <-
      runOnce ["build", "--lib", "--target", "x86_64", "--strata", testStrataDir, "-o", out, path]
    case exitCode of
      ExitSuccess   -> return (Right ())
      ExitFailure _ -> return (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
