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

  , testCase "pure function forcing an effectful stream is rejected" $ do
      -- D233: an effectful coalgebra builds `Nu (Eff F)` = ν(T ∘ F). `peek`
      -- takes a PURE stream, so passing it the effectful one is a type error:
      -- otherwise forcing the layer would emit inside a pure function.
      r <- checkLib
        [ "import I.Test.Emit as E"
        , ""
        , "mkNu : Int -> Nu (Eff (K Int))"
        , "mkNu = ana (compose (\\_ -> 7) emit@E)"
        , ""
        , "peek : Nu (K Int) -> Int"
        , "peek v = Out v"
        , ""
        , "run : Int"
        , "run = peek (mkNu 3)"
        ]
      assertBool "Should reject forcing an effectful stream inside a pure function" (isLeft r)

  , testCase "an effectful coalgebra cannot build a pure stream" $ do
      r <- checkLib
        [ "import I.Test.Emit as E"
        , ""
        , "mkNu : Int -> Nu (K Int)"
        , "mkNu = ana (compose (\\_ -> 7) emit@E)"
        , ""
        -- USED, because a definition whose signature mentions `Nu`/`Mu` is
        -- only checked at its use sites today (a separate, pre-existing gap).
        , "run : Int"
        , "run = Out (mkNu 3)"
        ]
      assertBool "Should reject an effectful coalgebra at a pure stream type" (isLeft r)

  , testCase "forcing an effectful stream is an effectful suspension" $ do
      -- The honest twin: `Out` on `Nu (Eff F)` is `Eff Unit (F …)`.
      r <- checkLib
        [ "import I.Test.Emit as E"
        , ""
        , "mkNu : Int -> Nu (Eff (K Int))"
        , "mkNu = ana (compose (\\_ -> 7) emit@E)"
        , ""
        , "run : Eff Unit Int"
        , "run = Out (mkNu 3)"
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
