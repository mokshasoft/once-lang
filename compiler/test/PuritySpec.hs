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

  -- Plan 0.113 B2: halting/emitting are UP TO ISOMORPHISM. An empty codomain must
  -- be WRITTEN `Void`, a singleton one `Unit` (a skeleton): `Void * Int` would be
  -- an answering contract with no possible answer.
  , testCase "effectful FFI arrow into an empty codomain other than Void is rejected" $ do
      r <- checkLib [ "signature stop2 : Eff Int (Void * Int)" ]
      assertBool "Should reject an empty codomain not written Void" (isLeft r)

  , testCase "effectful FFI arrow into a singleton codomain other than Unit is rejected" $ do
      r <- checkLib [ "signature beep2 : Eff Int (Unit * Unit)" ]
      assertBool "Should reject a singleton codomain not written Unit" (isLeft r)

  , testCase "pure FFI arrow into an empty codomain is rejected" $ do
      r <- checkLib [ "signature f : Int -> (Void + Void)" ]
      assertBool "Should reject a pure arrow into an empty type" (isLeft r)

  , testCase "effectful FFI arrow into a sum with an empty summand is accepted" $ do
      -- `Int + Void` is neither empty nor a singleton: an answering contract.
      r <- checkLib [ "signature pick : Eff Int (Int + Void)" ]
      r @?= Right ()

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
        -- Typed at its declaration (plan 0.103 phase 1), used or not.
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
