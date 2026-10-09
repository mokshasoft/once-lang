-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Quantitative Type Theory (QTT) / linearity tests via `once check`.
--
-- Once tracks resource usage with quantities on arrows: `A^0 -> B` (erased,
-- 0 uses), `A^1 -> B` (linear, exactly 1 use), and the default `A -> B`
-- (unrestricted, ω uses). The elaborator enforces, per binding, that the
-- actual usage `q'` is `≤` the declared quantity `q` (UsageViolation,
-- Once.TypeCheck.Elaborate). This is the language's headline property
-- ("linear code needs no GC") and was previously untested.
module QttSpec (qttTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)

qttTests :: TestTree
qttTests = testGroup "QTT / linearity"
  [ testCase "linear (^1) parameter used exactly once is accepted" $ do
      let source = T.unlines
            [ "f : Int^1 -> Int"
            , "f x = x"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "linear (^1) parameter used twice is rejected" $ do
      -- `(x, x)` uses the linear `x` with quantity ω > 1.
      let source = T.unlines
            [ "f : Int^1 -> (Int * Int)"
            , "f x = (x, x)"
            ]
      result <- typeCheckSource source
      assertBool "Should reject duplicating a linear parameter" (isLeft result)

  , testCase "erased (^0) parameter that is used is rejected" $ do
      -- Using an erased parameter at all is quantity 1 > 0.
      let source = T.unlines
            [ "f : Int^0 -> Int"
            , "f x = x"
            ]
      result <- typeCheckSource source
      assertBool "Should reject using an erased parameter" (isLeft result)

  , testCase "erased (^0) parameter that is unused is accepted" $ do
      let source = T.unlines
            [ "f : Int^0 -> Int"
            , "f x = 5"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "unrestricted parameter may be duplicated" $ do
      -- The default arrow is ω, so duplication is fine.
      let source = T.unlines
            [ "f : Int -> (Int * Int)"
            , "f x = (x, x)"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  -- D232 (amends D127): standard QTT. In `compose f g = λx. f (g x)` the
  -- inner arm's term is the ARGUMENT of `f`, so it is scaled by `f`'s grade.
  -- Here `dup` (ω) duplicates what `\y -> h` returns: two copies of `h`.
  , testCase "linear (^1) parameter in compose's inner arm is rejected" $ do
      let source = T.unlines
            [ "dup : Int -> (Int * Int)"
            , "dup x = (x, x)"
            , ""
            , "f : Int^1 -> (Int -> (Int * Int))"
            , "f h = compose dup (\\y -> h)"
            ]
      result <- typeCheckSource source
      assertBool "Should reject duplicating a linear parameter through compose" (isLeft result)

  , testCase "linear (^1) parameter in compose's outer arm is accepted" $ do
      -- The outer arm is used once per call, and `f`'s result is not
      -- duplicated by anything: standard QTT charges `h` once.
      let source = T.unlines
            [ "dup : Int -> (Int * Int)"
            , "dup x = (x, x)"
            , ""
            , "f : Int^1 -> (Int -> Int)"
            , "f h = compose (\\y -> h) dup"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "linear (^1) argument of an effectful application is rejected" $ do
      -- `dupE h` is the suspension `λ_. dupE h`: its argument is scaled by
      -- `dupE`'s grade ω, exactly as a pure application's is.
      let source = T.unlines
            [ "dupE : Eff Int (Int * Int)"
            , "dupE = pair id id"
            , ""
            , "g : Int^1 -> Eff Unit (Int * Int)"
            , "g h = dupE h"
            ]
      result <- typeCheckSource source
      assertBool "Should reject duplicating a linear argument through an effectful arrow" (isLeft result)

  -- Plan 0.113 B1 (QTT's eliminator rule): the fold applies its algebra once
  -- per node, so whatever the algebra captures is used ω times. A linear
  -- capture would be duplicated by any list with two leaves.
  , testCase "linear (^1) parameter captured by a cata algebra is rejected" $ do
      let source = T.unlines
            [ "addPair : Int * Int -> Int"
            , "addPair p = fst p + snd p"
            , ""
            , "f : Int^1 -> (Mu (K Unit + (K Int * Id)) -> Int)"
            , "f k = cata (case (\\_ -> k) addPair)"
            ]
      result <- typeCheckSource source
      assertBool "Should reject a linear capture in a cata algebra" (isLeft result)

  , testCase "unrestricted parameter captured by a cata algebra is accepted" $ do
      let source = T.unlines
            [ "addPair : Int * Int -> Int"
            , "addPair p = fst p + snd p"
            , ""
            , "f : Int -> (Mu (K Unit + (K Int * Id)) -> Int)"
            , "f k = cata (case (\\_ -> k) addPair)"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "examples/qtt-test-basic.once type-checks" $ do
      -- A small QTT sampler (id/const/dup/compose/let) that ships in examples/
      -- but had no driving test.
      result <- typeCheckFile "../examples/qtt-test-basic.once"
      result @?= Right ()
  ]

------------------------------------------------------------------------
-- Helpers (mirror TypeCheckSpec; `once check` prints errors on stdout)
------------------------------------------------------------------------

typeCheckSource :: T.Text -> IO (Either String ())
typeCheckSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle
  typeCheckFile path

typeCheckFile :: FilePath -> IO (Either String ())
typeCheckFile path = do
  (exitCode, stdout, stderr) <- runOnce ["check", path]
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
