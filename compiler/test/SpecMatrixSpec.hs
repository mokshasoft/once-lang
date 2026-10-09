{-# LANGUAGE OverloadedStrings #-}
-- | Plan 0.113 phase D: the Spec-change → test matrix of the 2026-10-09 merge
-- analysis. Every semantic change the branch made to the Spec gets a test that
-- shows the RIGHT programs accepted AND the wrong ones rejected — the proofs show
-- the compiler meets the Spec; these show the Spec says what we mean.
-- (Rejections assert only `isLeft` for now; plan 0.115 makes them name the
-- error.)
module SpecMatrixSpec (specMatrixTests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce, testStrataDir)

specMatrixTests :: TestTree
specMatrixTests = testGroup "Spec-change matrix (plan 0.113 D)"
  [ testGroup "main (D227 amendment, D253)"
      [ testCase "a signature-less main that is not IO Unit is rejected" $ do
          r <- checkExe [ "main = 5" ]
          assertBool "Should reject a main of type Int" (isLeft r)
      ]

  , testGroup "polymorphism (D236–D243)"
      [ testCase "an unused definition typed once at rigid parameters is checked" $ do
          -- `x : a` returned at `b`: wrong for every instance, so wrong once.
          r <- checkLib [ "bad : a -> b", "bad x = x" ]
          assertBool "Should reject a body that is wrong at its rigid schema" (isLeft r)
      , testCase "a polymorphic head at an instance of its schema is accepted (d-poly)" $ do
          r <- checkLib
            [ "swap : a * b -> b * a"
            , "swap p = (snd p, fst p)"
            , ""
            , "x : Int * Int"
            , "x = swap (1, 2)"
            ]
          r @?= Right ()
      , testCase "a polymorphic head applied to a non-instance is rejected (d-poly)" $ do
          -- No instance of `a * b` is `Int`. (The diagnostic today is the generic
          -- "unspecialized variable" — plan 0.115 makes it name the mismatch.)
          r <- checkLib
            [ "swap : a * b -> b * a"
            , "swap p = (snd p, fst p)"
            , ""
            , "x : Int * Int"
            , "x = swap 5"
            ]
          assertBool "Should reject swap at a non-product" (isLeft r)
      , testCase "an annotation may not mention a type parameter (D252)" $ do
          -- Rejected already by the GRAMMAR: an expression annotation's type is
          -- ground (no type variables), the strictest form of D252's rule.
          r <- checkLib [ "f : a -> a", "f x = (x : a)" ]
          assertBool "Should reject an annotation naming a rigid parameter" (isLeft r)
      ]

  , testGroup "recursion schemes (D228, D191–D199)"
      [ testCase "cata of a non-function is rejected" $ do
          r <- checkLib [ "f : Mu (K Unit + Id) -> Int", "f = cata 5" ]
          assertBool "Should reject cata 5" (isLeft r)
      , testCase "Out of a non-ν is rejected" $ do
          r <- checkLib [ "x : Int", "x = Out 5" ]
          assertBool "Should reject Out 5" (isLeft r)
      ]

  , testGroup "comparisons mean Bool = Unit + Unit (D263/D264)"
      [ testCase "a comparison is not an Int" $ do
          r <- checkLib [ "x : Int", "x = 2 < 5" ]
          assertBool "Should reject a comparison at Int" (isLeft r)
      ]

  , testGroup "effects (D219, D222, D226)"
      [ testCase "an effectful arm under pair at a pure type is rejected" $ do
          r <- checkLib
            [ "import I.Test.Emit as E"
            , ""
            , "e1 : Eff Int Unit"
            , "e1 = compose emit@E (\\_ -> 1)"
            , ""
            , "both : Int -> (Unit * Unit)"
            , "both = pair e1 e1"
            ]
          assertBool "Should reject an emitting arm in a pure pair" (isLeft r)
      , testCase "effectful arms under pair at an effectful type are accepted (D222)" $ do
          r <- checkLib
            [ "import I.Test.Emit as E"
            , ""
            , "e1 : Eff Int Unit"
            , "e1 = compose emit@E (\\_ -> 1)"
            , ""
            , "both : Eff Int (Unit * Unit)"
            , "both = pair e1 e1"
            ]
          r @?= Right ()
      , testCase "a pure function where an effectful one is expected is accepted (pure <: eff)" $ do
          r <- checkLib
            [ "inc : Int -> Int"
            , "inc x = x + 1"
            , ""
            , "h : Eff Int Int"
            , "h = inc"
            ]
          r @?= Right ()
      , testCase "an effectful function where a pure one is expected is rejected" $ do
          r <- checkLib
            [ "import I.Test.Emit as E"
            , ""
            , "effInc : Eff Int Int"
            , "effInc = compose (\\_ -> 1) emit@E"
            , ""
            , "p : Int -> Int"
            , "p = effInc"
            ]
          assertBool "Should reject eff where pure is expected" (isLeft r)
      ]

  , testGroup "QTT (D276)"
      [ testCase "an unused affine (^1) parameter is accepted (One means at most once)" $ do
          r <- checkLib [ "f : Int^1 -> Int", "f x = 0" ]
          r @?= Right ()
      ]

  , testGroup "signatures extend Σ (D274, D249)"
      [ testCase "an own signature can be referenced" $ do
          r <- checkLib
            [ "signature tick : Eff Unit Unit"
            , ""
            , "g : Eff Unit Unit"
            , "g = tick"
            ]
          r @?= Right ()
      , testCase "a signature and a definition of one name are rejected" $ do
          r <- checkLib
            [ "signature f : Int -> Int"
            , ""
            , "f : Int -> Int"
            , "f x = x"
            ]
          assertBool "Should reject a name both declared and defined" (isLeft r)
      ]
  ]

-- A library build: parse, resolve, type check, compile; no `main`.
checkLib :: [T.Text] -> IO (Either String ())
checkLib = build ["--lib"]

-- An executable build: `main` must be `IO Unit`.
checkExe :: [T.Text] -> IO (Either String ())
checkExe = build []

build :: [String] -> [T.Text] -> IO (Either String ())
build extra sourceLines = withSystemTempFile "matrix.once" $ \path handle -> do
  TIO.hPutStr handle (T.unlines sourceLines)
  hClose handle
  withSystemTempFile "matrix-out" $ \out outH -> do
    hClose outH
    (exitCode, stdout, stderr) <-
      runOnce (["build"] ++ extra ++ ["--target", "x86_64", "--strata", testStrataDir, "-o", out, path])
    case exitCode of
      ExitSuccess   -> pure (Right ())
      ExitFailure _ -> pure (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
