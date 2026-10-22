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
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce, testStrataDir)
import TypeErrorSpec (typeCheckStderr)

specMatrixTests :: TestTree
specMatrixTests = testGroup "Spec-change matrix (plan 0.113 D)"
  [ testGroup "main (D253, D315)"
      [ testCase "a signature-less main whose type is not below Eff Unit Unit is rejected" $ do
          r <- checkExe [ "main = 5" ]
          assertBool "Should reject a main of type Int" (isLeft r)
      ]

  , testGroup "a signature is the body's principal type (D314, D321)"
      [ testCase "a summand the body leaves open must be Void" $ do
          r <- checkLib [ "f : Int -> Int + Int", "f = inl" ]
          assertBool "Should reject a sum wider than the body's" (isLeft r)
      , testCase "the least sum is accepted" $ do
          r <- checkLib [ "f : Int -> Int + Void", "f = inl" ]
          r @?= Right ()
      , testCase "a grade above the body's is rejected" $ do
          r <- checkLib [ "f : Act Int Int", "f x = x + 1" ]
          assertBool "Should reject Act for a pure body" (isLeft r)
      , testCase "a schema wider than the body's is rejected" $ do
          r <- checkLib [ "f : a -> a + b", "f = inl" ]
          assertBool "Should reject a free summand in a schema" (isLeft r)
        -- D321: the principal type is least over the domains the signature
        -- gives. `Void` is the given domain; the codomain is the body's.
      , testCase "a constant out of a given Void domain is accepted (D321)" $ do
          r <- checkLib [ "f : Void -> Int", "f = \\x -> 3" ]
          r @?= Right ()
      , testCase "returning the Void argument at Int is wider than the body's (D321)" $ do
          r <- checkLib [ "f : Void -> Int", "f = \\x -> x" ]
          assertBool "Should reject Int where the body's codomain is Void" (isLeft r)
      , testCase "main at its principal type is accepted (D315)" $ do
          r <- checkExe [ "import I.Linux.Syscalls as S", "", "main : Act Unit Void", "main = compose exit@S (\\_ -> 0)" ]
          r @?= Right ()
      , testCase "main at Eff Unit Unit over an Act body is rejected (D315)" $ do
          r <- checkExe [ "import I.Linux.Syscalls as S", "", "main : Eff Unit Unit", "main = compose exit@S (\\_ -> 0)" ]
          assertBool "Should reject a main wider than its body" (isLeft r)
      ]

  , testGroup "the loop is ana into Eff (D317)"
      [ testCase "control: a round that runs a loop is accepted on its own" $ do
          r <- checkLib (loopBase ++ [ "round : Eff (Int * Int) (Int + (Int * Int))", roundBody ])
          r @?= Right ()
      , testCase "a round never contains a loop" $ do
          -- item 3: `ana`'s round is at most `Act`; one that runs `loopSum`
          -- is at `Eff`, so the loop over it is rejected.
          r <- checkLib (loopBase ++ [ "round : Eff (Int * Int) (Int + (Int * Int))", roundBody, ""
                                     , "outer : Eff (Int * Int) Int", "outer = ana round" ])
          assertBool "Should reject a loop whose round is at Eff" (isLeft r)
      , testCase "a silent round warns" $ do
          -- item 4: allowed, but almost always a bug.
          src <- TIO.readFile "test/loop-sum.once"
          err <- typeCheckStderr src
          assertBool ("Should warn about a silent round, got: " ++ err)
                     ("performs no event" `isInfixOf` err)
      , testCase "a round that emits does not warn" $ do
          src <- TIO.readFile "test/loop-emit.once"
          err <- typeCheckStderr src
          assertBool ("Should not warn, got: " ++ err) (not ("performs no event" `isInfixOf` err))
      ]

  , testGroup "a case is at the join of its branches (D322)"
      [ testCase "branches leaving different summands open meet at their join" $ do
          r <- checkLib
            [ "stop : Int -> Int + Void", "stop x = inl x", ""
            , "next : Int -> Void + Int", "next x = inr x", ""
            , "pick : Int -> Int + Int"
            , "pick x = destruct (x < 0) of { Left u -> stop x ; Right u -> next x }" ]
          r @?= Right ()
      , testCase "a branch at Void joins the other branch's type" $ do
          r <- checkLib
            [ "fromVoid : Void -> Void", "fromVoid = initial", ""
            , "pickInt : Int + Void -> Int"
            , "pickInt s = destruct s of { Left x -> x ; Right v -> fromVoid v }" ]
          r @?= Right ()
      , testCase "branches with no upper bound are rejected" $ do
          r <- checkLib [ "f : Int + Int -> Int", "f s = destruct s of { Left x -> x ; Right y -> () }" ]
          assertBool "Should reject branches at Int and Unit" (isLeft r)
      , testCase "arrows out of different domains have no join" $ do
          r <- checkLib
            [ "g : Int -> Int", "g x = x", ""
            , "h : Unit -> Int", "h u = 1", ""
            , "f : Int + Int -> Void -> Int"
            , "f s = destruct s of { Left x -> g ; Right y -> h }" ]
          assertBool "Should reject arrow branches with different domains" (isLeft r)
      , testCase "a body states a wider type by an annotation" $ do
          r <- checkLib [ "two : Int + Unit", "two = (inl 2 : Int + Unit)" ]
          r @?= Right ()
      , testCase "a wider signature is rejected, naming both fixes" $ do
          r <- checkLib [ "two : Int + Unit", "two = inl 2" ]
          case r of
            Left msg -> assertBool ("Should name the annotation fix: " ++ msg)
                          ("more precise than its signature" `isInfixOf` msg && "annotation" `isInfixOf` msg)
            Right () -> assertFailure "Should reject a signature wider than the body"
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
            , "e1 : Act Int Unit"
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
            , "e1 : Act Int Unit"
            , "e1 = compose emit@E (\\_ -> 1)"
            , ""
            , "both : Act Int (Unit * Unit)"
            , "both = pair e1 e1"
            ]
          r @?= Right ()
      -- D314/D321: a signature is the body's principal type, so the
      -- subsumption is at a USE: `inc`'s pure arrow where `compose` at `act`
      -- expects an `act` one.
      , testCase "a pure function where an effectful one is expected is accepted (pure <: act)" $ do
          r <- checkLib
            [ "import I.Test.Emit as E"
            , ""
            , "inc : Int -> Int"
            , "inc x = x + 1"
            , ""
            , "h : Act Int Unit"
            , "h = compose emit@E inc"
            ]
          r @?= Right ()
      , testCase "an effectful function where a pure one is expected is rejected" $ do
          r <- checkLib
            [ "import I.Test.Emit as E"
            , ""
            , "effInc : Act Int Int"
            , "effInc = compose (\\_ -> 1) emit@E"
            , ""
            , "p : Int -> Int"
            , "p = effInc"
            ]
          assertBool "Should reject eff where pure is expected" (isLeft r)
        -- D318 item 2: a stream's layers are at a finite grade, `pure ⊑ act`,
        -- so a pure stream is accepted where an acting one is expected (each
        -- layer becomes a block with no call). PuritySpec rejects the converse.
      , testCase "a pure stream where an acting one is expected is accepted" $ do
          r <- checkLib
            [ "mkNu : Int -> Nu (K Int)"
            , "mkNu = ana (\\x -> x)"
            , ""
            , "peekA : Nu (Act (K Int)) -> Act Unit Int"
            , "peekA v = Out v"
            , ""
            , "run : Act Unit Int"
            , "run = peekA (mkNu 3)"
            ]
          r @?= Right ()
      ]

  , testGroup "QTT (D276)"
      [ testCase "an unused affine (^1) parameter is accepted (One means at most once)" $ do
          r <- checkLib [ "f : Int^1 -> Int", "f x = 0" ]
          r @?= Right ()
      ]

  , testGroup "signatures extend Σ (D274, D249)"
      [ testCase "an own signature can be referenced" $ do
          r <- checkLib
            [ "signature tick : Act Unit Unit"
            , ""
            , "g : Act Unit Unit"
            , "g = tick"
            ]
          r @?= Right ()
        -- D318 item 5: a signature declares constants, pure functions and
        -- operations; this is the constant.
      , testCase "a declared constant can be referenced" $ do
          r <- checkLib
            [ "signature seven : Int"
            , ""
            , "f : Unit -> Int"
            , "f u = seven"
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
-- `loop-sum.once`'s loop and a summand injection, for the D317 group.
loopBase :: [T.Text]
loopBase =
  [ "stop : Int * Int -> Unit -> Int + Void", "stop p _ = inl (snd p)", ""
  , "next : Int * Int -> Unit -> Void + (Int * Int)", "next p _ = inr (fst p - 1, snd p + fst p)", ""
  , "step : Int * Int -> Int + (Int * Int)", "step p = case (next p) (stop p) (fst p == 0)", ""
  , "loopSum : Eff (Int * Int) Int", "loopSum = ana step", ""
  , "stopI : Int -> Int + Void", "stopI x = inl x", "" ]

-- A round that runs the whole loop `loopSum`, widened to a round's type.
roundBody :: T.Text
roundBody = "round = (compose stopI loopSum : Eff (Int * Int) (Int + (Int * Int)))"

checkLib :: [T.Text] -> IO (Either String ())
checkLib = build ["--lib"]

-- An executable build: `main` is used at `Eff Unit Unit` (D315).
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
