-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Tests for type errors that should be rejected.
-- These test cases verify that ill-typed programs are correctly rejected.
-- `accepts`/`rejects`/`typeCheckSource` are exported so FloatSpec can reuse
-- them rather than duplicate the temp-file + `once check` plumbing.
module TypeErrorSpec (typeErrorTests, accepts, rejects, typeCheckSource, typeCheckStderr) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)

typeErrorTests :: TestTree
typeErrorTests = testGroup "Type Errors"
  [ typeMismatchTests
  , mainTypeTests
  , builtinShapeErrorTests
  , destructErrorTests
  , modeErrorTests
  , scopeErrorTests
  ]

------------------------------------------------------------------------
-- Type Mismatch Tests
------------------------------------------------------------------------

typeMismatchTests :: TestTree
typeMismatchTests = testGroup "Type mismatches"
  [ testCase "value body at function type is REJECTED (D127)" $ do
      -- `f : Int -> Int; f = 42` is now a TYPE ERROR. D126 accepted it by
      -- lifting a value body `b : B` at `A -> B` to the constant function
      -- `const b = b ∘ terminal`; D127 removed that implicit lift, because the
      -- lift is what forced a combinator arm to be CLOSED, and a closed arm
      -- cannot mention an enclosing binder. The constant function is still
      -- expressible — it is now WRITTEN, as `f = \\_ -> 42`.
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = 42"
            ]
      result <- typeCheckSource source
      assertBool "Should reject a bare value body at an arrow type" (isLeft result)

  , testCase "the written constant function is accepted" $ do
      -- …and this is what replaces it. Same denotation, spelled.
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = \\_ -> 42"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "value body must match the function's result type" $ do
      -- Rejected before D127 by the lift's codomain check, and after it by the
      -- absence of any lift at all — either way, not an escape hatch.
      let source = T.unlines
            [ "f : Int -> String"
            , "f = 42"
            ]
      result <- typeCheckSource source
      assertBool "Should reject Int body at result type String" (isLeft result)

  , testCase "String literal for Int type" $ do
      let source = T.unlines
            [ "x : Int"
            , "x = \"hello\""
            ]
      result <- typeCheckSource source
      assertBool "Should reject String for Int type" (isLeft result)

  , testCase "Int for String type" $ do
      let source = T.unlines
            [ "x : String"
            , "x = 42"
            ]
      result <- typeCheckSource source
      assertBool "Should reject Int for String type" (isLeft result)

  , testCase "function for Int type" $ do
      let source = T.unlines
            [ "x : Int"
            , "x = id"
            ]
      result <- typeCheckSource source
      assertBool "Should reject function for Int type" (isLeft result)

  , testCase "wrong argument type to function" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f x = x"
            , ""
            , "main : Int"
            , "main = f \"hello\""
            ]
      result <- typeCheckSource source
      assertBool "Should reject wrong argument type" (isLeft result)
  ]

------------------------------------------------------------------------
-- Main Function Type Tests
------------------------------------------------------------------------

mainTypeTests :: TestTree
mainTypeTests = testGroup "Main function validation"
  [ testCase "main at a type below Eff Unit Unit is valid" $ do
      -- D315: `main` is at its principal type and used at `Eff Unit Unit`;
      -- `id`'s principal type here is the pure `Unit -> Unit`. `Eff Unit Int`
      -- is NOT valid — the trailing object must be Unit.
      let source = T.unlines
            [ "main : Unit -> Unit"
            , "main = id"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "main without Eff is invalid" $ do
      -- main must have type Eff Unit A, not just A
      let source = T.unlines
            [ "main : Int"
            , "main = 42"
            ]
      result <- typeCheckSource source
      assertBool "Should reject main without Eff type" (isLeft result)

  , testCase "main with wrong input type" $ do
      -- main must be Eff Unit A, not Eff Int A
      let source = T.unlines
            [ "main : Eff Int Int"
            , "main = id"
            ]
      result <- typeCheckSource source
      assertBool "Should reject main with non-Unit input" (isLeft result)

  , testCase "main's body is checked at main's own type" $ do
      -- plan 0.121 R7 (D315): a pure-declared `main` with an effectful body
      -- is ill-typed, though its body would check at `Eff Unit Unit`.
      let source = T.unlines
            [ "signature tick : Act Unit Unit"
            , "main : Unit -> Unit"
            , "main = tick"
            ]
      result <- typeCheckSource source
      assertBool "Should reject an effectful body under a pure main" (isLeft result)
  ]

------------------------------------------------------------------------
-- Builtin shape errors (fst/snd/negation on the wrong type, arity)
------------------------------------------------------------------------

builtinShapeErrorTests :: TestTree
builtinShapeErrorTests = testGroup "Builtin shape errors"
  [ rejects "fst applied to a non-pair"
      [ "f : Int -> Int"
      , "f x = fst x"
      ]
  , rejects "snd applied to a non-pair"
      [ "f : Int -> Int"
      , "f x = snd x"
      ]
  , rejects "unary negation of a non-Int"
      [ "f : String -> Int"
      , "f x = -x"
      ]
  , rejects "over-application (id given two arguments)"
      [ "f : Int -> Int"
      , "f x = id x x"
      ]
  ]

------------------------------------------------------------------------
-- destruct (sum elimination) errors
------------------------------------------------------------------------

destructErrorTests :: TestTree
destructErrorTests = testGroup "destruct errors"
  [ rejects "destruct on a non-sum scrutinee"
      [ "f : Int -> Int"
      , "f x = destruct x of { Left a -> a ; Right b -> b }"
      ]
  , rejects "destruct branches with different types"
      [ "f : (Int + Int) -> Int"
      , "f x = destruct x of { Left a -> a ; Right b -> \"s\" }"
      ]
  ]

------------------------------------------------------------------------
-- Mode errors: check-only constructs used in inference position
------------------------------------------------------------------------

-- D323: without a signature, a definition has the type its body SYNTHESIZES.
-- These bodies only check (a lambda takes a context; `inl`, `inr` and
-- `initial` leave their target open), so each needs a signature.
modeErrorTests :: TestTree
modeErrorTests = testGroup "Check-only bodies need a signature (D323)"
  [ rejects "bare lambda without a type signature"
      [ "f = \\x -> x"
      ]
  , rejects "inl with no target sum type"
      [ "g = inl"
      ]
  , rejects "inr with no target sum type"
      [ "g = inr"
      ]
  , rejects "initial with no target type"
      [ "g = initial"
      ]
  ]

------------------------------------------------------------------------
-- Scope errors: unbound (qualified) names
------------------------------------------------------------------------

scopeErrorTests :: TestTree
scopeErrorTests = testGroup "Scope errors"
  [ rejects "unbound local variable"
      [ "f : Int -> Int"
      , "f x = y"
      ]
  , rejects "unbound qualified (imported) name"
      [ "import I.Linux.Syscalls as S"
      , ""
      , "f : Int -> Int"
      , "f = nope@S"
      ]
    -- plan 0.121 R11 (D324): no definition names `main`, bare or as `main@this`.
    -- The control is accepted, so only the reference to `main` is rejected.
  , accepts "control: main without a reference to it"
      [ "main : Unit -> Unit"
      , "main = id"
      ]
  , rejectsWith "a definition referring to main@this" "refers to `main`"
      [ "main : Unit -> Unit"
      , "main = id"
      , "g : Unit -> Unit"
      , "g = main@this"
      ]
  , rejectsWith "a definition referring to a bare main" "refers to `main`"
      [ "main : Unit -> Unit"
      , "main = id"
      , "g : Unit -> Unit"
      , "g = main"
      ]
  , accepts "a local variable named main is unaffected"
      [ "f : Int -> Int"
      , "f main = main"
      ]
    -- D319 (`OneName`): each name in a program's signature is declared once.
    -- Two equal declarations used to satisfy `sig-unique`; they do not
    -- satisfy `OneName`. The control shows one declaration is accepted.
  , accepts "control: an operation declared once"
      [ "signature tick : Act Unit Unit"
      , "f : Act Unit Unit"
      , "f = tick"
      ]
  , rejectsWith "an operation declared twice at one type" "`tick` is declared more than once"
      [ "signature tick : Act Unit Unit"
      , "signature tick : Act Unit Unit"
      , "f : Act Unit Unit"
      , "f = tick"
      ]
  , rejectsWith "an operation declared twice at two types" "`tick` is declared more than once"
      [ "signature tick : Act Unit Unit"
      , "signature tick : Act Int Unit"
      , "f : Act Unit Unit"
      , "f = tick"
      ]
    -- plan 0.121 R10: a type signature is immediately followed by its
    -- definition, as written; an import between them separates them even
    -- when the imported module has no signatures (Derived.Nat has none).
  , rejects "an import between a type signature and its definition"
      [ "f : Int -> Int"
      , "import Derived.Nat"
      , "f x = x"
      ]
  ]

------------------------------------------------------------------------
-- Test Helpers
------------------------------------------------------------------------

-- | Type check a source string using the CLI 'check' command.
-- Returns Right () on success, Left error message on failure.
typeCheckSource :: T.Text -> IO (Either String ())
typeCheckSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle  -- Must close before external process reads
  -- `once check` prints type errors on stdout; include both streams in Left.
  (exitCode, stdout, stderr) <- runOnce ["check", path]
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left (stdout ++ stderr))

-- | The STDERR of `once check` — the warning channel (D123/D116).
--
-- Separate from `typeCheckSource`, which folds both streams into its failure
-- case: a warning is not a failure, so reading the channel needs its own door.
-- This is what lets `FloatSpec` tell `0.5` from `0.1`, which it could not do
-- while `Once.Warnings` was unreachable from the driver.
typeCheckStderr :: T.Text -> IO String
typeCheckStderr source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle
  (_, _, err) <- runOnce ["check", path]
  return err

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

-- | Assert that a program (given as source lines) is REJECTED by `once check`.
rejects :: TestName -> [T.Text] -> TestTree
rejects name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertBool ("Should reject: " ++ name) (isLeft result)

-- | Assert that a program is REJECTED with an error that contains `needle`,
-- so the test fails if the program is rejected for another reason.
rejectsWith :: TestName -> String -> [T.Text] -> TestTree
rejectsWith name needle sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  case result of
    Left err -> assertBool ("Error should mention " ++ show needle ++ ":\n" ++ err)
                           (T.pack needle `T.isInfixOf` T.pack err)
    Right () -> assertFailure ("Should reject: " ++ name)

-- | Assert that a program is ACCEPTED by `once check` (D072 flips).
accepts :: TestName -> [T.Text] -> TestTree
accepts name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertBool ("Should accept: " ++ name) (not (isLeft result))
