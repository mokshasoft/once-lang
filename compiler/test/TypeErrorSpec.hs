-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Tests for type errors that should be rejected.
-- These test cases verify that ill-typed programs are correctly rejected.
-- `accepts`/`rejects`/`typeCheckSource` are exported so FloatSpec can reuse
-- them rather than duplicate the temp-file + `once check` plumbing.
module TypeErrorSpec (typeErrorTests, accepts, rejects, typeCheckSource) where

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
  [ testCase "value body at function type lifts to a constant function" $ do
      -- `f : Int -> Int; f = 42` is ACCEPTED: a value body `b : B` at type
      -- `A -> B` lifts to the constant function `const b = b ∘ terminal`
      -- (here `42 : Unit -> Int` precomposed with `terminal : Int -> Unit`).
      -- This is the same value-lifting the language applies elsewhere, so it
      -- is allowed rather than special-cased. The body must still match the
      -- RESULT type: `f : Int -> String; f = 42` and `f : Int -> Int; f = unit`
      -- are both rejected (see below), as are multi-argument arrows.
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = 42"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "value body must match the function's result type" $ do
      -- The constant-function lifting is not a blanket escape hatch: the body
      -- type must equal the arrow's result type.
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
  [ testCase "main with IO Unit (Eff Unit Unit) is valid" $ do
      -- The canonical (and only valid) main type is `IO Unit` = `Eff Unit Unit`
      -- (fixed by validateMain; see Once.Denotation.Behavior). `Eff Unit Int`
      -- is NOT valid — the trailing object must be Unit.
      let source = T.unlines
            [ "main : IO Unit"
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

-- D072: these four were rejection tests ("check-only constructs used in
-- inference position"). The principal-type oracle now infers a SCHEMA
-- for each (bare lambda `t0 -> t0`, `inl : t0 -> t0 + t1`, `inr`,
-- `initial : Void -> t0`) and routes the def to the telescope, so they
-- are ACCEPTED — each use site instantiates the schema and is
-- kernel-checked.
modeErrorTests :: TestTree
modeErrorTests = testGroup "Inference-mode schemas (D072: accepted)"
  [ accepts "bare lambda without a type signature"
      [ "f = \\x -> x"
      ]
  , accepts "inl with no target sum type"
      [ "g = inl"
      ]
  , accepts "inr with no target sum type"
      [ "g = inr"
      ]
  , accepts "initial with no target type"
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
      , "main : IO Unit"
      , "main = nope@S"
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

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

-- | Assert that a program (given as source lines) is REJECTED by `once check`.
rejects :: TestName -> [T.Text] -> TestTree
rejects name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertBool ("Should reject: " ++ name) (isLeft result)

-- | Assert that a program is ACCEPTED by `once check` (D072 flips).
accepts :: TestName -> [T.Text] -> TestTree
accepts name sourceLines = testCase name $ do
  result <- typeCheckSource (T.unlines sourceLines)
  assertBool ("Should accept: " ++ name) (not (isLeft result))
