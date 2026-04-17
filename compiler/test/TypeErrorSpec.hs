-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Tests for type errors that should be rejected.
-- These test cases verify that ill-typed programs are correctly rejected.
module TypeErrorSpec (typeErrorTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)

typeErrorTests :: TestTree
typeErrorTests = testGroup "Type Errors"
  [ typeMismatchTests
  , mainTypeTests
  ]

------------------------------------------------------------------------
-- Type Mismatch Tests
------------------------------------------------------------------------

typeMismatchTests :: TestTree
typeMismatchTests = testGroup "Type mismatches"
  [ testCase "Int literal where function expected" $ do
      -- A function type Int -> Int cannot have literal body
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = 42"
            ]
      result <- typeCheckSource source
      assertBool "Should reject Int literal for function type" (isLeft result)

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
  [ testCase "main with Eff Unit A is valid" $ do
      -- This is the canonical main type
      let source = T.unlines
            [ "main : Eff Unit Int"
            , "main = arr 42"
            ]
      result <- typeCheckSource source
      -- Note: arr lifts pure values to Eff
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
-- Test Helpers
------------------------------------------------------------------------

-- | Type check a source string using the CLI 'check' command.
-- Returns Right () on success, Left error message on failure.
typeCheckSource :: T.Text -> IO (Either String ())
typeCheckSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle  -- Must close before external process reads
  (exitCode, _stdout, stderr) <- readProcessWithExitCode
    "cabal" ["run", "once", "--", "check", path] ""
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left stderr)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
