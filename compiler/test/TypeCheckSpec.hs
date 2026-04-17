-- | Tests for the Agda-based type checker via CLI integration tests.
-- Tests inter-function calls, recursion, and type checking edge cases.
module TypeCheckSpec (typeCheckTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)

typeCheckTests :: TestTree
typeCheckTests = testGroup "Type Checker (Agda)"
  [ interFunctionCallTests
  , recursionTests
  , builtinShadowingTests
  ]

------------------------------------------------------------------------
-- Inter-function Call Tests
------------------------------------------------------------------------

interFunctionCallTests :: TestTree
interFunctionCallTests = testGroup "Inter-function calls"
  [ testCase "simple function call" $ do
      -- A function can call another function defined earlier
      let source = T.unlines
            [ "helper : Int -> Int"
            , "helper x = x"
            , ""
            , "main : Int"
            , "main = helper 5"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "chained function calls" $ do
      -- Functions can call multiple other functions
      let source = T.unlines
            [ "add1 : Int -> Int"
            , "add1 x = x + 1"
            , ""
            , "double : Int -> Int"
            , "double x = x + x"
            , ""
            , "compute : Int -> Int"
            , "compute x = double (add1 x)"
            , ""
            , "main : Int"
            , "main = compute 5"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "function calling function with lambda parameter" $ do
      -- Inter-function call where caller passes a lambda arg
      let source = T.unlines
            [ "apply : Int -> Int"
            , "apply x = x"
            , ""
            , "test : Int -> Int"
            , "test y = apply y"
            , ""
            , "main : Int"
            , "main = test 42"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "constants can be referenced" $ do
      -- Simple Int constants can be referenced by other functions
      let source = T.unlines
            [ "port : Int"
            , "port = 8080"
            , ""
            , "config : Int"
            , "config = port"
            , ""
            , "main : Int"
            , "main = config"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "many functions in sequence" $ do
      -- Test with 5+ functions to ensure accumulation works
      let source = T.unlines
            [ "f1 : Int"
            , "f1 = 1"
            , ""
            , "f2 : Int"
            , "f2 = f1"
            , ""
            , "f3 : Int"
            , "f3 = f2"
            , ""
            , "f4 : Int"
            , "f4 = f3"
            , ""
            , "f5 : Int"
            , "f5 = f4"
            , ""
            , "main : Int"
            , "main = f5"
            ]
      result <- typeCheckSource source
      result @?= Right ()
  ]

------------------------------------------------------------------------
-- Recursion Tests
------------------------------------------------------------------------

recursionTests :: TestTree
recursionTests = testGroup "Recursion"
  [ testCase "simple recursion (no args)" $ do
      let source = T.unlines
            [ "loop : Int"
            , "loop = loop"
            , ""
            , "main : Int"
            , "main = 0"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "recursion with parameter" $ do
      let source = T.unlines
            [ "countdown : Int -> Int"
            , "countdown n = countdown n"
            , ""
            , "main : Int"
            , "main = countdown 10"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "recursion with multiple parameters" $ do
      let source = T.unlines
            [ "gcd : Int -> Int -> Int"
            , "gcd a b = gcd b a"
            , ""
            , "main : Int"
            , "main = gcd 12 8"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "mutual-style (A calls B, B defined after A's type but calls itself)" $ do
      -- Note: True mutual recursion isn't supported, but this tests
      -- that a function can call itself even when other functions exist
      let source = T.unlines
            [ "even : Int -> Int"
            , "even n = even n"
            , ""
            , "odd : Int -> Int"
            , "odd n = odd n"
            , ""
            , "main : Int"
            , "main = even 4"
            ]
      result <- typeCheckSource source
      result @?= Right ()
  ]

------------------------------------------------------------------------
-- Builtin Shadowing Tests
------------------------------------------------------------------------

builtinShadowingTests :: TestTree
builtinShadowingTests = testGroup "Builtin names"
  [ testCase "user-defined 'id' is shadowed by builtin" $ do
      -- The builtin 'id : α → α' takes precedence over user-defined id
      -- This causes a type mismatch when calling with concrete type
      let source = T.unlines
            [ "id : Int -> Int"
            , "id x = x"
            , ""
            , "test : Int"
            , "test = id 5"
            ]
      result <- typeCheckSource source
      -- This should fail because builtin id : α → α doesn't unify with Int arg
      assertBool "Should fail due to builtin shadowing" (isLeft result)

  , testCase "non-builtin names work fine" $ do
      -- Using a non-builtin name avoids the shadowing issue
      let source = T.unlines
            [ "myId : Int -> Int"
            , "myId x = x"
            , ""
            , "test : Int"
            , "test = myId 5"
            ]
      result <- typeCheckSource source
      result @?= Right ()

  , testCase "user-defined 'fst' is shadowed by builtin" $ do
      let source = T.unlines
            [ "fst : Int -> Int"
            , "fst x = x"
            , ""
            , "test : Int"
            , "test = fst 5"
            ]
      result <- typeCheckSource source
      -- Builtin fst : (A * B) → A doesn't match Int argument
      assertBool "Should fail due to builtin shadowing" (isLeft result)

  , testCase "user-defined 'snd' is shadowed by builtin" $ do
      let source = T.unlines
            [ "snd : Int -> Int"
            , "snd x = x"
            , ""
            , "test : Int"
            , "test = snd 5"
            ]
      result <- typeCheckSource source
      assertBool "Should fail due to builtin shadowing" (isLeft result)
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
  -- Note: cabal run resolves to the built executable
  (exitCode, _stdout, stderr) <- readProcessWithExitCode
    "cabal" ["run", "once", "--", "check", path] ""
  case exitCode of
    ExitSuccess -> return (Right ())
    ExitFailure _ -> return (Left stderr)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
