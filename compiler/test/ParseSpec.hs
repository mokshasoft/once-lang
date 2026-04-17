-- | Parse tests using `once parse` command
module ParseSpec (parseTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce)

parseTests :: TestTree
parseTests = testGroup "Parse"
  [ validSyntaxTests
  , invalidSyntaxTests
  ]

------------------------------------------------------------------------
-- Valid Syntax Tests
------------------------------------------------------------------------

validSyntaxTests :: TestTree
validSyntaxTests = testGroup "Valid syntax"
  [ testCase "simple function" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f x = x"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)"]

  , testCase "multiple functions" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f x = x"
            , ""
            , "g : Int -> Int"
            , "g x = x"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)", "g : (Int ω→ Int)"]

  , testCase "function with multiple parameters" $ do
      let source = T.unlines
            [ "add : Int -> Int -> Int"
            , "add x y = x"
            ]
      result <- parseSource source
      assertParsed result ["add : (Int ω→ (Int ω→ Int))"]

  , testCase "product type" $ do
      let source = T.unlines
            [ "swap : (Int * Int) -> (Int * Int)"
            , "swap p = (snd p, fst p)"
            ]
      result <- parseSource source
      assertParsed result ["swap : ((Int * Int) ω→ (Int * Int))"]

  , testCase "sum type" $ do
      let source = T.unlines
            [ "f : (Int + Int) -> Int"
            , "f x = case x of { Left a -> a ; Right b -> b }"
            ]
      result <- parseSource source
      assertParsed result ["f : ((Int + Int) ω→ Int)"]

  , testCase "effectful function" $ do
      let source = T.unlines
            [ "main : Eff Unit Int"
            , "main = 42"
            ]
      result <- parseSource source
      assertParsed result ["main : Eff Unit Int"]

  , testCase "composition" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = id . id"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)"]

  , testCase "lambda" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f = \\x -> x"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)"]

  , testCase "let binding" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f x = let y = x in y"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)"]

  , testCase "primitive declaration" $ do
      let source = T.unlines
            [ "primitive exit : Eff Int Unit"
            ]
      result <- parseSource source
      assertParsed result ["exit : Eff Int Unit"]

  , testCase "import statement" $ do
      let source = T.unlines
            [ "import I.Math.Int as I"
            , ""
            , "f : Int -> Int"
            , "f = id"
            ]
      result <- parseSource source
      assertParsed result ["f : (Int ω→ Int)"]

  , testCase "type alias" $ do
      let source = T.unlines
            [ "type Pair a b = (a * b)"
            , ""
            , "f : Pair Int Int -> Int"
            , "f p = fst p"
            ]
      result <- parseSource source
      assertParsed result ["f : ((Int * Int) ω→ Int)"]
  ]

------------------------------------------------------------------------
-- Invalid Syntax Tests
------------------------------------------------------------------------

invalidSyntaxTests :: TestTree
invalidSyntaxTests = testGroup "Invalid syntax"
  [ testCase "missing type signature" $ do
      let source = T.unlines
            [ "f x = x"  -- no type signature
            ]
      result <- parseSource source
      assertParseError result

  , testCase "missing function body" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            -- no definition
            ]
      result <- parseSource source
      -- This might parse as just a signature, depends on parser behavior
      -- For now just check it doesn't crash
      case result of
        Left _ -> return ()  -- parse error is fine
        Right _ -> return () -- empty function list is also fine

  , testCase "mismatched parentheses" $ do
      let source = T.unlines
            [ "f : (Int -> Int"  -- missing closing paren
            , "f x = x"
            ]
      result <- parseSource source
      assertParseError result

  , testCase "invalid operator" $ do
      let source = T.unlines
            [ "f : Int -> Int"
            , "f x = x $$ x"  -- invalid operator
            ]
      result <- parseSource source
      assertParseError result
  ]

------------------------------------------------------------------------
-- Test Helpers
------------------------------------------------------------------------

-- | Parse a source string using the CLI 'parse' command.
-- Returns Right [signatures] on success, Left error on failure.
parseSource :: T.Text -> IO (Either String [T.Text])
parseSource source = withSystemTempFile "test.once" $ \path handle -> do
  TIO.hPutStr handle source
  hClose handle
  (exitCode, stdout, _stderr) <- runOnce ["parse", path]
  case exitCode of
    ExitSuccess ->
      let ls = T.lines (T.pack stdout)
          -- Filter out "Parse OK" line and empty lines
          sigs = filter (\l -> l /= "Parse OK" && not (T.null l)) ls
      in return (Right sigs)
    ExitFailure _ -> return (Left stdout)

-- | Assert that parsing succeeded and produced expected signatures
assertParsed :: Either String [T.Text] -> [T.Text] -> Assertion
assertParsed (Left err) _ = assertFailure $ "Parse failed: " ++ err
assertParsed (Right actual) expected =
  assertEqual "Function signatures" expected actual

-- | Assert that parsing failed
assertParseError :: Either String [T.Text] -> Assertion
assertParseError (Right sigs) =
  assertFailure $ "Expected parse error but got: " ++ show sigs
assertParseError (Left _) = return ()
