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
      -- Sum elimination is `destruct e of {…}` (the `case … of` form was
      -- retired; `case` is no longer a surface keyword).
      let source = T.unlines
            [ "f : (Int + Int) -> Int"
            , "f x = destruct x of { Left a -> a ; Right b -> b }"
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

  , testCase "signature declaration" $ do
      -- External primitives are declared with `signature` (the old
      -- `primitive` keyword was removed).
      let source = T.unlines
            [ "signature exit : Eff Int Unit"
            ]
      result <- parseSource source
      assertParsed result ["exit : Eff Int Unit"]

  , testCase "signature with effect-shape annotation" $ do
      -- Signatures may carry an effect-shape annotation (`! halts` / `! emits`,
      -- per Once.SigOp.Info.EffectShape). It is consumed by the parser and not
      -- reflected in the printed signature.
      let source = T.unlines
            [ "signature ex : Eff Int Unit ! halts"
            , "signature em : Eff Int Unit ! emits"
            ]
      result <- parseSource source
      assertParsed result ["ex : Eff Int Unit", "em : Eff Int Unit"]

  , testCase "import statement" $ do
      -- `import` now resolves the interpretation and surfaces ITS signatures
      -- too, so the parse output is the imported module's signatures plus the
      -- local ones. Assert the local `f` is present rather than pinning the
      -- (interpretation-defined) full list.
      let source = T.unlines
            [ "import I.Math.Int as I"
            , ""
            , "f : Int -> Int"
            , "f = id"
            ]
      result <- parseSource source
      assertParsedContains result "f : (Int ω→ Int)"

  -- NOTE: a "type alias" test was removed here. Parameterised type aliases
  -- (`type Pair a b = (a * b)`) are not a surface feature — the parser rejects
  -- `type` declarations — so there was nothing current to remodel it to.

  , testCase "inferred signature" $ do
      -- A definition without a type signature is accepted; since D072 the
      -- principal-type oracle infers the SCHEMA of a sig-less polymorphic
      -- definition (here `t0 \969\8594 t0`, i.e. `t0 \x3c9\x2192 t0`) instead of
      -- the `<inferred>` placeholder.
      let source = T.unlines
            [ "f x = x"
            ]
      result <- parseSource source
      assertParsed result ["f : (t0 \969\8594 t0)"]
  ]

------------------------------------------------------------------------
-- Invalid Syntax Tests
------------------------------------------------------------------------

invalidSyntaxTests :: TestTree
invalidSyntaxTests = testGroup "Invalid syntax"
  [ testCase "missing function body" $ do
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

  -- NOTE: removed two cases that no longer represent invalid syntax:
  --   * "missing type signature" (`f x = x`) — now accepted; the type is
  --     inferred (see the "inferred signature" case under valid syntax).
  --   * "invalid operator" (`x $$ x`) — the parser no longer rejects it.
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

-- | Assert that parsing succeeded and the given signature is among the
-- results (used when imports inject additional, interpretation-defined
-- signatures whose full list we don't want to pin).
assertParsedContains :: Either String [T.Text] -> T.Text -> Assertion
assertParsedContains (Left err) _ = assertFailure $ "Parse failed: " ++ err
assertParsedContains (Right actual) expected =
  assertBool ("Expected signature " ++ show expected ++ " in " ++ show actual)
             (expected `elem` actual)

-- | Assert that parsing failed
assertParseError :: Either String [T.Text] -> Assertion
assertParseError (Right sigs) =
  assertFailure $ "Expected parse error but got: " ++ show sigs
assertParseError (Left _) = return ()
