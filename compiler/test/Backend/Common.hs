module Backend.Common
  ( -- * Test Programs
    testPrograms
  , helloOnce
  , helloOnceNoAlloc
  , helloOnceWithAlloc
  , multiStringOnce
  , emptyStringOnce
  , unicodeOnce
  , longStringOnce
  , escapedOnce
  , nestedOnce
  , multiFuncOnce
  , conditionalOnce
  , productOnce
  , hiOnce
    -- * Test Utilities
  , runOnce
  , cleanupDir
  , testMain
    -- * Common Types
  , tA
  , tB
  ) where

import Control.Exception (SomeException, try)
import qualified Data.Text as T
import System.Directory (findExecutable, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

import Once.Type (Type (..))

-- | Common type variables for tests
tA, tB :: Type
tA = TVar "A"
tB = TVar "B"

-- | Run the once compiler. Tries 'once' directly first (for Nix builds),
-- falls back to 'stack exec -- once' for development.
runOnce :: [String] -> IO (ExitCode, String, String)
runOnce args = do
  onceInPath <- findExecutable "once"
  case onceInPath of
    Just oncePath -> readProcessWithExitCode oncePath args ""
    Nothing -> readProcessWithExitCode "stack" (["exec", "--", "once"] ++ args) ""

-- | Cleanup a test directory, ignoring errors
cleanupDir :: FilePath -> IO ()
cleanupDir dir = do
  _ <- try (removeDirectoryRecursive dir) :: IO (Either SomeException ())
  return ()

-- | Test main for C swap test
testMain :: T.Text
testMain = T.unlines
  [ "#include <stdio.h>"
  , "#include \"once_swap.h\""
  , ""
  , "int main() {"
  , "    OncePair input = { .fst = (void*)1, .snd = (void*)2 };"
  , "    OncePair output = once_swap(input);"
  , "    printf(\"swap(%ld,%ld) = (%ld,%ld)\\n\","
  , "           (long)input.fst, (long)input.snd,"
  , "           (long)output.fst, (long)output.snd);"
  , "    return 0;"
  , "}"
  ]

-- | Test programs with expected output for allocation independence tests
-- Format: (name, source, expectedOutput)
testPrograms :: [(String, T.Text, String)]
testPrograms =
  [ ("hello", helloOnce, "Hello for Once\n")
  , ("multiString", multiStringOnce, "First\nSecond\nThird\n")
  , ("emptyString", emptyStringOnce, "\n")
  , ("unicodeString", unicodeOnce, "Hello 世 World\n")
  , ("longString", longStringOnce, replicate 100 'x' ++ "\n")
  , ("escapedChars", escapedOnce, "Tab:\tNewline:\nQuote:\"\n")
  , ("nestedCalls", nestedOnce, "Inner\nOuter\n")
  , ("multiFunction", multiFuncOnce, "Func1\nFunc2\n")
  ]

-- | Basic hello world
helloOnce :: T.Text
helloOnce = T.unlines
  [ "-- hello.once: Hello World for Once"
  , "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Hello for Once\""
  ]

-- | Hello without allocation annotation (uses default)
helloOnceNoAlloc :: T.Text
helloOnceNoAlloc = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Hello for Once\""
  ]

-- | Hello with explicit allocation strategy
helloOnceWithAlloc :: String -> T.Text
helloOnceWithAlloc strat = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main @" <> T.pack strat <> " = puts \"Hello for Once\""
  ]

-- | Multiple string literals
multiStringOnce :: T.Text
multiStringOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "print3 : Unit -> Unit"
  , "print3 = puts \"Third\""
  , ""
  , "print2 : Unit -> Unit"
  , "print2 = puts \"Second\" . print3"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"First\" . print2"
  ]

-- | Empty string (edge case)
emptyStringOnce :: T.Text
emptyStringOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"\""
  ]

-- | Unicode characters
unicodeOnce :: T.Text
unicodeOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Hello 世 World\""
  ]

-- | Long string (100 x's)
longStringOnce :: T.Text
longStringOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"" <> T.replicate 100 "x" <> "\""
  ]

-- | Escaped characters
escapedOnce :: T.Text
escapedOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Tab:\\tNewline:\\nQuote:\\\"\""
  ]

-- | Nested function calls with strings
nestedOnce :: T.Text
nestedOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "inner : Unit -> Unit"
  , "inner = puts \"Inner\""
  , ""
  , "outer : Unit -> Unit"
  , "outer = puts \"Outer\""
  , ""
  , "main : Unit -> Unit"
  , "main = inner . outer"
  ]

-- | Multiple functions each with their own string
multiFuncOnce :: T.Text
multiFuncOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "func1 : Unit -> Unit"
  , "func1 = puts \"Func1\""
  , ""
  , "func2 : Unit -> Unit"
  , "func2 = puts \"Func2\""
  , ""
  , "main : Unit -> Unit"
  , "main = func1 . func2"
  ]

-- | Conditional string (using case - tests sum types with strings)
-- Note: This is a placeholder - actual conditional would need Bool type
conditionalOnce :: T.Text
conditionalOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Branch A\""
  ]

-- | String in product type (placeholder)
productOnce :: T.Text
productOnce = T.unlines
  [ "primitive puts : String Utf8 -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = puts \"Left Right\""
  ]

-- | Simple exit program
hiOnce :: T.Text
hiOnce = T.unlines
  [ "-- hi.once: The simplest Once executable"
  , "primitive exit0 : Unit -> Unit"
  , ""
  , "main : Unit -> Unit"
  , "main = exit0"
  ]
