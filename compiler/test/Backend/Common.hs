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
    -- * Effect-trace testing
  , traceRuntimeAsm
  , buildAndRunTrace
    -- * Common Types
  , tA
  , tB
  ) where

import Control.Exception (SomeException, try)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, doesFileExist, findExecutable, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Once.Type (Type (..))

-- | Common type variables for tests
tA, tB :: Type
tA = TVar "A"
tB = TVar "B"

-- | Run the once compiler. Tries 'once' directly first (for Nix builds),
-- falls back to 'cabal run once --' for development.
runOnce :: [String] -> IO (ExitCode, String, String)
runOnce args = do
  onceInPath <- findExecutable "once"
  case onceInPath of
    Just oncePath -> readProcessWithExitCode oncePath args ""
    Nothing -> readProcessWithExitCode "cabal" (["run", "once", "--"] ++ args) ""

-- | Cleanup a test directory, ignoring errors
cleanupDir :: FilePath -> IO ()
cleanupDir dir = do
  _ <- try (removeDirectoryRecursive dir) :: IO (Either SomeException ())
  return ()

-- | The observable runtime for effect-trace tests: a tiny x86_64 assembly file
-- providing `once_4emit` (write a byte to stdout) and `once_4exit` (exit). The
-- symbols are the SigOps' own names (Once.Target.Symbol.once-symbol-own), so a
-- program that declares `signature emit`/`signature exit` LOCALLY links against
-- them directly — no module-path mangling. Relative to the package dir (the cwd
-- under `cabal test`). Reusable by any spec wanting an observable trace.
traceRuntimeAsm :: FilePath
traceRuntimeAsm = "test/trace-runtime.s"

-- | Build a Once program (given as source) for x86_64, link it against the
-- trace runtime ('traceRuntimeAsm'), run it, and return @(stdout, exitCode)@
-- on success or an error on the left.
--
-- The program is expected to declare `signature emit : Eff Int Unit` and
-- `signature exit : Eff Int Unit` locally and observe a trace: each `emit`
-- writes one stdout byte, so @stdout@ is the emitted byte sequence and the exit
-- code is the final `exit` argument. `once build` links eagerly and reports the
-- (intentionally external) `once_4emit`/`once_4exit` as undefined; we use the
-- object file it produces and link the runtime ourselves with `ld`.
buildAndRunTrace :: String -> T.Text -> IO (Either String (String, Int))
buildAndRunTrace name source = do
  let testDir = "/tmp/once_trace_" ++ name
      srcFile = testDir </> name ++ ".once"
      base    = testDir </> name
      objFile = base ++ ".o"          -- emitted by `once build` (outputBase ++ ".o")
      rtObj   = testDir </> "trace-runtime.o"
      exeFile = base ++ ".exe"
  createDirectoryIfMissing True testDir
  TIO.writeFile srcFile source
  -- Compile. The link step fails on the external emit/exit symbols, but the
  -- object file is written first; a real source error leaves no object.
  _ <- runOnce ["build", "--target", "x86_64", "--exe", "--save-temps", srcFile, "-o", base]
  haveObj <- doesFileExist objFile
  if not haveObj
    then do
      (_, _, buildErr) <- runOnce ["check", srcFile]
      cleanupDir testDir
      return $ Left $ "compile failed: " ++ buildErr
    else do
      asResult <- run "as" [traceRuntimeAsm, "-o", rtObj]
      ldResult <- either (return . Left) (const (run "ld" [objFile, rtObj, "-o", exeFile])) asResult
      case ldResult of
        Left err -> cleanupDir testDir >> return (Left err)
        Right () -> do
          (runExit, runOut, _) <- readProcessWithExitCode exeFile [] ""
          cleanupDir testDir
          let code = case runExit of ExitSuccess -> 0; ExitFailure c -> c
          return $ Right (runOut, code)
  where
    run cmd args = do
      (ec, _out, err) <- readProcessWithExitCode cmd args ""
      return $ case ec of
        ExitSuccess   -> Right ()
        ExitFailure _ -> Left (cmd ++ " failed: " ++ err)

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

-- | Basic hello world (using let binding for effect sequencing)
helloOnce :: T.Text
helloOnce = T.unlines
  [ "-- hello.once: Hello World for Once"
  , "primitive println : Eff (String Utf8) Unit"
  , "primitive exit0 : Eff Unit Unit"
  , ""
  , "main : IO Unit"
  , "main = let result = println \"Hello for Once\" in exit0"
  ]

-- | Hello without allocation annotation (uses default)
helloOnceNoAlloc :: T.Text
helloOnceNoAlloc = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , "primitive exit0 : Eff Unit Unit"
  , ""
  , "main : IO Unit"
  , "main = let result = println \"Hello for Once\" in exit0"
  ]

-- | Hello with explicit allocation strategy
helloOnceWithAlloc :: String -> T.Text
helloOnceWithAlloc strat = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , "primitive exit0 : Eff Unit Unit"
  , ""
  , "main : IO Unit"
  , "main @" <> T.pack strat <> " = let result = println \"Hello for Once\" in exit0"
  ]

-- | Multiple string literals
multiStringOnce :: T.Text
multiStringOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "print3 : IO Unit"
  , "print3 = compose println \"Third\""
  , ""
  , "print2 : IO Unit"
  , "print2 = compose println \"Second\" . print3"
  , ""
  , "main : IO Unit"
  , "main = compose println \"First\" . print2"
  ]

-- | Empty string (edge case)
emptyStringOnce :: T.Text
emptyStringOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"\""
  ]

-- | Unicode characters
unicodeOnce :: T.Text
unicodeOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"Hello 世 World\""
  ]

-- | Long string (100 x's)
longStringOnce :: T.Text
longStringOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"" <> T.replicate 100 "x" <> "\""
  ]

-- | Escaped characters
escapedOnce :: T.Text
escapedOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"Tab:\\tNewline:\\nQuote:\\\"\""
  ]

-- | Nested function calls with strings
nestedOnce :: T.Text
nestedOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "inner : IO Unit"
  , "inner = compose println \"Inner\""
  , ""
  , "outer : IO Unit"
  , "outer = compose println \"Outer\""
  , ""
  , "main : IO Unit"
  , "main = inner . outer"
  ]

-- | Multiple functions each with their own string
multiFuncOnce :: T.Text
multiFuncOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "func1 : IO Unit"
  , "func1 = compose println \"Func1\""
  , ""
  , "func2 : IO Unit"
  , "func2 = compose println \"Func2\""
  , ""
  , "main : IO Unit"
  , "main = func1 . func2"
  ]

-- | Conditional string (using case - tests sum types with strings)
-- Note: This is a placeholder - actual conditional would need Bool type
conditionalOnce :: T.Text
conditionalOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"Branch A\""
  ]

-- | String in product type (placeholder)
productOnce :: T.Text
productOnce = T.unlines
  [ "primitive println : Eff (String Utf8) Unit"
  , ""
  , "main : IO Unit"
  , "main = compose println \"Left Right\""
  ]

-- | Simple exit program
hiOnce :: T.Text
hiOnce = T.unlines
  [ "-- hi.once: The simplest Once executable"
  , "primitive exit0 : Eff Unit Unit"
  , ""
  , "main : IO Unit"
  , "main = exit0"
  ]
