module Backend.Common
  ( -- * Multi-arch runtime testing
    BackendArch (..)
  , archName
  , backendArches
  , buildAndRunOn
  , exitCases
  , runOnceArch
    -- * Test Programs
  , testPrograms
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
  , testStrataDir
  , buildAndRunTrace
    -- * Common Types
  , tA
  , tB
  ) where

import Control.Exception (SomeException, try)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, findExecutable, makeAbsolute, removeDirectoryRecursive)
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (proc, env, readProcessWithExitCode, readCreateProcessWithExitCode)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

import Once.Type (Type (..))

------------------------------------------------------------------------
-- Multi-arch runtime testing (Plan 0.53): build each program for every
-- backend arch and run it — natively for x86_64, under qemu user-mode for
-- x86_32 / riscv64. `once` shells out to $AS/$LD/$OBJCOPY, so per-arch cross
-- tools are supplied via the compiler subprocess's environment. `once`
-- auto-links the matching `Strata/Interpretations/*.<arch>` impls.
------------------------------------------------------------------------

data BackendArch = X86_64 | X86_32 | RiscV64 deriving (Eq)

archName :: BackendArch -> String
archName X86_64  = "x86_64"
archName X86_32  = "x86_32"
archName RiscV64 = "riscv64"

-- | The arches the runtime/backend specs execute on.
backendArches :: [BackendArch]
backendArches = [X86_64, X86_32, RiscV64]

-- | Cross-tool env (AS/LD/OBJCOPY) for the `once` subprocess. x86_64 uses the
-- host defaults; x86_32 uses native binutils via thin --32 / -m elf_i386
-- wrappers (test/tools/); riscv64 uses the riscv64-unknown-linux-gnu toolchain.
archToolEnv :: BackendArch -> IO [(String, String)]
archToolEnv X86_64 = pure []
archToolEnv X86_32 = do
  asW <- makeAbsolute "test/tools/as-x86-32"
  ldW <- makeAbsolute "test/tools/ld-x86-32"
  pure [("AS", asW), ("LD", ldW)]
archToolEnv RiscV64 = pure
  [ ("AS", "riscv64-unknown-linux-gnu-as")
  , ("LD", "riscv64-unknown-linux-gnu-ld")
  , ("OBJCOPY", "riscv64-unknown-linux-gnu-objcopy") ]

-- | qemu prefix to run a built exe for this arch (empty = native).
archRunPrefix :: BackendArch -> [String]
archRunPrefix X86_64  = []
archRunPrefix X86_32  = ["qemu-i386"]
archRunPrefix RiscV64 = ["qemu-riscv64"]

-- | Run `once build …` with the arch's cross tools injected into the env.
runOnceArch :: BackendArch -> [String] -> IO (ExitCode, String, String)
runOnceArch arch args = do
  extra <- archToolEnv arch
  base  <- getEnvironment
  let env' = extra ++ filter ((`notElem` map fst extra) . fst) base
  onceInPath <- findExecutable "once"
  let cp = case onceInPath of
             Just p  -> proc p args
             Nothing -> proc "cabal" (["run", "once", "--"] ++ args)
  readCreateProcessWithExitCode cp { env = Just env' } ""

-- | Build `test/<name>.once` for `arch` and run it (native or qemu, with a
-- 10s wall-clock cap so a codegen bug that loops shows as a failure, not a
-- hang). Returns Right () iff the process exit code equals `expected`.
buildAndRunOn :: BackendArch -> String -> Int -> IO (Either String ())
buildAndRunOn arch name expected = do
  let tag     = archName arch
      testDir = "/tmp/once_" ++ tag ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
      exeFile = testDir </> name
  createDirectoryIfMissing True testDir
  source <- TIO.readFile ("test/" ++ name ++ ".once")
  TIO.writeFile srcFile source
  (buildExit, _out, buildErr) <- runOnceArch arch
    ["build", "--target", tag, "--alloc", "heap", "--no-optimize", "--exe", srcFile, "-o", exeFile]
  case buildExit of
    ExitFailure _ -> cleanupDir testDir >> pure (Left ("[" ++ tag ++ "] build failed: " ++ buildErr))
    ExitSuccess -> do
      (runExit, _rout, _rerr) <- readProcessWithExitCode "timeout"
        (["10"] ++ archRunPrefix arch ++ [exeFile]) ""
      cleanupDir testDir
      let code = case runExit of ExitSuccess -> 0; ExitFailure c -> c
      pure $ if code == expected
               then Right ()
               else Left ("[" ++ tag ++ "] expected exit " ++ show expected
                          ++ " but got " ++ show code
                          ++ (if code == 124 then " (TIMEOUT/hang)" else ""))

-- | One test program → a per-arch test group (each arch is its own case, so a
-- partial backend shows exactly which arches pass). Reads `test/<name>.once`.
exitCases :: String -> String -> Int -> TestTree
exitCases label name expected =
  testGroup label
    [ testCase (archName a) (buildAndRunOn a name expected >>= either assertFailure pure)
    | a <- backendArches ]

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

-- | Strata root for the trace tests. It contains the OBSERVABLE test
-- interpretation `I.Test.Emit` (whose `emit` writes a byte to stdout) and a
-- symlink to the real Linux interpretation (so `exit` comes from
-- `I.Linux.Syscalls`); a single --strata root resolves both imports. Relative
-- to the package dir, which is the cwd under `cabal test`. Reusable by any spec
-- wanting to observe an effect trace at runtime.
testStrataDir :: FilePath
testStrataDir = "test/teststrata"

-- | Build a Once program (given as source) for x86_64 against 'testStrataDir',
-- run it, and return @(stdout, exitCode)@ on success or a build error on the
-- left. The program imports `I.Test.Emit` and `I.Linux.Syscalls`; each `emit`
-- writes one stdout byte, so @stdout@ is the emitted byte sequence and the exit
-- code is the final `exit` argument. The compiler links the interpretation
-- implementations itself — no manual assembly/link step.
buildAndRunTrace :: String -> T.Text -> IO (Either String (String, Int))
buildAndRunTrace name source = do
  let testDir = "/tmp/once_trace_" ++ name
      srcFile = testDir </> name ++ ".once"
      exeFile = testDir </> name
  createDirectoryIfMissing True testDir
  TIO.writeFile srcFile source
  (buildExit, _out, buildErr) <- runOnce
    [ "build", "--target", "x86_64", "--exe"
    , "--strata", testStrataDir, srcFile, "-o", exeFile ]
  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "build failed: " ++ buildErr
    ExitSuccess -> do
      (runExit, runOut, _runErr) <- readProcessWithExitCode exeFile [] ""
      cleanupDir testDir
      let code = case runExit of ExitSuccess -> 0; ExitFailure c -> c
      return $ Right (runOut, code)

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
