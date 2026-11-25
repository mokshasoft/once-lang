module Backend.Common
  ( -- * Multi-arch runtime testing
    BackendArch (..)
  , archName
  , backendArches
  , buildAsmOn
  , End (..)
  , TestHost (..)
  , testHost
  , endOfStatus
  , assertEnd
  , valueCases
  , runCases
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
  , buildAndRunTraceOn
  , buildAndRunTraceWith
  , buildAndRunTraceFile
  , traceCases
  , foreverCases
  , archWordBytes
  , decodeTrace
  , signedAt
    -- * Common Types
  , tA
  , tB
  ) where

import Control.Exception (SomeException, try)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, findExecutable, listDirectory, makeAbsolute, removeDirectoryRecursive)
import System.Environment (getEnvironment, lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeExtension)
import System.IO (IOMode (WriteMode), withFile)
import qualified Data.ByteString as BS
import System.Process (proc, env, std_out, StdStream (UseHandle), createProcess,
                       waitForProcess, readProcessWithExitCode, readCreateProcessWithExitCode)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertEqual)

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

-- | The Host the runtime tests run under (plan 0.140 §3.6):
-- `ONCE_TEST_HOST=linux` (the default) runs each image as a Linux process,
-- natively or under qemu user mode; `ONCE_TEST_HOST=bare` builds it for the
-- bare-metal Host of the arch's QEMU machine (`Bare/Virt` on riscv64,
-- `Bare/PC` on x86) and boots it under qemu-system, the UART on stdout.
data TestHost = LinuxHost | BareHost deriving (Eq, Show)

testHost :: IO TestHost
testHost = do
  v <- lookupEnv "ONCE_TEST_HOST"
  case v of
    Just "bare" -> pure BareHost
    _           -> pure LinuxHost

-- | The `once build` flags that pick the Host.
hostBuildFlags :: TestHost -> BackendArch -> [String]
hostBuildFlags LinuxHost _       = []
hostBuildFlags BareHost RiscV64  = ["--host", "Bare/Virt"]
hostBuildFlags BareHost _        = ["--host", "Bare/PC"]

-- | The command prefix that runs a built image (empty = native).
hostRunPrefix :: TestHost -> BackendArch -> [String]
hostRunPrefix LinuxHost X86_64  = []
hostRunPrefix LinuxHost X86_32  = ["qemu-i386"]
hostRunPrefix LinuxHost RiscV64 = ["qemu-riscv64"]
hostRunPrefix BareHost  RiscV64 =
  ["qemu-system-riscv64", "-machine", "virt", "-bios", "none"] ++ qemuBare ++ ["-kernel"]
hostRunPrefix BareHost  arch    =
  [if arch == X86_32 then "qemu-system-i386" else "qemu-system-x86_64"]
    ++ qemuBare ++ ["-device", "isa-debug-exit,iobase=0xf4,iosize=0x04", "-kernel"]

qemuBare :: [String]
qemuBare = ["-display", "none", "-serial", "stdio", "-monitor", "none", "-no-reboot"]

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

-- | How a run ended (plan 0.140 §3.5). The Spec has three ends (D374), and
-- the end is a kind: it carries no value. A value a test observes goes in the
-- trace (`I.Test.Emit`).
data End = Returned | Exhausted | Halted deriving (Eq, Show)

-- | A Host's end table, its exit device's, read off the status as the runner
-- sees it. Linux: `exit_group(0)` is `returned`, `I.Halt`'s `exit_group(2)`
-- is `halted`, `once_exhausted`'s SIGABRT is `exhausted` (134 through
-- `timeout`, -6 when the signal is passed on). `Bare/Virt`: the test
-- finisher's 0, 1, 2. `Bare/PC`: `isa-debug-exit`'s (v << 1) | 1, so 1, 3, 5.
-- Any other status is no end of the Spec: a timeout (124), or a defect of the
-- trusted base.
endOfStatus :: TestHost -> BackendArch -> Int -> Either Int End
endOfStatus LinuxHost _ c = case c of
  0    -> Right Returned
  2    -> Right Halted
  134  -> Right Exhausted
  (-6) -> Right Exhausted
  _    -> Left c
endOfStatus BareHost RiscV64 c = case c of
  0 -> Right Returned
  1 -> Right Exhausted
  2 -> Right Halted
  _ -> Left c
endOfStatus BareHost _ c = case c of
  1 -> Right Returned
  3 -> Right Exhausted
  5 -> Right Halted
  _ -> Left c

-- | Assert that a run ended @want@.
assertEnd :: String -> End -> Either Int End -> IO ()
assertEnd tag want got = case got of
  Right e -> assertEqual (tag ++ " end") want e
  Left c  -> assertFailure (tag ++ " expected end " ++ show want ++ ", got status " ++ show c
                            ++ " (no end of the Spec" ++ (if c == 124 then ": TIMEOUT/hang)" else ")"))

-- | Build `test/<name>.once` for `arch` with `--save-temps` and return the
-- emitted assembly text. Goes through `runOnceArch`, the same build path the
-- runtime tests use, so the two cannot disagree about how a test program is
-- compiled — which is the whole point of not writing this as a shell script.
buildAsmOn :: BackendArch -> String -> IO (Either String String)
buildAsmOn arch name = do
  let tag     = archName arch
      testDir = "/tmp/once_asm_" ++ tag ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
      exeFile = testDir </> name
  createDirectoryIfMissing True testDir
  source <- TIO.readFile ("test/" ++ name ++ ".once")
  TIO.writeFile srcFile source
  (buildExit, _out, buildErr) <- runOnceArch arch
    ["build", "--target", tag, "--no-optimize", "--save-temps"
    , "--exe", srcFile, "-o", exeFile]
  case buildExit of
    ExitFailure _ -> cleanupDir testDir >> pure (Left ("[" ++ tag ++ "] build failed: " ++ buildErr))
    ExitSuccess -> do
      entries <- listDirectory testDir
      case filter ((== ".s") . takeExtension) entries of
        []      -> cleanupDir testDir >> pure (Left ("[" ++ tag ++ "] --save-temps left no .s"))
        (sf : _) -> do
          asm <- readFile (testDir </> sf)
          length asm `seq` cleanupDir testDir
          pure (Right asm)

-- | A `.once` FILE that computes one value: it emits @v@ and returns. One
-- per-arch test group (each arch is its own case, so a partial backend shows
-- exactly which arches pass), built with `--no-optimize`; 'traceCases' is the
-- same check with and without the optimizer.
valueCases :: String -> String -> Integer -> TestTree
valueCases label name v = runCases label name [v] Returned

-- | A `.once` FILE's trace and end, on every backend arch, built with
-- `--no-optimize`.
runCases :: String -> String -> [Integer] -> End -> TestTree
runCases label name emitted end =
  testGroup label
    [ testCase (archName a) (runTraceFile ["--no-optimize"] a name emitted end)
    | a <- backendArches ]

-- | 'buildAndRunTraceWith' for a `.once` FILE in `test/`, rather than inline
-- source. Everything else is shared with `buildAndRunTraceWith`, so a
-- file-based trace test and an inline one cannot disagree about how a program
-- is compiled.
buildAndRunTraceFile :: [String] -> BackendArch -> String -> IO (Either String (String, Either Int End))
buildAndRunTraceFile flags arch name = do
  source <- TIO.readFile ("test/" ++ name ++ ".once")
  buildAndRunTraceWith flags arch name source

-- | Assert a `.once` FILE's whole observable: the ordered SigOp trace AND the
-- end, on every backend arch, built with the optimizer and without it.
--
-- The trace is the observable (D058); the end is a kind and carries no value
-- (plan 0.140 §3.5).
traceCases :: String -> String -> [Integer] -> End -> TestTree
traceCases label name emitted end =
  testGroup label
    [ testCase (archName a ++ concatMap (' ' :) flags) (runTraceFile flags a name emitted end)
    | a <- backendArches, flags <- [[], ["--no-optimize"]] ]

-- | Build and run a `.once` FILE, and assert its trace (each word read as a
-- signed `Int`) and its end.
runTraceFile :: [String] -> BackendArch -> String -> [Integer] -> End -> IO ()
runTraceFile flags a name emitted end = do
  r <- buildAndRunTraceFile flags a name
  case r of
    Left err -> assertFailure err
    Right (out, code) -> case decodeTrace a out of
      Left err -> assertFailure ("[" ++ archName a ++ "] " ++ err)
      Right ws -> do
        assertEqual ("[" ++ archName a ++ "] emitted arguments (effect order + values)")
                    emitted (map (signedAt a) ws)
        assertEnd ("[" ++ archName a ++ "]") end code

-- | A `.once` FILE that must never end (D317: a server is the anamorphism into
-- `Eff`, which need not stop). On every backend arch it is run for `foreverSecs`
-- seconds and must still be running when `timeout` stops it (status 124), with
-- a trace that starts with `prefix` (empty: the trace stays empty, D317 item 5,
-- "never arrives"). Only the bytes of the prefix are read: an endless emitter
-- writes megabytes in that time.
foreverCases :: String -> String -> [Integer] -> TestTree
foreverCases label name prefix =
  testGroup label
    [ testCase (archName a) $ do
        r <- buildAndRunForever a name
        case r of
          Left err -> assertFailure err
          Right (out, code) -> do
            assertEqual ("[" ++ archName a ++ "] still running when stopped (timeout's status)")
                        124 code
            case decodeTrace a out of
              Left err -> assertFailure ("[" ++ archName a ++ "] " ++ err)
              Right ws -> assertEqual ("[" ++ archName a ++ "] the trace's first words")
                                      prefix (map (signedAt a) ws)
    | a <- backendArches ]
  where
    buildAndRunForever arch nm = do
      let tag     = archName arch
          testDir = "/tmp/once_forever_" ++ tag ++ "_" ++ nm
          exeFile = testDir </> nm
          want    = length prefix * archWordBytes arch
      createDirectoryIfMissing True testDir
      host <- testHost
      (buildExit, _out, buildErr) <- runOnceArch arch
        ([ "build", "--target", tag, "--exe"
         , "--strata", testStrataDir, "test/" ++ nm ++ ".once", "-o", exeFile ]
         ++ hostBuildFlags host arch)
      case buildExit of
        ExitFailure _ -> do
          cleanupDir testDir
          pure (Left ("[" ++ tag ++ "] build failed: " ++ buildErr))
        ExitSuccess -> do
          let outPath = testDir </> "stdout.bin"
          code <- withFile outPath WriteMode $ \h -> do
            (_, _, _, ph) <- createProcess
              (proc "timeout" ([show foreverSecs] ++ hostRunPrefix host arch ++ [exeFile]))
                { std_out = UseHandle h }
            runExit <- waitForProcess ph
            pure (case runExit of ExitSuccess -> 0; ExitFailure c -> c)
          raw <- BS.readFile outPath
          let out = map (toEnum . fromIntegral) (BS.unpack (BS.take want raw))
          length out `seq` cleanupDir testDir
          pure (Right (out, code))

-- | How long a never-ending program runs before it is stopped.
foreverSecs :: Int
foreverSecs = 1

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

-- | Strata root for the runtime tests: the repository's `Strata`, relative to
-- the package dir, which is the cwd under `cabal test`.
testStrataDir :: FilePath
testStrataDir = "../Strata"

-- | Build a Once program (given as source) for x86_64 against 'testStrataDir',
-- run it, and return @(stdout, status)@ on success or a build error on the
-- left. Each `emit` writes one machine word to stdout, so @stdout@ is the
-- trace ('decodeTrace'); the status gives the end ('endOfStatus'). The
-- compiler links the interpretation implementations itself.
buildAndRunTrace :: String -> T.Text -> IO (Either String (String, Either Int End))
buildAndRunTrace = buildAndRunTraceOn X86_64

-- | This target's machine word, in bytes. `emit`/`emitF` write exactly one of
-- these per invocation, so it is also the trace's frame size.
archWordBytes :: BackendArch -> Int
archWordBytes X86_32 = 4
archWordBytes _      = 8

-- | Reinterpret a machine word as the SIGNED value it represents.
--
-- Once has only signed integers, so this is how an `Int` argument is read back
-- from a trace. It is deliberately NOT folded into `decodeTrace`: a trace
-- carries REPRESENTATIONS, and how to read one is decided by the argument's
-- TYPE — the same split the spec makes when `ev-arg : ⟦ ev-dom ⟧` is read at
-- its own base type. An `Int` is read as two's complement; a `Float`'s word is
-- a bit pattern and is compared as-is.
--
-- It also makes `Int` expectations ARCH-INDEPENDENT: −5 is `0xFFFFFFFFFFFFFFFB`
-- at 64 bits and `0xFFFFFFFB` at 32, and both read back as −5.
signedAt :: BackendArch -> Integer -> Integer
signedAt arch w
  | w >= half = w - 2 * half
  | otherwise = w
  where half = 2 ^ (8 * archWordBytes arch - 1)

-- | Decode a raw emit trace into the SEQUENCE OF ARGUMENTS it carries.
--
-- The observable interpretation writes one whole machine word per `emit` /
-- `emitF`, little-endian, so the trace is a frame sequence and this is its
-- reader. A length that is not a whole number of words means a truncated or
-- over-long write — reported rather than silently rounded, because that is
-- exactly the kind of argument-passing bug the trace exists to catch.
decodeTrace :: BackendArch -> String -> Either String [Integer]
decodeTrace arch out
  | r /= 0    = Left ("trace is " ++ show n ++ " bytes, not a whole number of "
                      ++ show w ++ "-byte words: " ++ show (map fromEnum out))
  | otherwise = Right (go bytes)
  where
    w          = archWordBytes arch
    bytes      = map fromEnum out
    n          = length bytes
    (_, r)     = n `divMod` w
    go []      = []
    go bs      = let (this, rest) = splitAt w bs
                 in le this : go rest
    le         = foldr (\b acc -> acc * 256 + fromIntegral b) 0

-- | 'buildAndRunTrace' at a chosen arch (plan 0.73 G5). The observable test
-- interpretation now has an implementation for all three, so an effect trace
-- can be read back on each — which is what makes a FLOAT argument's encoding
-- observable at RUNTIME rather than only in the emitted assembly: the same
-- literal emits eight bytes of `binary64` here and four of `binary32` on
-- x86-32, because a `Float` denotes its target's representation (D113).
buildAndRunTraceOn :: BackendArch -> String -> T.Text -> IO (Either String (String, Either Int End))
buildAndRunTraceOn = buildAndRunTraceWith []

-- | 'buildAndRunTraceOn' with extra build flags (e.g. `--no-optimize`).
buildAndRunTraceWith :: [String] -> BackendArch -> String -> T.Text -> IO (Either String (String, Either Int End))
buildAndRunTraceWith flags arch name source = do
  let tag     = archName arch
      testDir = "/tmp/once_trace_" ++ tag ++ concat flags ++ "_" ++ name
      srcFile = testDir </> name ++ ".once"
      exeFile = testDir </> name
  createDirectoryIfMissing True testDir
  TIO.writeFile srcFile source
  host <- testHost
  (buildExit, _out, buildErr) <- runOnceArch arch
    ([ "build", "--target", tag, "--exe"
     , "--strata", testStrataDir, srcFile, "-o", exeFile ] ++ flags ++ hostBuildFlags host arch)
  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "[" ++ tag ++ "] build failed: " ++ buildErr
    ExitSuccess -> do
      -- Read the child's stdout as RAW BYTES. An effect trace is a byte
      -- sequence, not text: `emitF` writes a float's machine word, and a
      -- `binary64` pattern contains bytes like 0xE0 that are not valid UTF-8,
      -- so decoding stdout as text throws instead of reporting the trace.
      -- Each byte becomes one `Char` (latin-1), which is exactly what callers
      -- already assume when they say `map fromEnum out`.
      let outPath = testDir </> "stdout.bin"
      code <- withFile outPath WriteMode $ \h -> do
        (_, _, _, ph) <- createProcess
          (proc "timeout" (["10"] ++ hostRunPrefix host arch ++ [exeFile]))
            { std_out = UseHandle h }
        runExit <- waitForProcess ph
        pure (case runExit of ExitSuccess -> 0; ExitFailure c -> c)
      raw <- BS.readFile outPath
      let out = map (toEnum . fromIntegral) (BS.unpack raw)
      length out `seq` cleanupDir testDir
      return $ Right (out, endOfStatus host arch code)

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
