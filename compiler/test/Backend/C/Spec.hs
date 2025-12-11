module Backend.C.Spec (cBackendTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (forM)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

import Once.Backend.C (generateC, CModule (..))
import Once.IR (IR (..))
import Once.Type (Type (..))

import Backend.Common

-- | All C backend tests
cBackendTests :: TestTree
cBackendTests = testGroup "C"
  [ codegenTests
  , gccCompilationTests
  , executableModeTests
  , allocationTests
  ]

-- | Tests for C code generation from IR
codegenTests :: TestTree
codegenTests = testGroup "codegen"
  [ testGroup "swap.once"
      [ testCase "generates correct header" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header _ = generateC "swap" swapTy swapIR
          assertBool "has include guard" $ T.isInfixOf "ONCE_SWAP_H" header
          assertBool "has OncePair typedef" $ T.isInfixOf "typedef struct" header
          assertBool "has function decl" $ T.isInfixOf "once_swap" header

      , testCase "generates correct source" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule _ source = generateC "swap" swapTy swapIR
          assertBool "has include" $ T.isInfixOf "#include" source
          assertBool "has function def" $ T.isInfixOf "once_swap" source
          assertBool "swaps fst and snd" $ T.isInfixOf "x.snd" source && T.isInfixOf "x.fst" source

      , testCase "no duplicate typedefs" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header _ = generateC "swap" swapTy swapIR
          let count = length $ filter (== "typedef struct { void* fst; void* snd; } OncePair;") (T.lines header)
          assertEqual "exactly one OncePair typedef" 1 count
      ]

  , testGroup "id function"
      [ testCase "id generates identity" $ do
          let idTy = TArrow tA tA
              idIR = Id tA
              CModule _ source = generateC "identity" idTy idIR
          assertBool "returns input unchanged" $ T.isInfixOf "return x;" source
      ]

  , testGroup "projections"
      [ testCase "fst generates .fst access" $ do
          let fstTy = TArrow (TProduct tA tB) tA
              fstIR = Fst tA tB
              CModule _ source = generateC "first" fstTy fstIR
          assertBool "accesses .fst" $ T.isInfixOf "x.fst" source

      , testCase "snd generates .snd access" $ do
          let sndTy = TArrow (TProduct tA tB) tB
              sndIR = Snd tA tB
              CModule _ source = generateC "second" sndTy sndIR
          assertBool "accesses .snd" $ T.isInfixOf "x.snd" source
      ]

  , testGroup "composition"
      [ testCase "compose generates nested expression" $ do
          let ty = TArrow (TProduct tA tB) tA
              ir = Compose (Fst tA tB) (Id (TProduct tA tB))
              CModule _ source = generateC "comp" ty ir
          assertBool "has fst access" $ T.isInfixOf ".fst" source
      ]
  ]

-- | Tests for gcc compilation of generated code
gccCompilationTests :: TestTree
gccCompilationTests = testGroup "gcc compilation"
  [ testCase "generated swap.c compiles with gcc" $ do
      let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
          swapIR = Pair (Snd tA tB) (Fst tA tB)
          CModule header source = generateC "swap" swapTy swapIR
          dir = "/tmp/once_test_syntax"

      createDirectoryIfMissing True dir
      TIO.writeFile (dir ++ "/once_swap.h") header
      TIO.writeFile (dir ++ "/once_swap.c") source

      (exitCode, _, stderr) <- readProcessWithExitCode "gcc"
        ["-c", "-fsyntax-only", dir ++ "/once_swap.c"] ""

      removeDirectoryRecursive dir

      case exitCode of
        ExitSuccess -> pure ()
        ExitFailure _ -> assertFailure $ "gcc failed: " ++ stderr

  , testCase "generated swap runs correctly" $ do
      let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
          swapIR = Pair (Snd tA tB) (Fst tA tB)
          CModule header source = generateC "swap" swapTy swapIR
          dir = "/tmp/once_test_run"

      createDirectoryIfMissing True dir
      TIO.writeFile (dir ++ "/once_swap.h") header
      TIO.writeFile (dir ++ "/once_swap.c") source
      TIO.writeFile (dir ++ "/test_swap.c") testMain

      (compileCode, _, compileErr) <- readProcessWithExitCode "gcc"
        ["-o", dir ++ "/test_swap", dir ++ "/once_swap.c", dir ++ "/test_swap.c"] ""

      case compileCode of
        ExitFailure _ -> do
          removeDirectoryRecursive dir
          assertFailure $ "gcc compile failed: " ++ compileErr
        ExitSuccess -> do
          (runCode, stdout, runErr) <- readProcessWithExitCode (dir ++ "/test_swap") [] ""
          removeDirectoryRecursive dir
          case runCode of
            ExitFailure _ -> assertFailure $ "run failed: " ++ runErr
            ExitSuccess -> assertEqual "swap output" "swap(1,2) = (2,1)\n" stdout
  ]

-- | Tests for executable mode with interpretations
executableModeTests :: TestTree
executableModeTests = testGroup "executable mode"
  [ testCase "hi.once compiles with interpretation" $ do
      let dir = "/tmp/once_test_exe"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hi.once") hiOnce

      (exitCode, _, stderr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hi.once", "-o", dir ++ "/hi"]

      case exitCode of
        ExitFailure _ -> do
          removeDirectoryRecursive dir
          assertFailure $ "once build failed: " ++ stderr
        ExitSuccess -> do
          source <- TIO.readFile (dir ++ "/hi.c")
          assertBool "has stdlib include" $ T.isInfixOf "#include <stdlib.h>" source
          assertBool "has exit0 implementation" $ T.isInfixOf "exit(0)" source
          assertBool "has main function" $ T.isInfixOf "int main(void)" source
          assertBool "calls once_main" $ T.isInfixOf "once_main" source
          removeDirectoryRecursive dir

  , testCase "hi.once executable runs and exits 0" $ do
      let dir = "/tmp/once_test_exe_run"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hi.once") hiOnce

      (compilerCode, _, compilerErr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hi.once", "-o", dir ++ "/hi"]

      case compilerCode of
        ExitFailure _ -> do
          removeDirectoryRecursive dir
          assertFailure $ "once build failed: " ++ compilerErr
        ExitSuccess -> do
          (compileCode, _, compileErr) <- readProcessWithExitCode "gcc"
            ["-o", dir ++ "/hi", dir ++ "/hi.c"] ""

          case compileCode of
            ExitFailure _ -> do
              removeDirectoryRecursive dir
              assertFailure $ "gcc compile failed: " ++ compileErr
            ExitSuccess -> do
              (runCode, _, _) <- readProcessWithExitCode (dir ++ "/hi") [] ""
              removeDirectoryRecursive dir
              assertEqual "exit code is 0" ExitSuccess runCode

  , testCase "interpretation provides primitives" $ do
      let dir = "/tmp/once_test_prim"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hi.once") hiOnce

      (exitCode, _, stderr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hi.once", "-o", dir ++ "/hi"]

      case exitCode of
        ExitFailure _ -> do
          removeDirectoryRecursive dir
          assertFailure $ "once build failed: " ++ stderr
        ExitSuccess -> do
          source <- TIO.readFile (dir ++ "/hi.c")
          assertBool "exit0 takes void* parameter" $ T.isInfixOf "exit0(void* x)" source
          assertBool "exit0 calls exit(0)" $ T.isInfixOf "exit(0)" source
          removeDirectoryRecursive dir

  , testCase "hello.once with string literal runs correctly" $ do
      let dir = "/tmp/once_test_hello"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hello.once") helloOnce

      (compilerCode, _, compilerErr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hello.once", "-o", dir ++ "/hello"]

      case compilerCode of
        ExitFailure _ -> do
          removeDirectoryRecursive dir
          assertFailure $ "once build failed: " ++ compilerErr
        ExitSuccess -> do
          (compileCode, _, compileErr) <- readProcessWithExitCode "gcc"
            ["-o", dir ++ "/hello", dir ++ "/hello.c"] ""

          case compileCode of
            ExitFailure _ -> do
              removeDirectoryRecursive dir
              assertFailure $ "gcc compile failed: " ++ compileErr
            ExitSuccess -> do
              (runCode, stdout, _) <- readProcessWithExitCode (dir ++ "/hello") [] ""
              removeDirectoryRecursive dir
              assertEqual "exit code is 0" ExitSuccess runCode
              assertEqual "output is Hello for Once" "Hello for Once\n" stdout
  ]

-- | Tests for allocation strategies
allocationTests :: TestTree
allocationTests = testGroup "allocation"
  [ testCase "all allocation strategies produce same output" $ do
      let strategies = [Nothing, Just "stack", Just "heap", Just "const"]
      results <- forM strategies $ \allocFlag -> do
        let dir = "/tmp/once_alloc_test_" ++ maybe "default" id allocFlag
        createDirectoryIfMissing True dir

        let onceSource = case allocFlag of
              Nothing -> helloOnceNoAlloc
              Just strat -> helloOnceWithAlloc strat
        TIO.writeFile (dir ++ "/hello.once") onceSource

        let allocArg = maybe [] (\s -> ["--alloc", s]) allocFlag
        (compilerCode, _, compilerErr) <- runOnce $
          ["build", "--exe", "--interp", "../lib/Interpretations/Linux"] ++ allocArg ++ [dir ++ "/hello.once", "-o", dir ++ "/hello"]

        case compilerCode of
          ExitFailure _ -> do
            cleanupDir dir
            return $ Left $ "Compiler failed for " ++ show allocFlag ++ ": " ++ compilerErr
          ExitSuccess -> do
            (gccCode, _, gccErr) <- readProcessWithExitCode "gcc"
              ["-o", dir ++ "/hello", dir ++ "/hello.c"] ""
            case gccCode of
              ExitFailure _ -> do
                cleanupDir dir
                return $ Left $ "GCC failed for " ++ show allocFlag ++ ": " ++ gccErr
              ExitSuccess -> do
                (runCode, stdout, runErr) <- readProcessWithExitCode (dir ++ "/hello") [] ""
                cleanupDir dir
                case runCode of
                  ExitFailure _ -> return $ Left $ "Run failed for " ++ show allocFlag ++ ": " ++ runErr
                  ExitSuccess -> return $ Right stdout

      case sequence results of
        Left err -> assertFailure err
        Right outputs -> do
          let expected = "Hello for Once\n"
          assertBool "all outputs match expected" $ all (== expected) outputs
          assertBool "all outputs identical" $ case outputs of
            [] -> True
            (x:xs) -> all (== x) xs

  , testCase "function allocation annotation overrides --alloc flag" $ do
      let dir = "/tmp/once_alloc_override_test"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hello.once") (helloOnceWithAlloc "stack")

      (compilerCode, _, compilerErr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", "--alloc", "heap", dir ++ "/hello.once", "-o", dir ++ "/hello"]

      case compilerCode of
        ExitFailure _ -> do
          cleanupDir dir
          assertFailure $ "Compiler failed: " ++ compilerErr
        ExitSuccess -> do
          source <- TIO.readFile (dir ++ "/hello.c")
          assertBool "uses stack allocation (compound literal)" $ T.isInfixOf "(char[])" source
          cleanupDir dir

  , testCase "strategies produce different codegen" $ do
      let dir = "/tmp/once_alloc_codegen_test"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hello.once") helloOnceNoAlloc

      -- Generate with const
      (code1, _, _) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", "--alloc", "const", dir ++ "/hello.once", "-o", dir ++ "/const"]
      constCode <- case code1 of
        ExitSuccess -> TIO.readFile (dir ++ "/const.c")
        _ -> return ""

      -- Generate with stack
      (code2, _, _) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", "--alloc", "stack", dir ++ "/hello.once", "-o", dir ++ "/stack"]
      stackCode <- case code2 of
        ExitSuccess -> TIO.readFile (dir ++ "/stack.c")
        _ -> return ""

      cleanupDir dir

      -- Stack should use compound literal (char[])
      assertBool "stack uses compound literal" $ T.isInfixOf "(char[])" stackCode
      -- Const should NOT use compound literal
      assertBool "const does not use compound literal" $ not (T.isInfixOf "(char[])" constCode)

  , testCase "heap allocation uses once_heap_string" $ do
      let dir = "/tmp/once_heap_codegen_test"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hello.once") (helloOnceWithAlloc "heap")

      -- Generate with heap
      (exitCode, _, _) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hello.once", "-o", dir ++ "/heap"]

      case exitCode of
        ExitFailure _ -> do
          cleanupDir dir
          assertFailure "Compiler failed"
        ExitSuccess -> do
          heapCode <- TIO.readFile (dir ++ "/heap.c")
          cleanupDir dir
          -- Heap should use once_heap_string from MallocLike interface
          assertBool "heap uses once_heap_string" $ T.isInfixOf "once_heap_string" heapCode
          -- Heap should NOT use static literal
          assertBool "heap does not use static literal for string" $
            not (T.isInfixOf "once_puts((OnceString){ .data = \"Hello for Once\"" heapCode)

  , testCase "heap allocation compiles and runs correctly" $ do
      let dir = "/tmp/once_heap_run_test"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hello.once") (helloOnceWithAlloc "heap")

      -- Build
      (compilerCode, _, compilerErr) <- runOnce
        ["build", "--exe", "--interp", "../lib/Interpretations/Linux", dir ++ "/hello.once", "-o", dir ++ "/hello"]

      case compilerCode of
        ExitFailure _ -> do
          cleanupDir dir
          assertFailure $ "Compiler failed: " ++ compilerErr
        ExitSuccess -> do
          -- Compile with gcc
          (gccCode, _, gccErr) <- readProcessWithExitCode "gcc"
            ["-o", dir ++ "/hello", dir ++ "/hello.c"] ""

          case gccCode of
            ExitFailure _ -> do
              cleanupDir dir
              assertFailure $ "GCC failed: " ++ gccErr
            ExitSuccess -> do
              -- Run
              (runCode, stdout, _) <- readProcessWithExitCode (dir ++ "/hello") [] ""
              cleanupDir dir
              assertEqual "exit code" ExitSuccess runCode
              assertEqual "output" "Hello for Once\n" stdout
  ]
