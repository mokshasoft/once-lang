module BackendSpec (backendTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (removeDirectoryRecursive, createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

import Once.Backend.C (generateC, CModule (..))
import Once.IR (IR (..))
import Once.Type (Type (..))

-- Helper types
tA, tB :: Type
tA = TVar "A"
tB = TVar "B"

backendTests :: TestTree
backendTests = testGroup "Backend.C"
  [ testGroup "swap.once"
      [ testCase "generates correct header" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header _ = generateC "swap" swapTy swapIR
          -- Check header contains necessary parts
          assertBool "has include guard" $ T.isInfixOf "ONCE_SWAP_H" header
          assertBool "has OncePair typedef" $ T.isInfixOf "typedef struct" header
          assertBool "has function decl" $ T.isInfixOf "once_swap" header

      , testCase "generates correct source" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule _ source = generateC "swap" swapTy swapIR
          -- Check source contains the swap implementation
          assertBool "has include" $ T.isInfixOf "#include" source
          assertBool "has function def" $ T.isInfixOf "once_swap" source
          assertBool "swaps fst and snd" $ T.isInfixOf "x.snd" source && T.isInfixOf "x.fst" source

      , testCase "no duplicate typedefs" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header _ = generateC "swap" swapTy swapIR
          -- Count occurrences of typedef
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
              -- fst ∘ id = fst
              ir = Compose (Fst tA tB) (Id (TProduct tA tB))
              CModule _ source = generateC "comp" ty ir
          assertBool "has fst access" $ T.isInfixOf ".fst" source
      ]

  , testGroup "gcc compilation"
      [ testCase "generated swap.c compiles with gcc" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header source = generateC "swap" swapTy swapIR
              dir = "/tmp/once_test_syntax"

          -- Create temp directory and write files
          createDirectoryIfMissing True dir
          TIO.writeFile (dir ++ "/once_swap.h") header
          TIO.writeFile (dir ++ "/once_swap.c") source

          -- Compile with gcc (just check syntax, don't link)
          (exitCode, _, stderr) <- readProcessWithExitCode "gcc"
            ["-c", "-fsyntax-only", dir ++ "/once_swap.c"] ""

          -- Clean up
          removeDirectoryRecursive dir

          case exitCode of
            ExitSuccess -> pure ()
            ExitFailure _ -> assertFailure $ "gcc failed: " ++ stderr

      , testCase "generated swap runs correctly" $ do
          let swapTy = TArrow (TProduct tA tB) (TProduct tB tA)
              swapIR = Pair (Snd tA tB) (Fst tA tB)
              CModule header source = generateC "swap" swapTy swapIR
              dir = "/tmp/once_test_run"

          -- Create temp directory and write files
          createDirectoryIfMissing True dir
          TIO.writeFile (dir ++ "/once_swap.h") header
          TIO.writeFile (dir ++ "/once_swap.c") source
          TIO.writeFile (dir ++ "/test_swap.c") testMain

          -- Compile and run
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

  , testGroup "executable mode"
      [ testCase "hi.once compiles to executable" $ do
          let dir = "/tmp/once_test_exe"
          createDirectoryIfMissing True dir

          -- Write hi.once
          TIO.writeFile (dir ++ "/hi.once") hiOnce

          -- Run the compiler via subprocess (once build --exe)
          (exitCode, _, stderr) <- readProcessWithExitCode "stack"
            ["exec", "--", "once", "build", "--exe", dir ++ "/hi.once", "-o", dir ++ "/hi"] ""

          case exitCode of
            ExitFailure _ -> do
              removeDirectoryRecursive dir
              assertFailure $ "once build failed: " ++ stderr
            ExitSuccess -> do
              -- Check file was generated
              source <- TIO.readFile (dir ++ "/hi.c")
              assertBool "has stdlib include" $ T.isInfixOf "#include <stdlib.h>" source
              assertBool "has exit0 implementation" $ T.isInfixOf "exit(0)" source
              assertBool "has main function" $ T.isInfixOf "int main(void)" source
              assertBool "calls once_main" $ T.isInfixOf "once_main" source
              removeDirectoryRecursive dir

      , testCase "hi.once executable runs and exits 0" $ do
          let dir = "/tmp/once_test_exe_run"
          createDirectoryIfMissing True dir

          -- Write hi.once
          TIO.writeFile (dir ++ "/hi.once") hiOnce

          -- Run the compiler via subprocess
          (compilerCode, _, compilerErr) <- readProcessWithExitCode "stack"
            ["exec", "--", "once", "build", "--exe", dir ++ "/hi.once", "-o", dir ++ "/hi"] ""

          case compilerCode of
            ExitFailure _ -> do
              removeDirectoryRecursive dir
              assertFailure $ "once build failed: " ++ compilerErr
            ExitSuccess -> do
              -- Compile with gcc
              (compileCode, _, compileErr) <- readProcessWithExitCode "gcc"
                ["-o", dir ++ "/hi", dir ++ "/hi.c"] ""

              case compileCode of
                ExitFailure _ -> do
                  removeDirectoryRecursive dir
                  assertFailure $ "gcc compile failed: " ++ compileErr
                ExitSuccess -> do
                  -- Run the executable
                  (runCode, _, _) <- readProcessWithExitCode (dir ++ "/hi") [] ""
                  removeDirectoryRecursive dir
                  assertEqual "exit code is 0" ExitSuccess runCode

      , testCase "primitives generate correct C declarations" $ do
          let dir = "/tmp/once_test_prim"
          createDirectoryIfMissing True dir

          -- Write hi.once
          TIO.writeFile (dir ++ "/hi.once") hiOnce

          -- Run the compiler via subprocess
          (exitCode, _, stderr) <- readProcessWithExitCode "stack"
            ["exec", "--", "once", "build", "--exe", dir ++ "/hi.once", "-o", dir ++ "/hi"] ""

          case exitCode of
            ExitFailure _ -> do
              removeDirectoryRecursive dir
              assertFailure $ "once build failed: " ++ stderr
            ExitSuccess -> do
              source <- TIO.readFile (dir ++ "/hi.c")

              -- Check primitive is implemented correctly
              assertBool "exit0 takes void* parameter" $ T.isInfixOf "exit0(void* x)" source
              assertBool "exit0 suppresses unused warning" $ T.isInfixOf "(void)x" source
              assertBool "exit0 calls exit(0)" $ T.isInfixOf "exit(0)" source

              removeDirectoryRecursive dir
      ]
  ]
  where
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

    hiOnce :: T.Text
    hiOnce = T.unlines
      [ "-- hi.once: The simplest Once executable"
      , "primitive exit0 : Unit -> Unit"
      , ""
      , "main : Unit -> Unit"
      , "main = exit0"
      ]
