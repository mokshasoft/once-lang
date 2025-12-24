module Backend.X86.Spec (x86BackendTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

-- Note: TIO, createDirectoryIfMissing, ExitCode, readProcessWithExitCode
-- are used by executableTests below

import Once.Backend.Native (compileFullToX86)
import Once.IR (IR (..))
import Once.Type (Type (..))

import Backend.Common

-- | All x86 backend tests
x86BackendTests :: TestTree
x86BackendTests = testGroup "X86"
  [ codegenTests
  , assemblyTests
  , executableTests
  ]

-- | Tests for x86 code generation from IR
codegenTests :: TestTree
codegenTests = testGroup "codegen"
  [ testGroup "id function"
      [ testCase "id generates mov rax, rdi" $ do
          let idIR = Id tA
              asm = compileFullToX86 idIR
          assertBool "moves input to output" $ T.isInfixOf "movq %rdi, %rax" asm
      ]

  , testGroup "projections"
      [ testCase "fst generates first element access" $ do
          let fstIR = Fst tA tB
              asm = compileFullToX86 fstIR
          assertBool "accesses first element" $ T.isInfixOf "(%rdi)" asm

      , testCase "snd generates second element access" $ do
          let sndIR = Snd tA tB
              asm = compileFullToX86 sndIR
          assertBool "accesses second element" $ T.isInfixOf "8(%rdi)" asm
      ]

  , testGroup "pair"
      [ testCase "pair allocates and stores both elements" $ do
          let pairIR = Pair (Snd tA tB) (Fst tA tB)
              asm = compileFullToX86 pairIR
          -- Pair should save callee-saved registers
          assertBool "saves r14" $ T.isInfixOf "pushq %r14" asm
          assertBool "saves r15" $ T.isInfixOf "pushq %r15" asm
          -- Pair should allocate stack space
          assertBool "allocates stack" $ T.isInfixOf "subq $16" asm
      ]

  , testGroup "composition"
      [ testCase "compose chains operations" $ do
          let compIR = Compose (Fst tA tB) (Id (TProduct tA tB))
              asm = compileFullToX86 compIR
          -- Should have fst access
          assertBool "has fst access" $ T.isInfixOf "(%rdi)" asm
      ]
  ]

-- | Tests for assembly syntax correctness
assemblyTests :: TestTree
assemblyTests = testGroup "assembly syntax"
  [ testCase "pair generates valid inline assembly" $ do
      let swapIR = Pair (Snd tA tB) (Fst tA tB)
          asm = compileFullToX86 swapIR
      -- Check it generates actual x86 instructions
      assertBool "has push instruction" $ T.isInfixOf "pushq" asm
      assertBool "has mov instruction" $ T.isInfixOf "movq" asm

  , testCase "fst generates valid inline assembly" $ do
      let fstIR = Fst tA tB
          asm = compileFullToX86 fstIR
      -- Should have memory access and mov
      assertBool "has mov instruction" $ T.isInfixOf "movq" asm
  ]

-- | Tests for executable generation
executableTests :: TestTree
executableTests = testGroup "executable"
  [ testCase "hi.once compiles and runs" $ do
      let dir = "/tmp/once_x86_exe_test"
      createDirectoryIfMissing True dir

      TIO.writeFile (dir ++ "/hi.once") hiOnce

      -- Compile with x86 backend
      (compileCode, _, compileErr) <- runOnce
        ["build", "--exe", "--target", "x86_64",
         "-I:x86_64", "I.Linux.Syscalls",
         "--strata", "../Strata",
         dir ++ "/hi.once", "-o", dir ++ "/hi"]

      case compileCode of
        ExitFailure _ -> assertFailure $ "once build failed: " ++ compileErr
        ExitSuccess -> do
          (runCode, _, _) <- readProcessWithExitCode (dir ++ "/hi") [] ""
          assertEqual "exit code is 0" ExitSuccess runCode

  , testCase "swap function compiles to working executable" $ do
      let dir = "/tmp/once_x86_swap_test"
      createDirectoryIfMissing True dir

      -- Create a simple test that uses swap
      let testOnce = T.unlines
            [ "primitive exit0 : Eff Unit Unit"
            , ""
            , "swap : (Int * Int) -> (Int * Int)"
            , "swap = pair snd fst"
            , ""
            , "main : IO Unit"
            , "main = exit0"
            ]

      TIO.writeFile (dir ++ "/test.once") testOnce

      -- Compile with x86 backend
      (compileCode, _, compileErr) <- runOnce
        ["build", "--exe", "--target", "x86_64",
         "-I:x86_64", "I.Linux.Syscalls",
         "--strata", "../Strata",
         dir ++ "/test.once", "-o", dir ++ "/test"]

      case compileCode of
        ExitFailure _ -> assertFailure $ "once build failed: " ++ compileErr
        ExitSuccess -> do
          (runCode, _, _) <- readProcessWithExitCode (dir ++ "/test") [] ""
          assertEqual "exit code is 0" ExitSuccess runCode
  ]
