-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Arithmetic codegen tests.
--
-- Plan 0.20 Phase G landed the arith-to-block-SigOp pipeline:
--
--   - `Once.Arith.Machine.Recognise` walks the elaborator's CCC IR
--     output for maximal arith subtrees built from
--     `arith.{add,sub,mul,neg}.int` SigOps over integer literals and
--     input projections.
--   - `Once.Arith.Machine.Rewrite` replaces each recognised subtree
--     with a single `SigOp arith.block.<digest>` whose `SigOpInfo`
--     carries the recognised `MArithIR` body.
--   - `Once.Arith.Backend.X86.Emit` lowers each block's body to a
--     standalone `once_arith.block.<digest>` subroutine emitted
--     after the program text, complete with prologue/epilogue.
--
-- The test below was previously an inverted assertion that PASSED
-- while the link failed; it now does the positive `exit 13` check.

module ArithSpec (arithTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

arithTests :: TestTree
arithTests = testGroup "Arith"
  [ arithSimpleTest
  , arithLambda1Test
  , arithLambda2Test
  ]

-- | `3 + 5 * 2 = 13`. After Plan 0.20 Phase G this compiles to a
-- single `once_arith.block.<digest>` SigOp call that the backend
-- emits as a standalone subroutine. The driver's link step now
-- resolves cleanly and the binary exits with the arith result.
arithSimpleTest :: TestTree
arithSimpleTest =
  testCase "3 + 5 * 2 = 13 (arith block lowering)" $ do
    result <- buildAndRun "arith-simple" 13
    either assertFailure return result

-- | `f x = x + 3 * 5 - 2 * x; main = exit (f 5)`. Exercises a
-- single-arg arith lambda. The body has `x` at `InputPath = [Snd]`
-- (a one-hop dereference) so the codegen still emits a direct
-- `mov dst, 8(%rdi)`. For x = 5: 5 + 15 - 10 = 10.
arithLambda1Test :: TestTree
arithLambda1Test =
  testCase "f x = x + 3*5 - 2*x; f 5 = 10" $ do
    result <- buildAndRun "arith-lambda-1" 10
    either assertFailure return result

-- | `g x y = x + 2 * y; main = exit (g 4 19)`. Exercises a two-arg
-- curried lambda where the captured `x` sits at `InputPath =
-- [Fst, Snd]` — two hops through the curry env. The X86 path
-- walker uses `%rax` as the chained-load intermediate. For
-- (x, y) = (4, 19): 4 + 38 = 42.
arithLambda2Test :: TestTree
arithLambda2Test =
  testCase "g x y = x + 2*y; g 4 19 = 42" $ do
    result <- buildAndRun "arith-lambda-2" 42
    either assertFailure return result

------------------------------------------------------------------------
-- Test helpers (mirror Layer0Spec; default --alloc = heap via CLI)
------------------------------------------------------------------------

buildAndRun :: String -> Int -> IO (Either String ())
buildAndRun name expectedExitCode = do
  let testDir = "/tmp/once_" ++ name
      srcFile = "test/" ++ name ++ ".once"
      exeFile = testDir </> name

  createDirectoryIfMissing True testDir

  source <- TIO.readFile srcFile
  TIO.writeFile (testDir </> name ++ ".once") source

  (buildExit, _buildOut, buildErr) <- runOnce
    ["build", "--target", "x86_64", "--no-optimize", "--exe",
     testDir </> name ++ ".once", "-o", exeFile]

  case buildExit of
    ExitFailure _ -> do
      cleanupDir testDir
      return $ Left $ "Build failed: " ++ buildErr
    ExitSuccess -> do
      (runExit, _runOut, _runErr) <- readProcessWithExitCode exeFile [] ""

      cleanupDir testDir

      case runExit of
        ExitFailure code | code == expectedExitCode -> return $ Right ()
        ExitFailure code -> return $ Left $
          "Wrong exit code: expected " ++ show expectedExitCode ++
          " but got " ++ show code
        ExitSuccess -> return $ Left $
          "Expected exit code " ++ show expectedExitCode ++
          " but got 0 (success)"
