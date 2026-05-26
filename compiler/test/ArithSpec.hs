-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Arithmetic codegen tests.
--
-- Arithmetic is conceptually orthogonal to the categorical tower
-- (CCTB / CCT1 / CCT2 / …). The current direction (per Plan 0.2.4.1,
-- D040's earlier "separate ArithIR" design superseded) is to model
-- each arithmetic op as a SigOp:
--
--   - SigOpInfos already exist in `formal/Once/Arith/SigOp/Builders.agda`
--     under names `arith.add.int`, `arith.mul.int`, `arith.neg.int`, …
--   - Each one is supposed to discharge the `PreservesCCC` 6-field
--     contract from `formal/Once/CCC/SigOp/Helper.agda` (frame-eq,
--     not-halted, prior-preserved, heap-monotone, slot-monotone,
--     no capacity damage). `formal/Once/Arith/SigOp/Proofs.agda`
--     (`ArithProofs` module) is where those proofs live.
--   - Once discharged, arith SigOps compose into the TargetProvider
--     via `_<|>_` like any other primitive, and the dispatcher emits
--     real code at every call site.
--
-- What's missing today:
--
--   - A pipeline step that rewrites surface `+`/`*`/`-`/… into
--     `SigOp arith.<op>.<type>` invocations (the "ArithCompiler"
--     transform the deferred Plan 0.2.4.2-arith-to-sigop was meant
--     to land — that plan was never written).
--   - Wiring of arith SigOps into the composed TargetProvider so
--     the dispatcher recognizes them.
--   - Either the runtime symbol the backend currently asks for
--     (`once_arith.<op>.<type>`) gets defined in Strata, or — more
--     in line with the SigOp-and-PreservesCCC direction — that
--     emission path is replaced by the SigOp dispatch.
--
-- The single test below uses an inverted assertion: it PASSES while
-- the link fails, and FAILS loudly the moment arithmetic starts
-- producing a runnable binary. When that happens, the plumbing is
-- in place — flip the assertion to a positive `exit 13` check.

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
  [ arithSimpleBrokenTest
  ]

-- | `3 + 5 * 2 = 13` — currently broken at link, captured here so the
-- moment it starts linking we get a loud signal to convert this to a
-- positive assertion.
--
-- The once driver writes link errors to stdout (not stderr) and the
-- shared `runOnce` helper only surfaces stderr to the caller, so the
-- captured `err` string is typically empty; we rely on the build's
-- non-zero exit code alone.
arithSimpleBrokenTest :: TestTree
arithSimpleBrokenTest =
  testCase "3 + 5 * 2 (inverted: passes while once_arith.* is missing)" $ do
    result <- buildAndRun "arith-simple" 13
    case result of
      Left _ -> return ()
      Right () -> assertFailure $
        "arith-simple now builds and exits 13 — once_arith.* must " ++
        "have landed. Please flip this test to a positive assertion " ++
        "(buildAndRun \"arith-simple\" 13 >>= either assertFailure return)."

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
