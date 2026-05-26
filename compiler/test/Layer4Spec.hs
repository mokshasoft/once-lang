-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

-- | Layer 4 codegen tests — Exponentials: curry / apply / closures.
--
-- Layer 4 adds first-class function values: user-defined top-level
-- functions, curried fns with captures, higher-order fns. Built on
-- top of Layers 0-3.
--
-- Pre-Plan 0.19 only the morphism-realm subset worked (`exit (id 42)`
-- and compose chains of CCC primitives). User-defined fn references
-- routed through `Surface.sigOp` with the elaborator's curry-wrap
-- assuming asm-direct arrow ABI; user-defined fns compile as
-- Unit-curry-returning-closure routines, so the apply chain forwarded
-- the returned closure ptr through `once_exit`, exiting with its low
-- byte (e.g. 80 / 216).
--
-- Plan 0.19 split Surface.sigOp into:
--   - `sigOp`   — external primitive (asm-direct arrow ABI, used for
--                 syscalls via `signature foo : …`)
--   - `closure` — user-defined entry (asm Unit→Closure ABI)
-- The resolver rewrites `Surface.sigOp x → Surface.closure x` when `x`
-- is in the user-fn list; closure elaborates as `SigOp ∘ terminal`
-- (no curry-wrap), so call sites work via standard apply chains.
-- Eliminated 1 inline postulate (`sigOp-arrow-eta` in
-- Once.Surface.Correct).
--
-- All Layer 4 tests use `--alloc heap` because the heap-only-pivot
-- branch focuses on heap allocation; the closure ABI for stack mode
-- is a separate concern.
--
-- Run with: cabal test --test-option='-p "/Layer4/"'

module Layer4Spec (layer4Tests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Backend.Common (runOnce, cleanupDir)

layer4Tests :: TestTree
layer4Tests = testGroup "Layer4"
  [ -- Inline morphism-realm primitives (pre-Plan 0.19 baseline)
    testCase "id inline (exit 42)" $
      buildAndRun "layer4-direct-id" 42 >>= either assertFailure return
  , testCase "id compose chain inline (exit 42)" $
      buildAndRun "layer4-id-compose-chain" 42 >>= either assertFailure return

    -- Morphism aliases (resolveExpr substitution)
  , testCase "named morphism alias myid=id (exit 42)" $
      buildAndRun "layer4-named-id" 42 >>= either assertFailure return
  , testCase "named morphism alias mysnd=snd (exit 42)" $
      buildAndRun "layer4-named-snd" 42 >>= either assertFailure return
  , testCase "alias of alias (g=f=id) (exit 42)" $
      buildAndRun "layer4-alias-of-alias" 42 >>= either assertFailure return
  , testCase "user fn defined as compose chain (exit 42)" $
      buildAndRun "layer4-composed-alias" 42 >>= either assertFailure return

    -- User-defined curried fns with captures
  , testCase "curried keepFst x y = x, applied (42,99) (exit 42)" $
      buildAndRun "layer4-keep-fst" 42 >>= either assertFailure return
  , testCase "capture fidelity: keepFst 99 42 returns 99" $
      buildAndRun "layer4-keep-fst-99" 99 >>= either assertFailure return
  , testCase "curried keepSnd x y = y (exit 42)" $
      buildAndRun "layer4-keep-snd" 42 >>= either assertFailure return
  , testCase "3-arg curried mid3 a b c = b (exit 42)" $
      buildAndRun "layer4-3args-mid" 42 >>= either assertFailure return
  , testCase "partial application: partial = keepFst 42 (exit 42)" $
      buildAndRun "layer4-partial-app" 42 >>= either assertFailure return

    -- Higher-order
  , testCase "fn as arg: apply1 id 42 (exit 42)" $
      buildAndRun "layer4-fn-as-arg" 42 >>= either assertFailure return
  , testCase "fn returns fn: getId 99 42 (exit 42)" $
      buildAndRun "layer4-fn-returns-fn" 42 >>= either assertFailure return
  , testCase "twice id 42 (exit 42)" $
      buildAndRun "layer4-twice" 42 >>= either assertFailure return

    -- Layer 1 + Layer 4 (user fns over pairs)
  , testCase "user swap p = (snd p, fst p) (exit 42)" $
      buildAndRun "layer4-user-swap" 42 >>= either assertFailure return
  , testCase "swap (swap (42,99)) round-trip (exit 42)" $
      buildAndRun "layer4-swap-twice" 42 >>= either assertFailure return
  , testCase "user fn returns pair, project (exit 42)" $
      buildAndRun "layer4-mkpair" 42 >>= either assertFailure return

    -- Layer 2 + Layer 4
  , testCase "user fn destructs sum (exit 42)" $
      buildAndRun "layer4-sum-and-fn" 42 >>= either assertFailure return
  , testCase "user fn returns sum, destruct at call site (exit 42)" $
      buildAndRun "layer4-mksum" 42 >>= either assertFailure return

    -- Closure-as-data-payload (CCT1 inside CCTB / CCT2)
  , testCase "closure as sum payload: pickFn (inl forty2) (exit 42)" $
      buildAndRun "layer4-closure-in-sum" 42 >>= either assertFailure return
  , testCase "closure as pair component: applyFst (forty2, 99) (exit 42)" $
      buildAndRun "layer4-closure-in-pair" 42 >>= either assertFailure return
  ]

------------------------------------------------------------------------
-- Test Helpers (mirrors Layer1Spec/Layer2Spec, with --alloc heap)
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
     "--alloc", "heap",
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
