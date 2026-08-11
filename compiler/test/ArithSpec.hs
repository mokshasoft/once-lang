-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Arithmetic block lowering tests.
--
-- After Plan 0.20 arith expressions compile to a single
-- `once_arith.block.<digest>` SigOp the backend emits as a subroutine.
-- Plan 0.53: each runs on every backend arch (x86_64 native, x86_32 /
-- riscv64 under qemu) via the shared `exitCases` helper.
--
-- Run with: cabal test --test-option='-p "/Arith/"'

module ArithSpec (arithTests) where

import Test.Tasty

import Backend.Common (exitCases)

arithTests :: TestTree
arithTests = testGroup "Arith"
  [ exitCases "3 + 5 * 2 = 13 (arith block lowering)" "arith-simple"   13
  , exitCases "f x = x + 3*5 - 2*x; f 5 = 10"         "arith-lambda-1" 10
  , exitCases "g x y = x + 2*y; g 4 19 = 42"          "arith-lambda-2" 42
  ]
