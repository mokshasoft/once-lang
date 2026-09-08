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
    -- Ported from tests/run-exit-tests.sh (2026-09-08). These ran only in the
    -- shell scripts, so they were exercised on x86_64 alone and only when the
    -- scripts were run by hand; `exitCases` runs each on all three backends.
  , testGroup "division and modulo"
      [ exitCases "17 / 3 = 5"                          "arith-div-1"     5
      , exitCases "8-bit signed division, negative"     "arith-div8-neg"  253
      , exitCases "division by a literal zero"          "arith-div-zero"  255
      , exitCases "division by a zero computed at run time"
                                                        "arith-div-zero-runtime" 255
      , exitCases "17 % 3 = 2"                          "arith-mod-1"     2
      , exitCases "modulo by a literal zero"            "arith-mod-zero"  7
      , exitCases "modulo by a zero computed at run time"
                                                        "arith-mod-zero-runtime" 7
      , exitCases "8-bit multiply"                      "arith-mul8"      48
      ]
  ]
