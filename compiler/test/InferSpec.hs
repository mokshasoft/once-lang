-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Signature-less inference, end to end (D072).
--
-- These programs declare definitions WITHOUT a type signature and rely on the
-- untrusted unification oracle plus the verified check to recover one. They
-- ran only in `tests/run-exit-tests.sh` until 2026-09-08, which meant they
-- were exercised on x86_64 alone, by hand, and never in `cabal test`. Ported
-- here so each runs on all three backends (x86_64 native, x86_32 / riscv64
-- under qemu) through the same `exitCases` helper as everything else.
module InferSpec (inferTests) where

import Test.Tasty

import Backend.Common (exitCases)

inferTests :: TestTree
inferTests = testGroup "Inference (no signature)"
  [ exitCases "identity, inferred (exit 0)"          "infer-id"            0
  , exitCases "lambda, inferred (exit 5)"            "infer-lambda"        5
  , exitCases "composition, inferred (exit 5)"       "infer-compose"       5
  , exitCases "composition chain, inferred (exit 7)" "infer-compose-chain" 7
  , exitCases "polymorphic alias, inferred (exit 9)" "infer-poly-alias"    9
  ]
