-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 0 codegen tests
--
-- Tests that compile to executables and verify output via exit codes.
-- Uses only Layer 0 constructs: id, composition, primitives.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `exitCases` helper.

module Layer0Spec (layer0Tests) where

import Test.Tasty

import Backend.Common (exitCases)

layer0Tests :: TestTree
layer0Tests = testGroup "Layer0"
  [ exitCases "id returns input (exit 42)"              "layer0-id"       42
  , exitCases "composition of ids (exit 42)"            "layer0-compose"  42
  , exitCases "constant function (exit 7)"              "layer0-neg"      7
  , exitCases "terminal collapses Int to Unit (exit 42)" "layer0-terminal" 42
  ]
