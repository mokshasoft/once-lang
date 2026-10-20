-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Definitions without a signature, end to end (D323).
--
-- A definition without a signature has the type its body SYNTHESIZES; the
-- definition alone decides it. These programs rely on that and run on all
-- three backends (x86_64 native, x86_32 / riscv64 under qemu). Bodies that
-- only check (a lambda, a bare polymorphic reference) need a signature; their
-- rejection is tested in `GeneratorSpec`.
module InferSpec (inferTests) where

import Test.Tasty

import Backend.Common (exitCases)

inferTests :: TestTree
inferTests = testGroup "No signature: the synthesized type (D323)"
  [ exitCases "a literal (exit 7)"                   "infer-literal"       7
  , exitCases "an applied generator (exit 7)"        "infer-applied"       7
  ]
