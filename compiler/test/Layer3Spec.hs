-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 3 codegen tests — nested combinations of Layer 1 (products)
-- and Layer 2 (sums): pairs containing sums, sums containing pairs,
-- deeper nestings.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `valueCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer3/"'

module Layer3Spec (layer3Tests) where

import Test.Tasty

import Backend.Common (valueCases)

layer3Tests :: TestTree
layer3Tests = testGroup "Layer3"
  [ valueCases "pair nested inside a sum (emits 42)"     "layer3-pair-in-sum" 42
  , valueCases "sum nested inside a pair (emits 42)"     "layer3-sum-in-pair" 42
  , valueCases "nested-mix: pair / sum / pair (emits 42)" "layer3-nested-mix" 42
  ]
