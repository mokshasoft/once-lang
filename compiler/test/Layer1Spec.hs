-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 1 codegen tests — Products: ⟨_,_⟩, fst, snd
--
-- Tests that compile to executables and verify the value each emits.
-- Layer 1 adds pair construction and projection on top of Layer 0.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `valueCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer1/"'

module Layer1Spec (layer1Tests) where

import Test.Tasty

import Backend.Common (valueCases)

layer1Tests :: TestTree
layer1Tests = testGroup "Layer1"
  [ valueCases "fst projects first component (emits 42)"    "layer1-fst"         42
  , valueCases "deeply-nested snd (emits 42)"               "layer1-snd-deep"    42
  , valueCases "compose chain of snd morphisms (emits 42)"  "layer1-compose-snd" 42
  ]
