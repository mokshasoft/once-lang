-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 1 codegen tests — Products: ⟨_,_⟩, fst, snd
--
-- Tests that compile to executables and verify output via exit codes.
-- Layer 1 adds pair construction and projection on top of Layer 0.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `exitCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer1/"'

module Layer1Spec (layer1Tests) where

import Test.Tasty

import Backend.Common (exitCases)

layer1Tests :: TestTree
layer1Tests = testGroup "Layer1"
  [ exitCases "fst projects first component (exit 42)"    "layer1-fst"         42
  , exitCases "deeply-nested snd (exit 42)"               "layer1-snd-deep"    42
  , exitCases "compose chain of snd morphisms (exit 42)"  "layer1-compose-snd" 42
  ]
