-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 2 codegen tests — Sums: inl, inr, destruct
--
-- Layer 2 adds sum construction (inl/inr) and elimination (destruct)
-- on top of Layer 1: inl/inr build (tag, payload) pairs; destruct
-- dispatches on the tag at offset 0 (case-on-tag codegen).
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `exitCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer2/"'

module Layer2Spec (layer2Tests) where

import Test.Tasty

import Backend.Common (exitCases)

layer2Tests :: TestTree
layer2Tests = testGroup "Layer2"
  [ exitCases "destruct on inl selects Left branch (exit 42)"   "layer2-case-inl-direct" 42
  , exitCases "destruct on inr selects Right branch (exit 99)"  "layer2-case-inr-direct" 99
  , exitCases "initial typechecks/links as Void -> A (exit 42)" "layer2-initial"         42
  ]
