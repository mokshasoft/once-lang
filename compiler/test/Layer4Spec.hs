-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 4 codegen tests — user-defined functions, closures, currying,
-- captures, higher-order, and closures as data payloads.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `exitCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer4/"'

module Layer4Spec (layer4Tests) where

import Test.Tasty

import Backend.Common (exitCases)

layer4Tests :: TestTree
layer4Tests = testGroup "Layer4"
  [ -- Inline morphism-realm primitives (pre-Plan 0.19 baseline)
    exitCases "id inline (exit 42)"                            "layer4-direct-id"         42
  , exitCases "id compose chain inline (exit 42)"              "layer4-id-compose-chain"  42
    -- Morphism aliases (resolveExpr substitution)
  , exitCases "named morphism alias myid=id (exit 42)"         "layer4-named-id"          42
  , exitCases "named morphism alias mysnd=snd (exit 42)"       "layer4-named-snd"         42
  , exitCases "alias of alias (g=f=id) (exit 42)"              "layer4-alias-of-alias"    42
  , exitCases "user fn defined as compose chain (exit 42)"     "layer4-composed-alias"    42
    -- User-defined curried fns with captures
  , exitCases "curried keepFst x y = x, applied (42,99) (exit 42)" "layer4-keep-fst"      42
  , exitCases "capture fidelity: keepFst 99 42 returns 99"     "layer4-keep-fst-99"       99
  , exitCases "curried keepSnd x y = y (exit 42)"              "layer4-keep-snd"          42
  , exitCases "3-arg curried mid3 a b c = b (exit 42)"         "layer4-3args-mid"         42
  , exitCases "partial application: partial = keepFst 42 (exit 42)" "layer4-partial-app"  42
    -- Higher-order
  , exitCases "fn as arg: apply1 id 42 (exit 42)"              "layer4-fn-as-arg"         42
  , exitCases "fn returns fn: getId 99 42 (exit 42)"           "layer4-fn-returns-fn"     42
  , exitCases "twice id 42 (exit 42)"                          "layer4-twice"             42
    -- Layer 1 + Layer 4 (user fns over pairs)
  , exitCases "user swap p = (snd p, fst p) (exit 42)"         "layer4-user-swap"         42
  , exitCases "swap (swap (42,99)) round-trip (exit 42)"       "layer4-swap-twice"        42
  , exitCases "user fn returns pair, project (exit 42)"        "layer4-mkpair"            42
    -- Layer 2 + Layer 4
  , exitCases "user fn destructs sum (exit 42)"                "layer4-sum-and-fn"        42
  , exitCases "user fn returns sum, destruct at call site (exit 42)" "layer4-mksum"       42
    -- Closure-as-data-payload (CCT1 inside CCTB / CCT2)
  , exitCases "closure as sum payload: pickFn (inl forty2) (exit 42)"    "layer4-closure-in-sum"  42
  , exitCases "closure as pair component: applyFst (forty2, 99) (exit 42)" "layer4-closure-in-pair" 42
  ]
