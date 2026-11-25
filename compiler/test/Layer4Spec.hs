-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 4 codegen tests — user-defined functions, closures, currying,
-- captures, higher-order, and closures as data payloads.
--
-- Plan 0.53: runs on every backend arch (x86_64 native, x86_32 / riscv64
-- under qemu) via the shared multi-arch `valueCases` helper.
--
-- Run with: cabal test --test-option='-p "/Layer4/"'

module Layer4Spec (layer4Tests) where

import Test.Tasty

import Backend.Common (valueCases)

layer4Tests :: TestTree
layer4Tests = testGroup "Layer4"
  [ -- Inline morphism-realm primitives (pre-Plan 0.19 baseline)
    valueCases "id inline (emits 42)"                            "layer4-direct-id"         42
  , valueCases "id compose chain inline (emits 42)"              "layer4-id-compose-chain"  42
    -- Morphism aliases (resolveExpr substitution)
  , valueCases "named morphism alias myid=id (emits 42)"         "layer4-named-id"          42
  , valueCases "named morphism alias mysnd=snd (emits 42)"       "layer4-named-snd"         42
  , valueCases "alias of alias (g=f=id) (emits 42)"              "layer4-alias-of-alias"    42
  , valueCases "user fn defined as compose chain (emits 42)"     "layer4-composed-alias"    42
    -- User-defined curried fns with captures
  , valueCases "curried keepFst x y = x, applied (42,99) (emits 42)" "layer4-keep-fst"      42
  , valueCases "capture fidelity: keepFst 99 42 returns 99"     "layer4-keep-fst-99"       99
  , valueCases "curried keepSnd x y = y (emits 42)"              "layer4-keep-snd"          42
  , valueCases "3-arg curried mid3 a b c = b (emits 42)"         "layer4-3args-mid"         42
  , valueCases "partial application: partial = keepFst 42 (emits 42)" "layer4-partial-app"  42
    -- Higher-order
  , valueCases "fn as arg: apply1 id 42 (emits 42)"              "layer4-fn-as-arg"         42
  , valueCases "fn returns fn: getId 99 42 (emits 42)"           "layer4-fn-returns-fn"     42
  , valueCases "twice id 42 (emits 42)"                          "layer4-twice"             42
    -- Layer 1 + Layer 4 (user fns over pairs)
  , valueCases "user swap p = (snd p, fst p) (emits 42)"         "layer4-user-swap"         42
  , valueCases "swap (swap (42,99)) round-trip (emits 42)"       "layer4-swap-twice"        42
  , valueCases "user fn returns pair, project (emits 42)"        "layer4-mkpair"            42
    -- Layer 2 + Layer 4
  , valueCases "user fn destructs sum (emits 42)"                "layer4-sum-and-fn"        42
  , valueCases "user fn returns sum, destruct at call site (emits 42)" "layer4-mksum"       42
    -- Closure-as-data-payload (CCT1 inside CCTB / CCT2)
  , valueCases "closure as sum payload: pickFn (inl forty2) (emits 42)"    "layer4-closure-in-sum"  42
  , valueCases "closure as pair component: applyFst (forty2, 99) (emits 42)" "layer4-closure-in-pair" 42
  ]
