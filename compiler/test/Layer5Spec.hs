-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Layer 5 codegen tests: structured recursion — catamorphisms AND, since
-- D189-D195, anamorphisms.
--
-- Compiles `.once` programs that use `cata` over a μ-type, or `ana`/`Out` over
-- a ν-type, to executables and verifies the exit code. Plan 0.53: each runs on every backend arch
-- (x86_64 native, x86_32 / riscv64 under qemu) via the shared `exitCases`.
--
-- Run with: cabal test --test-option='-p "/Layer5/"'

module Layer5Spec (layer5Tests) where

import Test.Tasty

import Backend.Common (exitCases)

layer5Tests :: TestTree
layer5Tests = testGroup "Layer5"
  [ exitCases "cata isEven of an even Nat (exit 42)" "layer5-iseven" 42
  , testGroup "cata-general (Plan 0.36 Phase 0)"
      [ exitCases name name code | (name, code) <- cataGeneralCases ]
  , testGroup "cata-effectful (Plan 0.36)"
      -- Both effect-emitting catas build and run to their sentinel (exit 7).
      -- `emit@E` is a runtime nop in the shipped interpretation, so the exit
      -- code is the observable here; the emit trace itself is exercised by
      -- TraceSpec (against the observable test interpretation).
      [ exitCases name name 7 | name <- cataEffectfulCases ]
  , testGroup "ana/Out — the ν half (D189-D195)"
      -- The codata dual of the groups above, and the reason they exist here
      -- rather than only in `tests/run-exit-tests.sh`: THAT harness is x86_64
      -- only, and until now the ν codegen had never executed on x86_32 or
      -- riscv64. `exitCases` runs all three.
      --
      -- `nu-ana-build` builds a suspension and discards it — it covers the
      -- ten-instruction two-cell build and the coalgebra block. `nu-ana-force`
      -- FORCES a layer, which is the call through the ν's second cell, and is
      -- the half no proof in the tree discharges yet (`obs-correct-Out` is
      -- still a postulate). If the ν codegen regresses, this is what fails.
      [ exitCases "ana builds a suspension (exit 42)" "nu-ana-build" 42
      , exitCases "Out forces a layer (exit 42)"      "nu-ana-force" 42
      ]
  ]

-- | Plan 0.36 Phase-0 north-star matrix: one cata per polynomial-functor
-- shape (K/Id/+/*), each fold's value observed as the `exit` argument.
-- Shape #5 (leaf tree, two recursive positions) is the decisive non-Nat case.
cataGeneralCases :: [(String, Int)]
cataGeneralCases =
  [ ("layer5-cata-degenerate",      42)  -- #1 Mu (K Int), 0 rec positions
  , ("layer5-cata-nat",              3)  -- #2 Mu (K Unit + Id), 1 rec, bare Id
  , ("layer5-cata-list-sum",        42)  -- #3 Mu (K Unit + (K Int * Id))
  , ("layer5-cata-nelist-sum",      42)  -- #4 Mu (K Int + (K Int * Id))
  , ("layer5-cata-leaftree-sum",    42)  -- #5 Mu (K Int + (Id * Id))  <- decisive
  , ("layer5-cata-nodetree-sum",    42)  -- #6 Mu (K Unit + (Id * (K Int * Id)))
  , ("layer5-cata-ternarytree-sum", 42)  -- #7 Mu (K Int + (Id * Id * Id))
  , ("layer5-cata-multictor-size",   4)  -- #8 Mu (K Unit + (Id + (Id * Id)))
  , ("layer5-cata-nestedprod-sum",  42)  -- #9 Mu (K Unit + ((K Int * K Int) * Id))
  ]

-- | The two effect-emitting cata north-star fixtures (Plan 0.36). Both build
-- and run to the sentinel exit 7; the algebra invokes `emit@E` per emitting
-- layer (a runtime nop in the shipped interpretation).
cataEffectfulCases :: [String]
cataEffectfulCases =
  [ "layer5-cata-list-emit"      -- trace [emit 5, emit 3, exit 7]
  , "layer5-cata-leaftree-emit"  -- crown: trace [emit 40, emit 2, exit 7]
  ]
