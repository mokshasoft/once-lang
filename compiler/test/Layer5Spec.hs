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

import Backend.Common (exitCases, traceCases)

layer5Tests :: TestTree
layer5Tests = testGroup "Layer5"
  [ exitCases "cata isEven of an even Nat (exit 42)" "layer5-iseven" 42
  , testGroup "cata-general (Plan 0.36 Phase 0)"
      [ exitCases name name code | (name, code) <- cataGeneralCases ]
  , traceCases "apply eliminates an eff closure — capture (D222 A′)"
               "apply-eff-closure" [5] 7
  , traceCases "apply eliminates an eff closure — argument (D222 A′)"
               "apply-eff-closure-snd" [9] 7
  , traceCases "pair arm order — TWO emitting arms (D222)"
               "pair-arm-order-emit" [1, 2] 7
  , testGroup "cata-effectful (Plan 0.36)"
      -- D220/D221: these assert the TRACE, not the exit code. They used to use
      -- `exitCases`, which links the production `Strata/` NOP `emit` and can
      -- only see `exit@S 7` — so both tests passed while emitting nothing, and
      -- the crown case's assembly was byte-identical to a bare `main = exit@S 7`.
      -- `traceCases` builds against the BYTE-WRITING interpretation and checks
      -- the ordered emit arguments, which is the actual observable (D058).
      [ traceCases name name emitted 7 | (name, emitted) <- cataEffectfulCases ]
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
      -- D199: the first ν test with a RECURSIVE POSITION. The two above use
      -- `Nu (K Int)`, where a forced layer has nothing to re-suspend, so they
      -- pass whether or not `Out` re-suspends. This one forces twice, through
      -- the recursive slot, and segfaulted before the re-suspension pass.
      , exitCases "forcing twice through Id (exit 42)" "nu-ana-deep"  42
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

-- | The two effect-emitting cata north-star fixtures (Plan 0.36), with the
-- TRACE each must emit. The algebra invokes `emit@E` once per emitting layer.
--
-- The leaftree case is the only one that can see the fold's ORDER: one
-- recursive position cannot order anything, so the list emits [5, 3] whichever
-- way the fold runs. `seqF (G ⊗ H)` specifies LEFT-first, so the crown case is
-- [40, 2] — and it was [2, 40] until D221.
cataEffectfulCases :: [(String, [Integer])]
cataEffectfulCases =
  [ ("layer5-cata-list-emit",     [5, 3])
  , ("layer5-cata-leaftree-emit", [40, 2])   -- crown: LEFT leaf first
  ]
