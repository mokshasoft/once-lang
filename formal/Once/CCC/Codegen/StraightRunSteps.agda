-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.StraightRunSteps  (Plan 0.58 Phase 2)
--
-- Machine-side building blocks for `obs-correct-compose`: running a
-- STRAIGHT trace segment as a prefix of a larger program produces a
-- `FlatSteps` chain, so `flat-events-steps` can split the composite
-- program's events into the sub-IRs' events.
--
-- This module is built bottom-up (each lemma green + committed) so the
-- big `IRObsCorrectFlat` surgery only ever assembles finished pieces.
------------------------------------------------------------------------

module Once.CCC.Codegen.StraightRunSteps where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module _ {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch)

  -- Prefix fetch (dual of `FlatStepLemmas.fetch-++`, which reads the
  -- SUFFIX at offset `length xs + j`): reading position `j` of `xs ++ ys`
  -- with `j` inside `xs` sees only `xs`. This is why running the `f`
  -- portion of `trace(f) ++ mov ∷ trace(g)` (pc `0 .. |f|-1`) fetches the
  -- SAME instructions as running `trace(f)` standalone.
  fetch-prefix : ∀ (xs ys : AbstractTrace) (j : ℕ)
               → j < length xs → fetch (xs ++ ys) j ≡ fetch xs j
  fetch-prefix []       ys j       ()
  fetch-prefix (i ∷ xs) ys zero    _        = refl
  fetch-prefix (i ∷ xs) ys (suc j) (s≤s lt) = fetch-prefix xs ys j lt
