-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrectFlat — observable correctness over the
-- FLAT machine (Plan 0.36, corrected machine side).
--
-- `MachineRefinesObsF` is the flat-machine instance of the Plan 0.36
-- encoding: a program's only observable is its SigOp trace, so
-- trace-correctness (`traces-agree`) is the headline obligation and
-- value-correctness (`ValidAtWF`) is a FIELD (`value-realized`).
--
-- D200: this file is now the ASSEMBLY only. It was 4358 lines, and a genuine
-- recheck cost 728 s / 2.2 GB — a price paid on every iteration of the ten
-- postulates still open in it. The per-constructor clauses live in
-- `Once.CCC.Codegen.IRObsCorrect.*` and are re-exported here, so every
-- importer of this module sees exactly what it saw before.
--
-- What made the split safe: `ir-obs-correct` below is the ONLY recursive
-- definition in the development. Its two recursive cases
-- (`comp-obs-correct`, `cata-correct`) take the induction hypothesis as an
-- ARGUMENT rather than calling back, so no clause depends on any other — they
-- depend only on `Interface` (the obligation) and `Machine` (the step
-- lemmas). That is why the parts form a star and not a chain.
--
--   Prelude    the import block, re-exported
--   Interface  `IRObsCorrectF` and everything its statement mentions
--   Machine    the step/memory lemmas + the straight-line setup skeletons
--   Simple     id, terminal, initial, free-heap, fst, snd, out-μ, const
--              (+ the postulates still open: In, pair, case, Para, in-ν,
--               Hylo, Fuse)
--   SigOp      the SigOp clause
--   Sum        inl, inr
--   TwoCell    curry, Ana (the shared ten-instruction build)
--   Apply      apply
--   Out        Out  (D199)
--   Comp       g ∘ f
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrectFlat (o : CanonicalName) where

-- The shared vocabulary comes in ONCE, publicly: `Machine` re-exports
-- `Interface`, which re-exports `Prelude`. The parts import it WITHOUT
-- `public` — seven public re-exports of the same prelude is seven paths to
-- `Data.Nat._+_`, which Agda rejects as a clashing definition.
open import Once.CCC.Codegen.IRObsCorrect.Machine o public

open import Once.CCC.Codegen.IRObsCorrect.Simple  o
open import Once.CCC.Codegen.IRObsCorrect.SigOp   o
open import Once.CCC.Codegen.IRObsCorrect.Sum     o
open import Once.CCC.Codegen.IRObsCorrect.TwoCell o
open import Once.CCC.Codegen.IRObsCorrect.Apply   o
open import Once.CCC.Codegen.IRObsCorrect.Out     o
open import Once.CCC.Codegen.IRObsCorrect.Comp    o

-- The name every importer uses. Each part re-exports `Core`/`Mach`, so the
-- surface here is what the single file's `IRObsCorrectFlatness` had.
module IRObsCorrectFlatness {FS : FrameSemantics} (program-bound : ℕ) where

  open Core     {FS} program-bound public
  open Mach     {FS} program-bound public
  open Simp     {FS} program-bound public
  open SigOpC   {FS} program-bound public
  open SumC     {FS} program-bound public
  open TwoCellC {FS} program-bound public
  open ApplyC   {FS} program-bound public
  open OutC     {FS} program-bound public
  open CompC    {FS} program-bound public

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).
  ir-obs-correct : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
  -- category structure
  ir-obs-correct id                  = obs-correct-id
  ir-obs-correct (g ∘ f)             = comp-obs-correct (ir-obs-correct g) (ir-obs-correct f)
  -- products
  ir-obs-correct ⟨ f , g ⟩         = obs-correct-pair f g
  ir-obs-correct fst                 = obs-correct-fst
  ir-obs-correct snd                 = obs-correct-snd
  -- sums
  ir-obs-correct inl                 = obs-correct-inl
  ir-obs-correct inr                 = obs-correct-inr
  ir-obs-correct (case f g)          = obs-correct-case f g
  -- terminal / initial
  ir-obs-correct terminal            = obs-correct-terminal
  ir-obs-correct initial             = obs-correct-initial
  -- exponentials — THE LABEL-BEARING PAIR
  ir-obs-correct (curry body)      = obs-correct-curry body
  ir-obs-correct apply               = obs-correct-apply
  -- μ / ν structure
  ir-obs-correct (In wf)           = obs-correct-In wf
  ir-obs-correct (out-μ wf)          = obs-correct-out-μ wf
  ir-obs-correct (Cata wf alg)       = cata-correct wf alg (ir-obs-correct alg)
  ir-obs-correct (Para wf f)         = obs-correct-Para wf f
  ir-obs-correct (Out wf)            = obs-correct-Out wf
  ir-obs-correct (in-ν wf)         = obs-correct-in-ν wf
  ir-obs-correct (Ana wf f)          = obs-correct-Ana wf f
  ir-obs-correct (Hylo wfF wfG a nt) = obs-correct-Hylo wfF wfG a nt
  ir-obs-correct (Fuse wfF wfG a nt) = obs-correct-Fuse wfF wfG a nt
  -- misc
  ir-obs-correct (free-heap r)       = obs-correct-free-heap r
  ir-obs-correct (const fit v)       = obs-correct-const fit v
  ir-obs-correct (SigOp si)          = obs-correct-sigop si

