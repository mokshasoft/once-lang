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
--              (+ the postulates still open: In, case, Para, in-ν,
--               Hylo, Fuse)
--   SigOp      the SigOp clause
--   Sum        inl, inr
--   TwoCell    curry, Ana (the shared ten-instruction build)
--   Apply      apply
--   Out        Out  (D199)
--   Comp       g ∘ f
--   Pair       ⟨ f , g ⟩'s four clusters (run, place, preservation, trace)
--   PairAssemble  …and the clause that wires them (D211)
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv; Linked)
import Once.Denotation.TraceMonad as TM
import Once.CCC.FrameSemantics
module Once.CCC.Codegen.IRObsCorrectFlat (o : CanonicalName) (tbl : DL.List IRFun) where

-- The shared vocabulary comes in ONCE, publicly: `Machine` re-exports
-- `Interface`, which re-exports `Prelude`. The parts import it WITHOUT
-- `public` — seven public re-exports of the same prelude is seven paths to
-- `Data.Nat._+_`, which Agda rejects as a clashing definition.
open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl public

open import Once.CCC.Codegen.IRObsCorrect.Simple  o tbl
open import Once.CCC.Codegen.IRObsCorrect.SigOp   o tbl
open import Once.CCC.Codegen.IRObsCorrect.Sum     o tbl
open import Once.CCC.Codegen.IRObsCorrect.TwoCell o tbl
open import Once.CCC.Codegen.IRObsCorrect.Apply   o tbl
open import Once.CCC.Codegen.IRObsCorrect.Out     o tbl
open import Once.CCC.Codegen.IRObsCorrect.Comp    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Case    o tbl
open import Once.CCC.Codegen.IRObsCorrect.Call    o tbl
-- `PairAssemble` imports `Pair` (the four clusters) itself, WITHOUT `public`
-- — same D200 rule: only this façade re-exports.
open import Once.CCC.Codegen.IRObsCorrect.Pair o tbl

-- The name every importer uses. Each part re-exports `Core`/`Mach`, so the
-- surface here is what the single file's `IRObsCorrectFlatness` had.
module IRObsCorrectFlatness {FS : FrameSemantics} where

  open Core     {FS} public
  open Mach     {FS} public
  open Simp     {FS} public
  open SigOpC   {FS} public
  open SumC     {FS} public
  open TwoCellC {FS} public
  open ApplyC   {FS} public
  open OutC     {FS} public
  open CompC    {FS} public
  open CaseC    {FS} public
  open PairAsm  {FS} public
  open CallC    {FS} public

  -- TOTAL, and now with NO CATCH-ALL (Plan 0.68 step 0). Every constructor has
  -- its own clause and its own named obligation, in `Once.IR`'s order — so a
  -- constructor that is added, removed or renamed is a TYPE ERROR here rather
  -- than a silent variable pattern absorbing it (the retired-ctor trap).
  -- plan 0.105: linked against the signatures the machine's interpretation
  -- declares, so every FFI SigOp in `ir` is declared there.
  ir-obs-correct : ∀ {A B} (ir : IR A B) → Linked (TM.sig (Once.CCC.FrameSemantics.fs-interp FS)) tbl ir → IRObsCorrectF ir
  -- category structure
  ir-obs-correct id                  _ = obs-correct-id
  ir-obs-correct (g ∘ f)             (lg , lf) = comp-obs-correct (ir-obs-correct g lg) (ir-obs-correct f lf)
  -- products
  ir-obs-correct ⟨ f , g ⟩         (lf , lg) = obs-correct-pair-proof (ir-obs-correct f lf) (ir-obs-correct g lg)
  ir-obs-correct fst                 _ = obs-correct-fst
  ir-obs-correct snd                 _ = obs-correct-snd
  -- sums
  ir-obs-correct inl                 _ = obs-correct-inl
  ir-obs-correct inr                 _ = obs-correct-inr
  ir-obs-correct (case f g)          (lf , lg) = obs-correct-case (ir-obs-correct f lf) (ir-obs-correct g lg)
  -- terminal / initial
  ir-obs-correct terminal            _ = obs-correct-terminal
  ir-obs-correct initial             _ = obs-correct-initial
  -- exponentials — THE LABEL-BEARING PAIR
  ir-obs-correct (curry body)        _ = obs-correct-curry body
  ir-obs-correct apply               _ = obs-correct-apply
  -- μ / ν structure
  ir-obs-correct (In wf)             _ = obs-correct-In wf
  ir-obs-correct (out-μ wf)          _ = obs-correct-out-μ wf
  ir-obs-correct (Cata wf alg)       la = cata-correct wf alg (ir-obs-correct alg la)
  ir-obs-correct (Out wf)            _ = obs-correct-Out wf
  ir-obs-correct (in-ν wf)           _ = obs-correct-in-ν wf
  ir-obs-correct (Ana wf f)          _ = obs-correct-Ana wf f
  -- misc
  ir-obs-correct (const fit v)       _ = obs-correct-const fit v
  ir-obs-correct (SigOp si)          d = obs-correct-sigop si d
  -- D245: a direct call of a LINKED table entry.
  ir-obs-correct (Call f)            lk = obs-correct-call f lk
