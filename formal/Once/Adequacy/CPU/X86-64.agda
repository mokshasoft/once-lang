-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CPU.X86-64 — X86-64 ArchSemantics instance
--
-- Wires `Once.CCC.Target.X86-64.Semantics` (clean step / exec / run
-- shape, restored from history) into the portable `ArchSemantics`
-- interface.
--
-- Concrete fields (no postulates, real ISA semantics):
--   - Program      = List Instr  (from Once.CCC.Target.X86-64.Syntax)
--   - State        = the existing record (regs, memory, flags, pc, halted)
--   - initialState = X86-64.Semantics.initState
--   - run          = X86-64.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `execInstr` against
--                    the Intel SDM.
--
-- Postulated bridges (will be discharged):
--   - observe  : Maybe State → Behavior   (waiting for `Behavior`)
--   - decode   : List Byte → Maybe Program (byte-encoding of Instr)
--
-- DirectSimulation remains the lower-level proof tool used to discharge
-- arch-specific lemmas about `run`.
------------------------------------------------------------------------

module Once.Adequacy.CPU.X86-64 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.String using (String)
open import Data.Nat using (ℕ)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-64.Semantics as X64
import Once.CCC.Target.X86-64.Syntax    as X64S

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- x86-64 machine (arith blocks dispatched, Pure ⇒ no event), instanced from
-- the arch-generic `Arith.Backend.RunTraceCore`. This DERIVES `run-trace` from
-- `X64.run`'s step semantics, replacing the old opaque observable postulate.
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg)
import Once.Arith.Backend.X86-64.RunTrace as RT

------------------------------------------------------------------------
-- run-trace-x86-64 — DERIVED (no longer an opaque observable postulate).
-- It is `RunTraceCore.run-trace` at the x86-64 telescope; its remaining
-- ingredients are the named gaps below — smaller and more honest than the
-- monolithic observable they replace:
--   * `val-x86-64`        — the concrete XInstr arith interpreter (step 4:
--                           the real per-XInstr semantics over `State`).
--   * `arith-env-x86-64`  — the arith-block table (which `once_arith.block.*`
--                           label ↦ which block), extracted from the program
--                           (step 4: derive from `prog`'s emitted blocks).
--   * `ev-x86-64`         — label→SigOp resolution: the honest boundary axiom.
--   * `step-budget-x86-64`— adequate fuel (event-count ↦ machine steps), the
--                           SAME honest gap `FlatFromObs.flat-trace` carries.
------------------------------------------------------------------------

postulate
  val-x86-64         : XInstr → X64.State → Reg → X64.Word
  step-budget-x86-64 : ℕ → ℕ
  ev-x86-64          : RT.EvExtractor val-x86-64
  arith-env-x86-64   : X64S.Program → RT.ArithEnv val-x86-64

run-trace-x86-64 : X64S.Program → X64.State → Behavior
run-trace-x86-64 prog s =
  RT.run-trace val-x86-64 step-budget-x86-64 ev-x86-64 (arith-env-x86-64 prog) prog s

postulate
  -- decode-x86-64 — POSTULATED. Concrete byte-encoder/decoder per the
  -- Intel SDM is significant work; left as a named gap for now.
  decode-x86-64 : List Byte → Maybe X64S.Program

  -- assemble-x86-64 — POSTULATED. GNU `as --target=x86-64` trust point;
  -- removed when the in-Agda assembler (B1) lands.
  assemble-x86-64 : String → List Byte

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X64S.Program
  ; State        = X64.State
  ; initialState = X64.initState
  ; run          = X64.run
  ; run-trace    = run-trace-x86-64
  ; decode       = decode-x86-64
  ; assemble     = assemble-x86-64
  }
