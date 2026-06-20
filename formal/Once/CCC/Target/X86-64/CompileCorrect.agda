-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CompileCorrect  (Plan 0.10)
--
-- THE GRAND THEOREM about the X86-64-EXTRACTED compiler.
--
-- Plan 0.10 closes the verification gap by making the extracted compile
-- *be* the verified compile:
--
--     compile = compile-trace ∘ ir-to-trace
--
-- The chain has two halves:
--
--   semantic-side  ir-to-trace-correct   — IR-side, FS-only, ARCH-AGNOSTIC
--                                          shared in Once.CCC.Codegen.IRTraceCorrect
--                                          (Phase E discharges per-IR)
--
--   machine-side   compile-trace-correct — arch-side, uses Simulation.trace-sim
--                                          (Phase D, this module)
--
-- The arch-side is short: it just delegates to `Simulation.trace-sim`.
-- All the Phase E per-IR work lives in the shared module so
-- X86-32/RiscV64 inherit every discharge automatically.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.CompileCorrect where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR using (IR; AllocMode)
open import Once.IR.Size using (ir-size)
open import Once.CCC.Eval using (eval)
import Once.CCC.Machine.Dispatcher as DispatcherModule

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; StoredValue; SV-Ptr; halted; regs; readReg; Input1;
         AbstractTrace)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame; next-slot)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace; ir-to-trace-at-frontier)
open import Once.CCC.Target.X86-64.Syntax using (Program)

------------------------------------------------------------------------
-- The theorem framework is parameterized by FrameSemantics, like the
-- verified-path Correctness module is.
------------------------------------------------------------------------

module Correctness {FS : FrameSemantics} (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS} program-bound)
  where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- Shared, arch-agnostic IR-side correctness (Phase E lives here).
  open import Once.CCC.Codegen.IRTraceCorrect using (module IRTraceCorrectness)
  open IRTraceCorrectness {FS} program-bound acc-pb sigOp-proof using (ir-to-trace-correct)

  ----------------------------------------------------------------------
  -- The extracted compile = compile-trace ∘ ir-to-trace.
  ----------------------------------------------------------------------

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)


  ----------------------------------------------------------------------
  -- Plan 0.32 (a): the extracted CORRECTNESS theorem moved to the flat
  -- machine — see `Once.CCC.Target.X86-64.CompileCorrectFlat`
  -- (`compile-correct-flat`). It replaces the old DirectSimulation-based
  -- `compile-trace-correct`/`compile-correct` (loop-blind, now deleted)
  -- with `FlatSim.flat-sim` over the REAL x86 `Semantics.exec`.
  ----------------------------------------------------------------------
