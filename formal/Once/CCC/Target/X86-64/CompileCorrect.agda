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
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR using (IR; AllocMode)
open import Once.CCC.Eval using (eval)

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; halted; regs; readReg; Input1;
         AbstractTrace)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Target.X86-64.Syntax using (Program)

------------------------------------------------------------------------
-- The theorem framework is parameterized by FrameSemantics, like the
-- verified-path Correctness module is.
------------------------------------------------------------------------

module Correctness {FS : FrameSemantics} (program-bound : ℕ) where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
  open import Once.CCC.Target.X86-64.DirectSimulation using (module Simulation)
  open Simulation {FS} using (X86State; Corresponds; exec-prog; trace-sim)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- Shared, arch-agnostic IR-side correctness (Phase E lives here).
  open import Once.CCC.Codegen.IRTraceCorrect using (module IRTraceCorrectness)
  open IRTraceCorrectness {FS} program-bound using (ir-to-trace-correct)

  ----------------------------------------------------------------------
  -- The extracted compile = compile-trace ∘ ir-to-trace.
  ----------------------------------------------------------------------

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)

  ----------------------------------------------------------------------
  -- compile-trace-correct: the arch-side half. Discharged via
  -- `Simulation.trace-sim` (Phase D).
  --
  -- Residual trusted base inside `trace-sim`: the SigOp codegen↔abstract
  -- correspondence is now a NAMED postulate
  -- `Simulation.sigop-codegen-faithful : ∀ name → ...` rather than an
  -- anonymous `PO.!!`. Per-(arch, sigop) discharge is now possible by
  -- splitting this into `sigop-codegen-faithful-exit`,
  -- `sigop-codegen-faithful-lit-int`, etc., each tied to a stronger
  -- abstract semantics for that name. See `docs/compiler/trusted-base.md`.
  ----------------------------------------------------------------------

  compile-trace-correct :
    ∀ (trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) →
    Corresponds s xs alloc →
    let abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs (current-frame alloc)
    in Corresponds abs-final-s arch-final-xs abs-final-alloc
  compile-trace-correct trace s alloc xs corr =
    trace-sim trace s xs alloc corr

  ----------------------------------------------------------------------
  -- THE GRAND THEOREM.
  --
  -- For every IR term, every input value, every initial X86State that
  -- corresponds to an abstract LocState representing the input,
  -- executing `compile ir` on the X86 machine produces an X86State that
  -- corresponds to an abstract LocState representing `eval ir x`.
  ----------------------------------------------------------------------

  compile-correct :
    ∀ {A B} (ir : IR A B)
      (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) →
    Corresponds s xs alloc →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    let trace = ir-to-trace ir
        abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs (current-frame alloc)
    in Corresponds abs-final-s arch-final-xs abs-final-alloc
       ×
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut abs-final-alloc (eval ir x) result-loc abs-final-s)
  compile-correct ir mIn x input-loc s alloc xs
                  corr valid before not-halted rdi-eq =
    let semantic-side =
          ir-to-trace-correct ir mIn x input-loc s alloc
            valid before not-halted rdi-eq
        machine-side =
          compile-trace-correct (ir-to-trace ir) s alloc xs corr
    in machine-side , semantic-side
