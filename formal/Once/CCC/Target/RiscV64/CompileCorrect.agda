-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.CompileCorrect  (Plan 0.10)
--
-- Mirror of `Once.CCC.Target.X86-64.CompileCorrect` for RISC-V 64. The
-- semantic-side `ir-to-trace-correct` is shared via
-- `Once.CCC.Codegen.IRTraceCorrect`; this module only adds the
-- arch-specific `compile-trace-correct` (delegating to the per-arch
-- `Simulation.trace-sim`) and combines them in `compile-correct`.
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.CompileCorrect where

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
  using (LocState; ValueLocation; halted; regs; readReg; Input;
         AbstractTrace)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Target.RiscV64.Syntax using (Program)

module Correctness {FS : FrameSemantics} (program-bound : ℕ) where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace)
  open import Once.CCC.Target.RiscV64.DirectSimulation using (module Simulation)
  open Simulation {FS} using (RV64State; Corresponds; exec-prog; trace-sim)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- Shared, arch-agnostic IR-side correctness (Phase E lives here).
  open import Once.CCC.Codegen.IRTraceCorrect using (module IRTraceCorrectness)
  open IRTraceCorrectness {FS} program-bound using (ir-to-trace-correct)

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)

  compile-trace-correct :
    ∀ (trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (rs : RV64State) →
    Corresponds s rs alloc →
    let abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-rs = exec-prog (compile-trace trace) rs (current-frame alloc)
    in Corresponds abs-final-s arch-final-rs abs-final-alloc
  compile-trace-correct trace s alloc rs corr =
    trace-sim trace s rs alloc corr

  compile-correct :
    ∀ {A B} (ir : IR A B)
      (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (rs : RV64State) →
    Corresponds s rs alloc →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    let trace = ir-to-trace ir
        abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-rs = exec-prog (compile-trace trace) rs (current-frame alloc)
    in Corresponds abs-final-s arch-final-rs abs-final-alloc
       ×
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut abs-final-alloc (eval ir x) result-loc abs-final-s)
  compile-correct ir mIn x input-loc s alloc rs
                  corr valid before not-halted rdi-eq =
    let semantic-side =
          ir-to-trace-correct ir mIn x input-loc s alloc
            valid before not-halted rdi-eq
        machine-side =
          compile-trace-correct (ir-to-trace ir) s alloc rs corr
    in machine-side , semantic-side
