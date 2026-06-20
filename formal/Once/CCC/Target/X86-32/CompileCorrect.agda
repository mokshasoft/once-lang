-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.CompileCorrect  (Plan 0.10)
--
-- Mirror of `Once.CCC.Target.X86-64.CompileCorrect` for x86-32. The
-- semantic-side `ir-to-trace-correct` is shared via
-- `Once.CCC.Codegen.IRTraceCorrect`; this module only adds the
-- arch-specific `compile-trace-correct` (delegating to the per-arch
-- `Simulation.trace-sim`) and combines them in `compile-correct`.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.CompileCorrect where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR using (IR; AllocMode)
open import Once.IR.Size using (ir-size)
open import Once.CCC.Eval using (eval)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (subst)
import Once.CCC.Machine.Dispatcher as DispatcherModule

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; StoredValue; SV-Ptr; halted; regs; readReg; Input1;
         AbstractTrace)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame; next-slot)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace; ir-to-trace-at-frontier)
open import Once.CCC.Target.X86-32.Syntax using (Program)

module Correctness {FS : FrameSemantics} (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS} program-bound)
  where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-trace)
  open import Once.CCC.Target.X86-32.DirectSimulation using (module Simulation)
  open Simulation {FS} using (X86State; Corresponds; exec-prog; trace-sim)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- Shared, arch-agnostic IR-side correctness (Phase E lives here).
  open import Once.CCC.Codegen.IRTraceCorrect using (module IRTraceCorrectness)
  open IRTraceCorrectness {FS} program-bound acc-pb sigOp-proof using (ir-to-trace-correct)

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)

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

  compile-correct :
    ∀ {A B} (ir : IR A B)
      (ir<bound : ir-size ir < program-bound)
      (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) →
    next-slot alloc ≡ 0 →
    Corresponds s xs alloc →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    let trace = ir-to-trace ir
        abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs (current-frame alloc)
    in Corresponds abs-final-s arch-final-xs abs-final-alloc
       ×
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut abs-final-alloc (eval ir x) result-loc abs-final-s)
  compile-correct ir ir<bound mIn x input-loc s alloc xs
                  ns≡0 corr valid before not-halted rdi-eq =
    let semantic-side =
          ir-to-trace-correct ir ir<bound mIn x input-loc s alloc
            valid before not-halted rdi-eq
        semantic-side' = subst (λ n →
            ∃[ mOut ] ∃[ result-loc ]
              ValidAtWF mOut (proj₂ (exec-trace
                (ir-to-trace-at-frontier n ir) s alloc))
                (eval ir x) result-loc
                (proj₁ (exec-trace
                  (ir-to-trace-at-frontier n ir) s alloc)))
          ns≡0 semantic-side
        machine-side =
          compile-trace-correct (ir-to-trace ir) s alloc xs corr
    in machine-side , semantic-side'
