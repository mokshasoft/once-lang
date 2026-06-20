-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CompileCorrectFlat
--
-- Plan 0.32 (a): the extracted grand theorem over the FLAT machine —
-- the replacement for the DirectSimulation-based `CompileCorrect`. For a
-- Cata-free IR, executing `compile-trace (ir-to-trace ir)` on the REAL
-- x86 CPU (`Semantics.exec`) corresponds to the flat abstract machine's
-- run, AND the flat final state witnesses `ValidAtWF` for `eval ir x`.
--
--   compile-correct-flat :
--     CompiledCorr (ir-to-trace ir) (mkFlat s alloc 0) xs →  -- entry corr
--     … (the IR/validity preconditions) … → StraightIR ir →
--       (∃ m s'. X.exec m (compile ir) xs ≡ just s'
--              × CompiledCorr (ir-to-trace ir) EF s')          -- machine, flat-sim
--     × (∃ mOut loc. ValidAtWF mOut (falloc EF) (eval ir x) loc -- semantic, lifted
--                              (forced (floc EF)))
--
-- MACHINE side  = `FlatSim.flat-sim` (the loop-running plus-simulation).
-- SEMANTIC side = `IRTraceCorrect.ir-to-trace-correct` (over `exec-trace`)
--   transported onto `exec-flat` by `FlatSemanticLift.lift-validAtWF-flat`
--   through the `exec-trace-is-flat` bridge, justified by
--   `StraightTrace.straight-ir-to-trace` (only `Cata` is non-straight).
--
-- DESIGN NOTES
-- * `enc-hl` (the heap-address encoding) stays ABSTRACT — a parameter, as
--   in FlatSimulation. A concrete layout belongs to the (currently
--   unwired) allocator (Plan 0.35); this theorem holds for any valid one.
-- * The semantic side is Cata-free (`StraightIR ir`): `exec-trace` is
--   loop-blind, so `Cata` semantics "go fully flat" separately. The
--   MACHINE side runs the loop for ALL IRs.
-- * `flat-sim`'s three inputs are CLEARLY-PROVABLE named postulates here
--   (Plan 0.32 minimal swap path), replacing DirectSimulation.trace-sim's
--   VACUOUS loop-blind holes — a strict trusted-base improvement. Their
--   per-instruction discharge (block-step lemmas) is done for the cata
--   instructions; alloc-heap (0.35 M6) / stack-ops / closure-sigop-const /
--   jump-resolution remain mechanical.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Target.X86-64.Syntax using (slot-size; Program)
open import Data.Nat using (ℕ; suc; _<_; _+_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.CCC.Machine.Dispatcher as DispatcherModule

module Once.CCC.Target.X86-64.CompileCorrectFlat
  (FS : FrameSemantics)
  (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS} program-bound)
  (enc-hl : HeapLocation → ℕ)
  (enc-hl-inj : ∀ {a b : HeapLocation} → enc-hl a ≡ enc-hl b → a ≡ b)
  (enc-hl-suc : ∀ (hl : HeapLocation) → enc-hl (sucHL hl) ≡ enc-hl hl + slot-size)
  where

open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (subst)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR using (IR; AllocMode)
open import Once.IR.Size using (ir-size)
open import Once.CCC.Eval using (eval)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; StoredValue; SV-Ptr; halted; regs; readReg; Input1;
         AbstractTrace; AllocState; module AbstractExec)
open AbstractExec {FS} using (exec-trace)
open import Once.CCC.Machine.Allocation using (next-slot; module FrontierInvariant)
open FrontierInvariant {FS} using (BeforeFrontier)

open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace; ir-to-trace-at-frontier)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)

open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

open import Once.CCC.Codegen.StraightTrace using (StraightIR; straight-ir-to-trace)
open import Once.CCC.Codegen.FlatSemanticLift using (lift-validAtWF-flat)
open import Once.CCC.Target.X86-64.FlatSim FS enc-hl enc-hl-inj enc-hl-suc
  using (FlatSimGoal; BlockStepAll; FlatNoHalt; EndCorr; flat-sim)
open import Once.CCC.Target.X86-64.FlatSimulation FS enc-hl enc-hl-inj enc-hl-suc
  using (CompiledCorr)

open import Once.CCC.Codegen.IRTraceCorrect using (module IRTraceCorrectness)
open IRTraceCorrectness {FS} program-bound acc-pb sigOp-proof using (ir-to-trace-correct)

------------------------------------------------------------------------
-- flat-sim's clearly-provable inputs (see header). Named so the trusted
-- base is explicit; discharge is the per-instruction block-step layer.
------------------------------------------------------------------------
postulate
  block-step-all : ∀ (prog : AbstractTrace) → BlockStepAll prog
  flat-no-halt   : ∀ (prog : AbstractTrace) → FlatNoHalt prog
  end-corr       : ∀ (prog : AbstractTrace) → EndCorr prog

-- flat-sim specialised to a program with the inputs supplied.
flat-sim-closed : ∀ (prog : AbstractTrace) (fuel : ℕ) (fs : FlatState) (s : X.State)
  → CompiledCorr prog fs s → FlatSimGoal prog fs fuel s
flat-sim-closed prog = flat-sim prog (block-step-all prog) (flat-no-halt prog) (end-corr prog)

------------------------------------------------------------------------
-- The extracted compile (= compile-trace ∘ ir-to-trace) and the theorem.
------------------------------------------------------------------------
compile : ∀ {A B} → IR A B → Program
compile ir = compile-trace (ir-to-trace ir)

compile-correct-flat : ∀ {A B} (ir : IR A B)
  → ir-size ir < program-bound
  → (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) (xs : X.State)
  → next-slot alloc ≡ 0
  → CompiledCorr (ir-to-trace ir) (mkFlat s alloc 0) xs
  → ValidAtWF mIn alloc x input-loc s
  → BeforeFrontier alloc input-loc
  → halted s ≡ false
  → readReg (regs s) Input1 ≡ SV-Ptr input-loc
  → StraightIR ir
  → let trace = ir-to-trace ir
        EF    = exec-flat (suc (length trace)) trace (mkFlat s alloc 0)
    in (∃[ m ] ∃[ s' ] (X.exec m (compile-trace trace) xs ≡ just s'
                     × CompiledCorr trace EF s'))
       ×
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut (falloc EF) (eval ir x) result-loc (forced (floc EF)))
compile-correct-flat ir ir<bound mIn x input-loc s alloc xs
                     ns≡0 cc-entry valid before not-halted rdi-eq straight =
  machine-side , semantic-flat
  where
    trace = ir-to-trace ir

    machine-side : _
    machine-side =
      flat-sim-closed trace (suc (length trace)) (mkFlat s alloc 0) xs cc-entry

    -- semantic over exec-trace, with frontier specialised to 0 via ns≡0
    semantic-tr : _
    semantic-tr =
      subst (λ n →
          ∃[ mOut ] ∃[ result-loc ]
            ValidAtWF mOut (proj₂ (exec-trace (ir-to-trace-at-frontier n ir) s alloc))
              (eval ir x) result-loc
              (proj₁ (exec-trace (ir-to-trace-at-frontier n ir) s alloc)))
        ns≡0
        (ir-to-trace-correct ir ir<bound mIn x input-loc s alloc valid before not-halted rdi-eq)

    semantic-flat : ∃[ mOut ] ∃[ result-loc ]
      ValidAtWF mOut (falloc (exec-flat (suc (length trace)) trace (mkFlat s alloc 0)))
        (eval ir x) result-loc
        (forced (floc (exec-flat (suc (length trace)) trace (mkFlat s alloc 0))))
    semantic-flat =
      let mOut , result-loc , v = semantic-tr
      in mOut , result-loc ,
         lift-validAtWF-flat program-bound trace s alloc
           (straight-ir-to-trace ir straight) v
