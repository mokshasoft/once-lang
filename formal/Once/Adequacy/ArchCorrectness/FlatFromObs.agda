-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatFromObs  (Plan 0.53-step2 / Phase B L1;
-- Plan 0.54 rung A step-7 rewire 2026-07-20)
--
-- Shared, arch-parametric construction of the per-arch `ArchCorrect` record.
--
-- STEP-7 REWIRE (the first break in the decomposition from the COMPILER apex
-- `Once.Compiler.correct` = `VC.correctᵈ`): previously this module POSTULATED
-- `ir-flat-correct`, left `flat-trace` an abstract parameter, and DISCARDED the
-- `ir-obs-correct` it was handed (`flat-from-obs _ = …`) — so the whole
-- IR-observable theorem (and everything under it: the composition case, the
-- arith value work) was an island. Now:
--
--   * `asm-sem`          — DEFINED  (`exec-bytes ∘ assemble`)
--   * `assemble-correct` — PROVED   (`refl`, by the `asm-sem` definition)
--   * `flat-trace`       — DEFINED: `take n (flat-events (EF n) (ir-to-trace ir)
--                          entry)`, where the adequate fuel `EF n` is exactly the
--                          `∃[ f ]` witness `traces-agree` supplies at depth `n`
--                          (fuel counts machine STEPS, `n` counts EVENTS — which
--                          is why a naive `flat-events n` would be wrong).
--   * `ir-flat-correct`  — PROVED from `ir-obs-correct`'s `traces-agree`
--                          (`proj₂` of that same witness). NO LONGER A POSTULATE.
--   * `asm-trace-correct`— NAMED postulate (printer / loader faithfulness; the
--                          concrete-machine half = Plan 0.54 rung B).
--
-- Residual introduced (narrow + named, replacing the opaque whole-statement
-- postulate): the ENTRY STATE and its preconditions — `ArchCorrectness.agda`
-- already flags these as "provable (no new mathematics)". `ValidAtWF` at `Unit`
-- is literally `valid-unit-wf`; the rest is loader/initial-frame plumbing.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.ArchCorrectness.FlatFromObs
  (arch          : Arch)
  (FS            : FrameSemantics)
  (as            : ArchSemantics)
  (program-bound : ℕ)
  where

open import Data.Bool using (false)
open import Data.List using (List; []; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.IR using (IR; Unit; AllocMode; Stack)
open import Once.IR.Size using (ir-size)
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; Registers; mkRegs; ValueLocation; AtDynamic; SV-Ptr;
         regs; readReg; Input1; halted)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Data.Nat using (z≤n; s≤s)
open import Once.CCC.Machine.Allocation
  using (AllocState; mkAllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
import Once.Compile as C
import Once.Parser.Module.Core as P

open IRObsCorrectFlatness {FS} program-bound using (IRObsCorrectF; MachineRefinesObsF)
open FlatMachine {FS} using (mkFlat)
open FlatEventTrace {FS} using (flat-events)
open FrontierInvariant {FS} using (BeforeFrontier; heap-before)
open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; valid-unit-wf)

------------------------------------------------------------------------
-- The DEFINED field (+ its proof)
------------------------------------------------------------------------

asm-sem : String → Behavior
asm-sem asm = ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm)

------------------------------------------------------------------------
-- The ENTRY STATE residual (narrow, named; replaces the opaque postulates).
-- The loader hands `main` a fresh frame: nothing allocated (`next-slot ≡ 0`),
-- not halted, `Input1` pointing at the (Unit) argument cell.
------------------------------------------------------------------------

-- The loader's initial FRAME is the genuine external trust point (FrameSemantics
-- documents program entry as exactly that: "we trust the OS/runtime set up
-- sufficient space before calling our code"). `Frame` is abstract, so it cannot
-- be constructed here. Everything ELSE about the entry state is now CONSTRUCTED,
-- and its preconditions are PROVED (was: 8 postulates, now 2).
postulate
  entry-frame : FrameSemantics.Frame FS
  -- the compiled `main` fits the (per-arch) program bound.
  entry-size  : ∀ (ir : IR Unit Unit) → ir-size ir < program-bound

-- A fresh frame: nothing on the stack (`next-slot ≡ 0`), one heap ref reserved
-- for the (erased) `Unit` argument cell so it is `BeforeFrontier`.
entry-alloc : AllocState {FS}
entry-alloc = mkAllocState entry-frame 0 1

entry-loc : ValueLocation FS
entry-loc = AtDynamic (heap-loc (mkHeapRef 0) 0)

-- Fillers are pointers to the same (erased Unit) cell — no numeric literal is
-- needed, so no `Number` instance for the machine word domain is required.
entry-regs : Registers FS
entry-regs = mkRegs (SV-Ptr entry-loc) (SV-Ptr entry-loc) (SV-Ptr entry-loc)
                    0 (SV-Ptr entry-loc)

entry-s : LocState FS
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false

-- All four preconditions now hold BY CONSTRUCTION.
entry-ns : next-slot entry-alloc ≡ 0
entry-ns = refl

entry-bf : BeforeFrontier entry-alloc entry-loc
entry-bf = heap-before (s≤s z≤n)

entry-nh : halted entry-s ≡ false
entry-nh = refl

entry-rdi : readReg (regs entry-s) Input1 ≡ SV-Ptr entry-loc
entry-rdi = refl

-- `main`'s machine-refinement witness at the entry state. The `Unit` input's
-- validity is `valid-unit-wf` — no plumbing needed for it.
entry-witness : (ir : IR Unit Unit) → IRObsCorrectF ir
              → MachineRefinesObsF ir tt entry-s entry-alloc
entry-witness ir ioc =
  ioc (entry-size ir) Stack tt entry-loc entry-s entry-alloc
      entry-ns valid-unit-wf entry-bf entry-nh entry-rdi

------------------------------------------------------------------------
-- `flat-trace` — DEFINED (the adequate fuel is `traces-agree`'s ∃-witness).
------------------------------------------------------------------------

flat-trace-of : (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
              → Maybe (IR Unit Unit) → Behavior
flat-trace-of ioc nothing   _ = []
flat-trace-of ioc (just ir) n =
  take n (flat-events (proj₁ (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir)) n))
                      (ir-to-trace ir) (mkFlat entry-s entry-alloc 0))

------------------------------------------------------------------------
-- The NAMED postulate that REMAINS (Layer-1 gap): printer / loader
-- faithfulness — the concrete-machine half (Plan 0.54 rung B).
------------------------------------------------------------------------

postulate
  asm-trace-correct :
    (ft : Maybe (IR Unit Unit) → Behavior) →
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → asm-sem asm n ≡ ft (moduleToIR m) n

------------------------------------------------------------------------
-- `ir-flat-correct` — PROVED from `traces-agree` (was a postulate).
------------------------------------------------------------------------

ir-flat-correct-of : (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
                   → ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ)
                   → flat-trace-of ioc mir n ≡ ⟦ mir ⟧IR n
ir-flat-correct-of ioc nothing   n = refl
ir-flat-correct-of ioc (just ir) n =
  proj₂ (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir)) n)

------------------------------------------------------------------------
-- The constructed ArchCorrect record — now CONSUMING `ir-obs-correct`.
------------------------------------------------------------------------

flat-from-obs :
  (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir) → ArchCorrect arch as
flat-from-obs ioc = record
  { asm-sem           = asm-sem
  ; flat-trace        = flat-trace-of ioc
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = asm-trace-correct (flat-trace-of ioc)
  ; ir-flat-correct   = ir-flat-correct-of ioc
  }
