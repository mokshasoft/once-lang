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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatFromObs (o : CanonicalName)
  (arch          : Arch)
  (FS            : FrameSemantics)
  -- Plan 0.54 rung D: the loader's initial FRAME is supplied BY THE ARCH, not
  -- postulated here. It used to be `postulate entry-frame : Frame FS` — opaque,
  -- so nothing about it could ever be proven, which is exactly why the apex
  -- needed a SECOND postulate (`entry-frame-base`) to say where its base was.
  -- As a parameter the arch can hand over a CONSTRUCTED frame and that second
  -- postulate becomes `refl` (x86-64 does; see `…ArchCorrectness.X86-64`).
  (entry-frame   : FrameSemantics.Frame FS)
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
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; Registers; mkRegs; ValueLocation; AtDynamic; SV-Tag;
         halted)
open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)
open import Data.Nat using (z≤n; s≤s)
open import Once.CCC.Machine.Allocation
  using (AllocState; mkAllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's own precondition — the emitted local labels are
-- pairwise distinct. Consumed by `AsmTraceCorrect` below.
open import Once.Adequacy.LabelClash using (DistinctLabels)

open IRObsCorrectFlatness {FS} program-bound using (IRObsCorrectF; MachineRefinesObsF; in-unit)
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
-- not halted. `main`'s (erased) Unit argument has no residence (D074) —
-- every register starts as the tag filler `SV-Tag 0`.
------------------------------------------------------------------------

-- The loader's initial FRAME is the genuine external trust point (FrameSemantics
-- documents program entry as exactly that: "we trust the OS/runtime set up
-- sufficient space before calling our code"). `Frame` is abstract, so it cannot
-- be constructed here. Everything ELSE about the entry state is now CONSTRUCTED,
-- and its preconditions are PROVED (was: 8 postulates, now 2).
postulate
  -- the compiled `main` fits the (per-arch) program bound.
  entry-size  : ∀ (ir : IR Unit Unit) → ir-size ir < program-bound

-- A fresh frame: nothing on the stack (`next-slot ≡ 0`), one heap ref reserved
-- for the (erased) `Unit` argument cell so it is `BeforeFrontier`.
-- Plan 0.63: the entry allocator is now indexed by the frame the prologue
-- reserved, because the reserved slot count lives WITH the frame
-- (`frame-slots`) instead of in the register file.
entry-alloc : ℕ → AllocState {FS}
-- the entry allocator: one ref reserved for the erased Unit cell, and NO block
-- has a size yet (the entry heap is empty, so `block-size ≡ λ _ → 0` — which makes
-- the correspondence's in-bounds coverage vacuously true at entry)
entry-alloc slots = mkAllocState entry-frame [] slots 0 1 (λ _ → 0)

entry-loc : ValueLocation FS
entry-loc = AtDynamic (heap-loc (mkHeapRef 0) 0)

-- D074: EVERY filler is a TAG. `main`'s (erased) Unit argument has no
-- residence (`in-unit`), so nothing requires Input1 to be a pointer — and a
-- pointer filler into the sizeless block 0 is exactly what made the heap
-- in-bounds invariant FALSE at entry. `SV-Tag 0` encodes to 0 just as the
-- pointer filler did (`enc-sv (SV-Tag 0) = 0`), so `entry-corr` is unchanged;
-- with no pointer anywhere in the entry state the in-bounds invariant holds
-- vacuously at the start of the run. (Plan 0.54 D item 4 made `Scratch` and
-- `Count` tags for `FlatRegTagWF`'s entry case; this finishes the move.)
entry-regs : Registers FS
entry-regs = mkRegs (SV-Tag 0) (SV-Tag 0) (SV-Tag 0) (SV-Tag 0) (SV-Tag 0)

-- THE ENTRY STATE IS INDEXED BY THE FRAME THE PROLOGUE RESERVED (2026-07-30).
--
-- `frame-slots` — the runtime slot counter the correspondence uses to bound the live
-- stack window — is moved ONLY by `instr-alloc-stack` / `-dealloc-stack` /
-- `-push-frame`, and `ir-to-trace` emits NONE of them: the frame reservation is the
-- `subq $budget*8, %rsp` bracket the per-arch emitter wraps around the trace. So
-- with `frame-slots ≡ 0` at entry it is 0 for the WHOLE run, the correspondence's
-- `stack-eq` says nothing about any slot, and "the slot this instruction reads is
-- in frame" (`slot-read-in-frame`) is FALSE for every emitted program that touches
-- a slot — an assumption that cannot be discharged, only refuted.
--
-- Entering with the reservation already made is both faithful (the machine really
-- starts inside its frame) and what makes that residual DISCHARGEABLE: it becomes
-- `slot < ir-stack-budget ir`, which is the emitter's own static invariant.
entry-s : LocState FS
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false

-- All four preconditions now hold BY CONSTRUCTION.
entry-ns : ∀ (slots : ℕ) → next-slot (entry-alloc slots) ≡ 0
entry-ns _ = refl

entry-bf : ∀ (slots : ℕ) → BeforeFrontier (entry-alloc slots) entry-loc
entry-bf _ = heap-before (s≤s z≤n)

entry-nh : halted entry-s ≡ false
entry-nh = refl

-- `main`'s machine-refinement witness at the entry state. The `Unit` input's
-- validity is `valid-unit-wf`, and its residence is `in-unit` (D074: a unit
-- input needs none — the tag filler in `Input1` is never read).
entry-witness : (ir : IR Unit Unit) → IRObsCorrectF ir
              → MachineRefinesObsF ir tt entry-s (entry-alloc (ir-stack-budget ir))
entry-witness ir ioc =
  ioc (entry-size ir) Stack tt entry-loc entry-s (entry-alloc (ir-stack-budget ir))
      (entry-ns (ir-stack-budget ir)) valid-unit-wf
      (entry-bf (ir-stack-budget ir)) entry-nh
            (in-unit refl)

------------------------------------------------------------------------
-- `flat-trace` — DEFINED (the adequate fuel is `traces-agree`'s ∃-witness).
------------------------------------------------------------------------

flat-trace-of : (∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
              → Maybe (IR Unit Unit) → Behavior
flat-trace-of ioc nothing   _ = []
flat-trace-of ioc (just ir) n =
  take n (flat-events (proj₁ (MachineRefinesObsF.traces-agree (entry-witness ir (ioc ir)) n))
                      (ir-to-trace ir) (mkFlat entry-s (entry-alloc (ir-stack-budget ir)) 0))

------------------------------------------------------------------------
-- The concrete↔abstract seam (Plan 0.54 rung B). At THIS module the machine
-- (`as : ArchSemantics`) is OPAQUE (injected), so `asm-trace-correct` cannot be
-- decomposed here — it would be an un-dischargeable internal postulate. Instead
-- it is a PARAMETER of `flat-from-obs`, supplied by the per-arch instance where
-- the concrete `X64.State`/`run-events` machine IS visible, so the arith slice
-- can consume `dispatch-arith-preserves` there (the rest = the explicit ISA /
-- printer / loader trust). Same move that un-postulated `ir-flat-correct`:
-- localise the obligation to where it can be discharged.
--
-- The `AsmTraceCorrect ft` type is the shape the per-arch instance must supply
-- (against the DEFINED `flat-trace-of ioc`).
------------------------------------------------------------------------

-- D100: the HONEST precondition on the toolchain. `as` refuses a file that
-- defines a label twice, so for such a program `asm-sem asm` is the trace of
-- nothing at all and this equation is FALSE — not merely unproved. Stating
-- `DistinctLabels` here (and NOT on `assemble-correct`, where the same class of
-- premise already went vacuous when `asm-sem` was defined) narrows every arch's
-- `loader-faithful` axiom to the programs the assembler actually accepts. The
-- apex supplies it, so `correct` gains no hypothesis — it gains an obligation.
AsmTraceCorrect : (Maybe (IR Unit Unit) → Behavior) → Set
AsmTraceCorrect ft =
  ∀ (m : P.Module) (asm : String) →
  C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
  DistinctLabels arch m →
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
  (ioc : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir)
  → AsmTraceCorrect (flat-trace-of ioc)
  → ArchCorrect arch as
flat-from-obs ioc atc = record
  { asm-sem           = asm-sem
  ; flat-trace        = flat-trace-of ioc
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = atc
  ; ir-flat-correct   = ir-flat-correct-of ioc
  }
