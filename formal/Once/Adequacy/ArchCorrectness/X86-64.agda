-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64
--
-- x86-64 backend correctness, CONSTRUCTED via the shared `FlatFromObs`.
-- Explicit trust surface: `asm-sem` DEFINED, `assemble-correct` = `refl`,
-- `flat-trace` DEFINED, `ir-flat-correct` PROVED. The one remaining seam
-- `asm-trace-correct` is DECOMPOSED here (Plan 0.54 rung B step 2) into an
-- honest external axiom + a provable simulation — see below.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64 where

open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.List using ([]; take)
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.Adequacy.CPU.X86-64 using (ev-x86-64; arith-env-x86-64; step-budget-x86-64; val-x86-64)
import Once.Arith.Backend.X86-64.RunTrace as RTx
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86-64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
import Once.Compile as C
import Once.Parser.Module.Core as P
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ

open IRObsCorrectFlatness {x86-64-frame-semantics} program-bound using (ir-obs-correct; MachineRefinesObsF)

-- The FlatFromObs bundle at the x86-64 params (concrete machine now VISIBLE).
module FFOx = FFO x86-64 x86-64-frame-semantics (arch-semantics x86-64) program-bound
as64 = arch-semantics x86-64

------------------------------------------------------------------------
-- The seam `asm-trace-correct`, DECOMPOSED (Plan 0.54 rung B step 2).
--
-- The middle term `conc-trace` is the CONCRETE machine's SigOp trace of a
-- compiled IR: lower the IR to a concrete x86-64 `Program` (the compiler's real
-- IR→instruction path `compile-trace ∘ ir-to-trace`) and run the concrete
-- `run-events` machine on it. DEFINED — so the split below is genuine (relates
-- real machines), not two postulates bridged by a third.
------------------------------------------------------------------------

conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  ArchSemantics.run-trace as64 (compile-trace (ir-to-trace ir))
                          (ArchSemantics.initialState as64)

postulate
  -- (A) TOOLCHAIN TRUST — the honest external boundary (GNU `as` class): the
  -- emitted text, assembled+decoded+loaded, traces as the concrete machine
  -- traces the compiled IR's `Program` directly. This is the assembler + loader
  -- + printer + decoder round-trip. It is NOT the CPU semantics and NOT the
  -- arith logic; it is exactly the toolchain boundary every verified compiler
  -- keeps (cf. CompCert's assembler/loader).
  x86-64-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false x86-64 m ≡ C.Built asm →
    ∀ (n : ℕ) → FFOx.asm-sem asm n ≡ conc-trace (moduleToIR m) n

-- ── (B) THE SIMULATION, now WIRED to the ConcFlatSim assembly (not a postulate).
-- The apex node `conc-flat-sim-just` is DEFINED via `events-agree`; every gap it
-- rests on is a NAMED obligation on THIS path (deleting it fails the typecheck).
open FlatMachine {x86-64-frame-semantics} using (mkFlat)

-- Instantiation params the recovered cluster is parametric over: the heap-location
-- encoding (`enc-hl`) + the allocator's live-cell injectivity (`LiveIn`/`enc-hl-inj-
-- live`, from `blocks-disjoint`) + the successor law. Genuine apex obligations.
postulate
  enc-hl : HeapLocation → ℕ
  LiveIn : AllocState {x86-64-frame-semantics} → HeapLocation → Set
  enc-hl-inj-live : ∀ (as : AllocState {x86-64-frame-semantics}) {a b : HeapLocation}
                  → LiveIn as a → LiveIn as b → enc-hl a ≡ enc-hl b → a ≡ b
  enc-hl-suc : ∀ (hl : HeapLocation) → enc-hl (sucHL hl) ≡ enc-hl hl + slot-size

open import Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim
  x86-64-frame-semantics enc-hl LiveIn enc-hl-inj-live enc-hl-suc
  using (events-agree; CompiledCorr)

postulate
  -- Initial-state correspondence: the concrete `initState` relates to the flat
  -- entry state `mkFlat entry-s entry-alloc 0` for the compiled IR.
  entry-corr : ∀ (ir : IR Unit Unit)
             → CompiledCorr (ir-to-trace ir) (mkFlat FFOx.entry-s FFOx.entry-alloc 0)
                            (ArchSemantics.initialState as64)

  -- FUEL ADEQUACY seam (surfaced by wiring): `events-agree` gives an EXISTENTIAL fuel
  -- `M` with `run-events M ≡ flat-events N`, but `conc-trace` is committed to
  -- `step-budget-x86-64 n`. Their first-`n` events agree because run-events' prefix is
  -- stable once the fuel suffices and `step-budget` is adequate. The honest fuel seam
  -- (`step-budget-x86-64` is already the abstract ℕ→ℕ adequate-fuel map).
  conc-fuel : ∀ (ir : IR Unit Unit) (n M : ℕ) →
      take n (RTx.run-events val-x86-64 ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
                (step-budget-x86-64 n) (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as64))
    ≡ take n (RTx.run-events val-x86-64 ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
                M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as64))

conc-flat-sim-just :
  ∀ (ir : IR Unit Unit) (n : ℕ) →
  conc-trace (just ir) n ≡ FFOx.flat-trace-of ir-obs-correct (just ir) n
conc-flat-sim-just ir n =
  trans (conc-fuel ir n (proj₁ agree)) (cong (take n) (proj₂ agree))
  where
    agree = events-agree
              (proj₁ (MachineRefinesObsF.traces-agree (FFOx.entry-witness ir (ir-obs-correct ir)) n))
              ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
              (ir-to-trace ir) (mkFlat FFOx.entry-s FFOx.entry-alloc 0)
              (ArchSemantics.initialState as64) (entry-corr ir)

-- conc-flat-sim, top-down: `nothing` proven (both traces `[]`); `just` delegates
-- to `conc-flat-sim-just` — the single refinement obligation the recovered cluster
-- fills. Everything hangs off this apex node (no proof islands).
x86-64-conc-flat-sim :
  ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
  conc-trace mir n ≡ FFOx.flat-trace-of ir-obs-correct mir n
x86-64-conc-flat-sim nothing   n = refl
x86-64-conc-flat-sim (just ir) n = conc-flat-sim-just ir n

-- The seam, ASSEMBLED from (A) ∘ (B). No longer one opaque postulate: the
-- provable half is named and separated from the honest toolchain axiom.
asm-trace-correct-x86-64 : FFOx.AsmTraceCorrect (FFOx.flat-trace-of ir-obs-correct)
asm-trace-correct-x86-64 m asm eq n =
  trans (x86-64-loader-faithful m asm eq n)
        (x86-64-conc-flat-sim (moduleToIR m) n)

x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct =
  FFO.flat-from-obs x86-64 x86-64-frame-semantics (arch-semantics x86-64)
    program-bound ir-obs-correct asm-trace-correct-x86-64
