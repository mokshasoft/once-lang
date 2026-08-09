-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32 — x86-32's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- Mirror of `Once.Adequacy.ArchCorrectness.X86-64` (Plan 0.53 Phase 2):
-- `x86-32-correct` is discharged through `ir-obs-correct` — the total
-- IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`, GENERIC in
-- `FrameSemantics`), instantiated at x86-32's `FrameSemantics`. Since
-- `ir-obs-correct` routes `Cata → cata-correct`, `cata-correct` is
-- LOAD-BEARING for the apex `correct` on this target too.
--
-- x86-32-correct is now CONSTRUCTED via the shared `FlatFromObs` module
-- (Phase B L1): `asm-sem`/`flat-trace` DEFINED, `assemble-correct` = `refl`,
-- with named postulates `asm-trace-correct`/`ir-flat-correct` + the loader
-- `entry-s`/`entry-alloc`. The old monolithic `x86-32-flat-from-obs`
-- postulate is retired.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

module Once.Adequacy.ArchCorrectness.X86-32 (o : CanonicalName) (program-bound : ℕ) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Data.Bool using (false)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-32; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.X86-32.FrameInstantiation using (x86-32-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-trace)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
open import Once.Adequacy.LabelClash using (DistinctLabels)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

-- Plan 0.54 rung D / D087: `program-bound` is a RESOURCE BOUND and so is now a
-- module PARAMETER threaded from the apex, not a postulate here.
open IRObsCorrectFlatness {x86-32-frame-semantics} program-bound using (ir-obs-correct)

-- x86-32's witness, CONSTRUCTED via the shared FlatFromObs (Phase B L1).
-- Plan 0.54 rung B: the concrete↔abstract seam, now LOCALISED here (was an
-- internal FlatFromObs postulate). At this per-arch instance the concrete
-- machine IS visible, so the arith slice is dischargeable from
-- `dispatch-arith-preserves`; the non-arith remainder is the explicit ISA /
-- printer / loader trust (GNU `as` class). Stated against the DEFINED
-- `flat-trace` via `FFO.AsmTraceCorrect`.
------------------------------------------------------------------------
-- THE ENTRY FRAME (Plan 0.54 rung D). `FlatFromObs` no longer postulates this
-- — each arch owns its own loader frame, so the postulate lives where the arch
-- does. x86-64 CONSTRUCTS its frame (it is the loader's `%rsp`, which makes
-- `entry-frame-base` a theorem there); x86-32 has no correspondence yet
-- (`x86-32-conc-flat-sim` below is still whole-cloth), so nothing constrains
-- this frame and it stays opaque until that lands.
------------------------------------------------------------------------
postulate
  entry-frame-x86-32 : FrameSemantics.Frame x86-32-frame-semantics

module FFOc = FFO o x86-32 x86-32-frame-semantics entry-frame-x86-32 (arch-semantics x86-32) program-bound
asC = arch-semantics x86-32

-- The concrete machine's SigOp trace of a compiled IR (see X86-64 for rationale):
-- lower the IR to a concrete x86-32 `Program` (`compile-trace ∘ ir-to-trace`) and
-- run the concrete machine on it.
conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  ArchSemantics.run-trace asC (compile-trace (ir-to-trace ir))
                          (ArchSemantics.initialState asC)

postulate
  -- (A) TOOLCHAIN TRUST — assembler + loader + printer + decoder (GNU `as`
  -- class); NOT the CPU, NOT the arith logic.
  -- D100: preconditioned on distinct emitted local labels — see the x86-64
  -- instance for why the unconditioned form was FALSE rather than trusted.
  x86-32-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false x86-32 m ≡ C.Built asm →
    DistinctLabels x86-32 m →
    ∀ (n : ℕ) → FFOc.asm-sem asm n ≡ conc-trace (moduleToIR m) n
  -- (B) THE SIMULATION — PROVABLE: concrete `run-events` ≡ abstract
  -- `flat-events`. Arith slice = `dispatch-arith-preserves` (here also the
  -- borrow/restore `BorrowRestoreCore`, still to build). Named simulation target.
  x86-32-conc-flat-sim :
    ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
    conc-trace mir n ≡ FFOc.flat-trace-of ir-obs-correct mir n

asm-trace-correct-x86-32 : FFOc.AsmTraceCorrect (FFOc.flat-trace-of ir-obs-correct)
asm-trace-correct-x86-32 m asm eq dl n =
  trans (x86-32-loader-faithful m asm eq dl n)
        (x86-32-conc-flat-sim (moduleToIR m) n)

x86-32-correct : ArchCorrect x86-32 (arch-semantics x86-32)
x86-32-correct =
  FFO.flat-from-obs o x86-32 x86-32-frame-semantics entry-frame-x86-32 (arch-semantics x86-32)
    program-bound ir-obs-correct asm-trace-correct-x86-32
