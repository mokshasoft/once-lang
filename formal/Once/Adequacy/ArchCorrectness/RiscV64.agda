-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64 — riscv64's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- Mirror of `Once.Adequacy.ArchCorrectness.X86-64` (Plan 0.53 Phase 3):
-- `riscv64-correct` is discharged through `ir-obs-correct` — the total
-- IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`, GENERIC in
-- `FrameSemantics`), instantiated at riscv64's `FrameSemantics`. Since
-- `ir-obs-correct` routes `Cata → cata-correct`, `cata-correct` is
-- LOAD-BEARING for the apex `correct` on this target too.
--
-- riscv64-correct is now CONSTRUCTED via the shared `FlatFromObs` module
-- (Phase B L1): `asm-sem`/`flat-trace` DEFINED, `assemble-correct` = `refl`,
-- with named postulates `asm-trace-correct`/`ir-flat-correct` + the loader
-- `entry-s`/`entry-alloc`. The old monolithic `riscv64-flat-from-obs`
-- postulate is retired.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

module Once.Adequacy.ArchCorrectness.RiscV64 (o : CanonicalName) (program-bound : ℕ) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Data.Bool using (false)
open import Data.Product using (proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (riscv64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace-cnt)
import Once.Compile as C
import Once.Parser.Module.Core as P
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

-- Plan 0.54 rung D / D087: `program-bound` is a RESOURCE BOUND and so is now a
-- module PARAMETER threaded from the apex, not a postulate here.
open IRObsCorrectFlatness {rv64-frame-semantics} program-bound using (ir-obs-correct)

------------------------------------------------------------------------
-- THE ENTRY FRAME (Plan 0.54 rung D). `FlatFromObs` no longer postulates this
-- — each arch owns its own loader frame, so the postulate lives where the arch
-- does. x86-64 CONSTRUCTS its frame (it is the loader's `%rsp`, which makes
-- `entry-frame-base` a theorem there); riscv64 has no correspondence yet
-- (`riscv64-conc-flat-sim` below is still whole-cloth), so nothing constrains
-- this frame and it stays opaque until that lands.
------------------------------------------------------------------------
postulate
  entry-frame-riscv64 : FrameSemantics.Frame rv64-frame-semantics

module FFOr = FFO o riscv64 rv64-frame-semantics entry-frame-riscv64 (arch-semantics riscv64) program-bound
asR = arch-semantics riscv64

-- The concrete machine's SigOp trace of a compiled IR (see X86-64 for the full
-- rationale): lower the IR to a concrete riscv64 `Program` (the compiler's real
-- path `compile-trace-cnt ∘ ir-to-trace`) and run the concrete machine on it.
conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  ArchSemantics.run-trace asR (proj₂ (compile-trace-cnt o 0 (ir-to-trace ir)))
                          (ArchSemantics.initialState asR)

postulate
  -- (A) TOOLCHAIN TRUST — assembler + loader + printer + decoder round-trip
  -- (GNU `as` class); NOT the CPU, NOT the arith logic.
  riscv64-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false riscv64 m ≡ C.Built asm →
    ∀ (n : ℕ) → FFOr.asm-sem asm n ≡ conc-trace (moduleToIR m) n
  -- (B) THE SIMULATION — PROVABLE: concrete `run-events` ≡ abstract
  -- `flat-events`, a correspondence between two of OUR models. Arith slice =
  -- `dispatch-arith-preserves`. The named target of the simulation proof.
  riscv64-conc-flat-sim :
    ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
    conc-trace mir n ≡ FFOr.flat-trace-of ir-obs-correct mir n

asm-trace-correct-riscv64 : FFOr.AsmTraceCorrect (FFOr.flat-trace-of ir-obs-correct)
asm-trace-correct-riscv64 m asm eq n =
  trans (riscv64-loader-faithful m asm eq n)
        (riscv64-conc-flat-sim (moduleToIR m) n)

riscv64-correct : ArchCorrect riscv64 (arch-semantics riscv64)
riscv64-correct =
  FFO.flat-from-obs o riscv64 rv64-frame-semantics entry-frame-riscv64 (arch-semantics riscv64)
    program-bound ir-obs-correct asm-trace-correct-riscv64
