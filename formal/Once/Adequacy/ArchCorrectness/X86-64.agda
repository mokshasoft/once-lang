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

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.List using ([])
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86v3-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
import Once.Compile as C
import Once.Parser.Module.Core as P
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ

open IRObsCorrectFlatness {x86v3-frame-semantics} program-bound using (ir-obs-correct)

-- The FlatFromObs bundle at the x86-64 params (concrete machine now VISIBLE).
module FFOx = FFO x86-64 x86v3-frame-semantics (arch-semantics x86-64) program-bound
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

  -- (B) THE SIMULATION — PROVABLE (the real rung-B content). The concrete
  -- `run-events` machine over `X64.State` produces the SAME SigOp trace as the
  -- abstract `flat-events` machine over `LocState`, for the same compiled IR.
  -- This is NOT the CPU semantics: it is a correspondence between two of OUR
  -- OWN models. Its arith slice is discharged by `dispatch-arith-preserves`
  -- (arith blocks are Pure ⇒ emit nothing and preserve CCC state); the
  -- non-arith slice is the per-instruction stepper↔abstract correspondence.
  -- Postulated FOR NOW; this is the named target of the simulation proof.
  x86-64-conc-flat-sim :
    ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
    conc-trace mir n ≡ FFOx.flat-trace-of ir-obs-correct mir n

-- The seam, ASSEMBLED from (A) ∘ (B). No longer one opaque postulate: the
-- provable half is named and separated from the honest toolchain axiom.
asm-trace-correct-x86-64 : FFOx.AsmTraceCorrect (FFOx.flat-trace-of ir-obs-correct)
asm-trace-correct-x86-64 m asm eq n =
  trans (x86-64-loader-faithful m asm eq n)
        (x86-64-conc-flat-sim (moduleToIR m) n)

x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct =
  FFO.flat-from-obs x86-64 x86v3-frame-semantics (arch-semantics x86-64)
    program-bound ir-obs-correct asm-trace-correct-x86-64
