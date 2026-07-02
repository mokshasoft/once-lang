-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatFromObs  (Plan 0.53-step2 / Phase B L1)
--
-- Shared, arch-parametric construction of the per-arch `ArchCorrect`
-- record, replacing the monolithic per-arch `<arch>-flat-from-obs`
-- postulate with a CONSTRUCTED record whose trust surface is EXPLICIT:
--
--   * `asm-sem`          — DEFINED  (`exec-bytes ∘ assemble`)
--   * `flat-trace`       — DEFINED  (`flat-events ∘ ir-to-trace` from the
--                                    loader entry frame, a parameter)
--   * `assemble-correct` — PROVED   (`refl`, by the `asm-sem` definition)
--   * `asm-trace-correct`— NAMED postulate (printer / loader faithfulness)
--   * `ir-flat-correct`  — NAMED postulate (→ Layer 2: from `ir-obs-correct`)
--
-- The loader entry frame (`entry-s`/`entry-alloc`) is a module parameter:
-- `AllocState` needs a concrete `Frame`, which no arbitrary `FrameSemantics`
-- supplies, so each arch passes its own (the `_start` entry state).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (LocState)
open import Once.CCC.Machine.Allocation using (AllocState)

module Once.Adequacy.ArchCorrectness.FlatFromObs
  (arch         : Arch)
  (FS           : FrameSemantics)
  (as           : ArchSemantics)
  (program-bound : ℕ)
  (entry-s      : LocState FS)
  (entry-alloc  : AllocState {FS})
  where

open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.List using (List; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.IR using (IR)
open import Once.Type using (Unit)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
open import Once.Denotation.Behavior using (Behavior)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Compile as C
import Once.Parser.Module.Core as P

open FlatMachine {FS} using (FlatState; mkFlat)
open FlatEventTrace {FS} using (flat-events)
open IRObsCorrectFlatness {FS} program-bound using (IRObsCorrectF)

------------------------------------------------------------------------
-- The two DEFINED fields
------------------------------------------------------------------------

asm-sem : String → Behavior
asm-sem asm = ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm)

flat-trace : Maybe (IR Unit Unit) → Behavior
flat-trace (just ir) n = flat-events n (ir-to-trace ir) (mkFlat entry-s entry-alloc 0)
flat-trace nothing   _ = []

------------------------------------------------------------------------
-- The two NAMED postulates (Layer-1 gaps; replace the monolithic one)
------------------------------------------------------------------------

postulate
  -- printer / loader faithfulness: the emitted asm executed by the CPU
  -- equals the flat trace of the compiled IR. Same trust class as GNU `as`.
  asm-trace-correct :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → asm-sem asm n ≡ flat-trace (moduleToIR m) n
  -- flat trace ≡ IR observable. Layer 2 PROVES this from `ir-obs-correct`.
  ir-flat-correct :
    ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) → flat-trace mir n ≡ ⟦ mir ⟧IR n

------------------------------------------------------------------------
-- The constructed ArchCorrect record
------------------------------------------------------------------------

-- `ir-obs-correct` is threaded (matching the old `<arch>-flat-from-obs`
-- signature) so Layer 2 can consume it without re-plumbing the call sites.
flat-from-obs :
  (∀ {A B} (ir : IR A B) → IRObsCorrectF ir) → ArchCorrect arch as
flat-from-obs _ = record
  { asm-sem          = asm-sem
  ; flat-trace       = flat-trace
  ; assemble-correct = λ _ _ _ _ _ → refl
  ; asm-trace-correct = asm-trace-correct
  ; ir-flat-correct  = ir-flat-correct
  }
