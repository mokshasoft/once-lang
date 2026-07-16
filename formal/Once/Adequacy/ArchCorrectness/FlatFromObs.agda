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
--   * `assemble-correct` — PROVED   (`refl`, by the `asm-sem` definition)
--   * `flat-trace`       — module PARAMETER (abstract). Its genuine
--                          definition is `take n (flat-events (EF ir n) …)`
--                          with a proven adequate-fuel `EF` — the fuel
--                          counts machine STEPS while `n` counts EVENTS, so
--                          the naive `flat-events n` is NOT correct. That
--                          definition + adequacy is Layer 2's job; leaving
--                          `flat-trace` abstract here keeps the postulates
--                          SOUND (they assert properties of an unspecified
--                          trace, satisfiable by the correct construction).
--   * `asm-trace-correct`— NAMED postulate (printer / loader faithfulness)
--   * `ir-flat-correct`  — NAMED postulate (→ Layer 2: from `ir-obs-correct`)
--
-- `ir-obs-correct` is still threaded so `cata-correct` stays load-bearing.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy `Unit` (IR is IRTy-indexed)
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.ArchCorrectness.FlatFromObs
  (arch          : Arch)
  (FS            : FrameSemantics)
  (as            : ArchSemantics)
  (program-bound : ℕ)
  (flat-trace    : Maybe (IR Unit Unit) → Behavior)
  where

open import Data.Bool using (false)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
import Once.Compile as C
import Once.Parser.Module.Core as P

open IRObsCorrectFlatness {FS} program-bound using (IRObsCorrectF)

------------------------------------------------------------------------
-- The DEFINED field (+ its proof)
------------------------------------------------------------------------

asm-sem : String → Behavior
asm-sem asm = ArchSemantics.exec-bytes as (ArchSemantics.assemble as asm)

------------------------------------------------------------------------
-- The NAMED postulates (Layer-1 gaps; replace the monolithic one)
------------------------------------------------------------------------

postulate
  -- printer / loader faithfulness: the emitted asm executed by the CPU
  -- equals the flat trace of the compiled IR. Same trust class as GNU `as`.
  asm-trace-correct :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false arch m ≡ C.Built asm →
    ∀ (n : ℕ) → asm-sem asm n ≡ flat-trace (moduleToIR m) n
  -- flat trace ≡ IR observable. Layer 2 PROVES this (once `flat-trace` is
  -- defined with an adequate fuel) from `ir-obs-correct`'s `traces-agree`.
  ir-flat-correct :
    ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) → flat-trace mir n ≡ ⟦ mir ⟧IR n

------------------------------------------------------------------------
-- The constructed ArchCorrect record
------------------------------------------------------------------------

flat-from-obs :
  (∀ {A B} (ir : IR A B) → IRObsCorrectF ir) → ArchCorrect arch as
flat-from-obs _ = record
  { asm-sem          = asm-sem
  ; flat-trace       = flat-trace
  ; assemble-correct = λ _ _ _ _ _ → refl
  ; asm-trace-correct = asm-trace-correct
  ; ir-flat-correct  = ir-flat-correct
  }
