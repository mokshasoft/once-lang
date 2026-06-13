-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.ArchCorrectness — the per-arch backend-correctness
-- witnesses that `Once.Verified.Compile.WithCPU` is instantiated with.
--
-- The apex `correct` is GENERIC over the target `Arch`; each target must
-- SUPPLY an `ArchCorrect` record (asm-text + flat-machine meanings, the
-- assemble/printer obligations, and the SigOp-trace obligation). The total
-- dispatcher `arch-correctness` FORCES per-arch coverage: you cannot add an
-- `Arch` constructor without a matching witness here (the coverage checker
-- rejects a missing clause) — a blanket `∀ arch` postulate could not.
--
-- TRUST vs OBLIGATION is NOT baked into the `ArchCorrect` record (every
-- field is phrased `…-correct`); WHETHER a field is a proof or a postulate
-- is decided HERE, per arch. Today each witness is a whole-record postulate
-- (assemble/printer trusted + the IR-observable obligation deferred). When an
-- arch genuinely discharges a field — e.g. x86-64's `ir-flat-correct` via
-- `IRObsCorrectFlat` — refactor THAT arch's witness from a postulate into a
-- `record { … }` construction, so the still-trusted fields stay postulated
-- and the proved field becomes a real proof. Nothing assumes the trusted
-- fields can't be proved later (an in-Agda assembler / verified printer).
------------------------------------------------------------------------

module Once.Verified.ArchCorrectness where

open import Once.Verified.CPU using (Arch; x86-64; x86-32; riscv64; arch-semantics)
open import Once.Verified.Compile using (ArchCorrect)

postulate
  x86-64-correct  : ArchCorrect x86-64  (arch-semantics x86-64)
  x86-32-correct  : ArchCorrect x86-32  (arch-semantics x86-32)
  riscv64-correct : ArchCorrect riscv64 (arch-semantics riscv64)

-- Total over `Arch` ⇒ adding a target forces a new witness here.
arch-correctness : ∀ (arch : Arch) → ArchCorrect arch (arch-semantics arch)
arch-correctness x86-64  = x86-64-correct
arch-correctness x86-32  = x86-32-correct
arch-correctness riscv64 = riscv64-correct
