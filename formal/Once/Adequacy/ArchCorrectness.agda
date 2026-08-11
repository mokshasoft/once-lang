-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness — the per-arch backend-correctness
-- witnesses that `Once.Adequacy.Compile.WithCPU` is instantiated with.
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
-- is decided HERE, per arch. Since Plan 0.53 (2026-07-01) ALL THREE witnesses
-- are constructed from the FS-generic IR-observable theorem `ir-obs-correct`
-- (`Once.Adequacy.ArchCorrectness.{X86-64,X86-32,RiscV64}`) — no longer
-- whole-record postulates. Each arch carries a single named
-- `<arch>-flat-from-obs` residual (the entry-state + prefix FS plumbing) plus
-- `program-bound`; those are provable (no new mathematics) and nothing assumes
-- the trusted fields can't be proved later (an in-Agda assembler / verified
-- printer). `cata-correct` is load-bearing for the apex on every target.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB

module Once.Adequacy.ArchCorrectness
  (o : CanonicalName) (program-bound : ℕ)
  (x86-64-heap-room : RB.HeapRoom o) (x86-64-stack-room : RB.StackRoom o)
  (x86-64-call-room : RB.CallRoom o) where

open import Once.Adequacy.CPU using (Arch; x86-64; x86-32; riscv64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)

-- All three targets are DISCHARGED THROUGH the generic IR-observable theorem
-- (`ir-obs-correct` → `cata-correct`) — see `…ArchCorrectness.{X86-64,X86-32,RiscV64}`.
-- So `cata-correct` is load-bearing for the apex on every target; each carries
-- only its single named `<arch>-flat-from-obs` FS-plumbing residual (Plan 0.53).
open import Once.Adequacy.ArchCorrectness.X86-64 o  program-bound x86-64-heap-room x86-64-stack-room x86-64-call-room using (x86-64-correct)
open import Once.Adequacy.ArchCorrectness.X86-32 o  program-bound using (x86-32-correct)
open import Once.Adequacy.ArchCorrectness.RiscV64 o program-bound using (riscv64-correct)

-- Total over `Arch` ⇒ adding a target forces a new witness here.
arch-correctness : ∀ (arch : Arch) → ArchCorrect arch (arch-semantics arch)
arch-correctness x86-64  = x86-64-correct
arch-correctness x86-32  = x86-32-correct
arch-correctness riscv64 = riscv64-correct
