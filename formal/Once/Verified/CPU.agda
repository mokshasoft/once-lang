-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU — TRUSTED BASE: per-arch CPU semantics
--
-- TWO LAYERS:
--
--   1. The portable interface — `ArchSemantics` record (defined in
--      `Once.Verified.CPU.Interface` to avoid module cycles). Each
--      supported arch (RiscV64, X86-64, X86-32) provides one of
--      these by combining its concrete `Program / State / run` with
--      a byte-decoder and a state-to-behavior projection.
--      Downstream proofs work against this record so they're
--      arch-generic.
--
--   2. The bytes-level execution — `exec : Arch → List Byte → Behavior`.
--      Computed by dispatching on Arch, decoding bytes, running the
--      per-arch semantics, and projecting to Behavior.
--
-- The TRUST point per arch is the body of its `ArchSemantics` instance
-- — specifically the `run` function (the per-arch ISA semantics).
-- Reviewers compare clause-by-clause against the vendor manual.
-- No separate "matches-spec" axiom; same convention as CompCert's
-- `Asm.v`.
------------------------------------------------------------------------

module Once.Verified.CPU where

open import Data.List using (List)

open import Once.Verified.Behavior        using (Behavior)
open import Once.Verified.CPU.Interface   public  -- re-export
import Once.Verified.CPU.RiscV64 as RiscV64-CPU

------------------------------------------------------------------------
-- Per-arch instances.
--
--   - RiscV64: real instance via `Once.CCC.Target.RiscV64.Semantics`.
--   - X86-64 / X86-32: pre-DirectSim shape to be restored from
--     history (commit 90468b8f and predecessors). Postulated until
--     then.
------------------------------------------------------------------------

postulate
  arch-semantics-x86-64 : ArchSemantics
  arch-semantics-x86-32 : ArchSemantics

arch-semantics : Arch → ArchSemantics
arch-semantics x86-64  = arch-semantics-x86-64
arch-semantics x86-32  = arch-semantics-x86-32
arch-semantics riscv64 = RiscV64-CPU.arch-semantics

------------------------------------------------------------------------
-- Top-level bytes-execution: arch-generic via `ArchSemantics`.
------------------------------------------------------------------------

exec : Arch → List Byte → Behavior
exec arch bytes = ArchSemantics.exec-bytes (arch-semantics arch) bytes
