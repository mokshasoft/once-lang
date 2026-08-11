-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU — TRUSTED BASE: per-arch CPU semantics
--
-- TWO LAYERS:
--
--   1. The portable interface — `ArchSemantics` record (defined in
--      `Once.Adequacy.CPU.Interface` to avoid module cycles). Each
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

module Once.Adequacy.CPU where

open import Data.List using (List)

open import Once.Denotation.Behavior        using (Behavior)
open import Once.Adequacy.CPU.Interface   public  -- re-export
import Once.Adequacy.CPU.RiscV64 as RiscV64-CPU
import Once.Adequacy.CPU.X86-64  as X86-64-CPU
import Once.Adequacy.CPU.X86-32  as X86-32-CPU

------------------------------------------------------------------------
-- Per-arch instances. All three are now real (not wholesale postulates).
-- Each instance's `Program / State / initialState / run` is concrete
-- in its corresponding `Once.CCC.Target.<arch>.Semantics`. Only the
-- byte-decoder and Behavior-projection are postulated per arch
-- (pending Plan 0.4.2's connector + a concrete decoder).
------------------------------------------------------------------------

arch-semantics : Arch → ArchSemantics
arch-semantics x86-64  = X86-64-CPU.arch-semantics
arch-semantics x86-32  = X86-32-CPU.arch-semantics
arch-semantics riscv64 = RiscV64-CPU.arch-semantics

------------------------------------------------------------------------
-- Top-level bytes-execution: arch-generic via `ArchSemantics`.
------------------------------------------------------------------------

exec : Arch → List Byte → Behavior
exec arch bytes = ArchSemantics.exec-bytes (arch-semantics arch) bytes
