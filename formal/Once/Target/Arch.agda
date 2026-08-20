-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.Arch — the single, shared target-architecture enum.
--
-- The architecture of the COMPILED BINARY (not the host the compiler runs
-- on). Owned by neither the codegen (`Once.Compile`) nor the verified CPU
-- interface (`Once.Adequacy.CPU.Interface`) — both import it, so there is
-- ONE `Arch` type across the pipeline and no relabelling map between a
-- "codegen Arch" and a "verified Arch".
------------------------------------------------------------------------

module Once.Target.Arch where

-- Supported architectures.
data Arch : Set where
  x86-64  : Arch
  x86-32  : Arch
  riscv64 : Arch

------------------------------------------------------------------------
-- The target's FLOAT FORMAT (plan 0.73, D113/D114).
--
-- A `Float`'s denotation is the TARGET'S representation, so a program's
-- machine-level meaning is target-relative at `Float` — `1.5` is `0x3FC00000`
-- at 32 bits and `0x3FF8000000000000` at 64. This is the function that carries
-- the arch into the meaning, and it lives here because "which format does this
-- target use" is a fact about the TARGET, owned by neither the codegen nor the
-- denotation.
--
-- It must AGREE with `FrameSemantics.float-format` of the arch's frame
-- semantics, and that agreement is not left to inspection: each arch's
-- correspondence carries `fmt-eq : float-format FS ≡ binaryNN`, discharged by
-- `refl`, so a disagreement is a type error rather than a wrong binary.
------------------------------------------------------------------------

open import Once.Float.Dyadic using (FloatFormat; binary32; binary64)

arch-float-format : Arch → FloatFormat
-- SSE2 is in x86-64's baseline ABI; a `double` is what a C `double` is.
arch-float-format x86-64  = binary64
-- x86-32 keeps a float in a 32-bit GPR, so a `binary64` immediate would not
-- fit a word: this target lays a `Float` out as single precision.
arch-float-format x86-32  = binary32
-- riscv64 with the `D` extension; a `double` fits a 64-bit register.
arch-float-format riscv64 = binary64
