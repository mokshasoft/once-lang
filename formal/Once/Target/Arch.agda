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

open import Data.Nat using (ℕ)
open import Once.Float.Dyadic using (FloatFormat; binary32; binary64)

------------------------------------------------------------------------
-- THE TARGET'S NUMERIC FACTS, in one record (plan 0.74, D115).
--
-- `Float` needed the format (D113) and `Int` needs the width for exactly the
-- same reason: `⟦ Int ⟧` is the RESIDUE, so `-5` denotes `2^w - 5` and is
-- width-relative just as a float literal is format-relative. One record
-- rather than two parallel `Arch → _` maps, so a target's numeric facts
-- cannot drift apart.
------------------------------------------------------------------------

record TargetNum : Set where
  constructor mkTargetNum
  field
    -- | The machine word in BITS. `Int` is a signed two's-complement word of
    -- this width (D054), so it also fixes the literal range: an `Int` holds
    -- `-2^(int-bits-1) … 2^(int-bits-1)-1`, and a literal outside it is a
    -- TYPE ERROR (D115).
    int-bits     : ℕ
    float-format : FloatFormat

open TargetNum public

arch-numerics : Arch → TargetNum
arch-numerics x86-64  = mkTargetNum 64 binary64
arch-numerics x86-32  = mkTargetNum 32 binary32
arch-numerics riscv64 = mkTargetNum 64 binary64

-- | Derived, so existing callers are unchanged.
arch-int-bits : Arch → ℕ
arch-int-bits a = int-bits (arch-numerics a)

arch-float-format : Arch → FloatFormat
arch-float-format a = float-format (arch-numerics a)

-- | The target's name, for diagnostics. Here rather than in the compiler
-- because it is a fact about the target, and because an error that says which
-- target refused a literal is the whole point of refusing per target.
open import Data.String using (String)

archName : Arch → String
archName x86-64  = "x86-64"
archName x86-32  = "x86-32"
archName riscv64 = "riscv64"
